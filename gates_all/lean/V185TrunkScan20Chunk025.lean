import V185TrunkScan20Chunk024

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_152833 : List Nat := [1, 2, 4, 1, 1, 5, 2, 2, 2]
def baseStart_152833 : Nat := 118140960795 + 152833 * 2 ^ 59
def prefixEnd_152833 : Nat := 4983230072969 + 3 ^ 40 * 152833 * 2
def baseEnd_152833 : Nat := 69757145661071799008569

theorem tailTrace_152833 : CollatzResearch.WordTrace tailWord_152833 prefixEnd_152833 69757145661071799008569 := by
  unfold tailWord_152833
  simp only [CollatzResearch.WordTrace]
  refine ⟨5574277455319617643439153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3716184970213078428959435 5574277455319617643439153)
  ·
    refine ⟨4180708091489713232579365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5574277455319617643439153 4180708091489713232579365)
    ·
      refine ⟨783882767154321231108631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4180708091489713232579365 783882767154321231108631)
      ·
        refine ⟨1175824150731481846662947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 783882767154321231108631 1175824150731481846662947)
        ·
          refine ⟨1763736226097222769994421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1175824150731481846662947 1763736226097222769994421)
          ·
            refine ⟨165350271196614634686977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1763736226097222769994421 165350271196614634686977)
            ·
              refine ⟨124012703397460976015233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165350271196614634686977 124012703397460976015233)
              ·
                refine ⟨93009527548095732011425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124012703397460976015233 93009527548095732011425)
                ·
                  refine ⟨69757145661071799008569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93009527548095732011425 69757145661071799008569)
                  ·
                    rfl

theorem cell20_152833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 2].length) (baseStart_152833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152833 prefixEnd_152833 := by exact prefixLift 152833
  have htrace : WordTrace (prefixWord ++ tailWord_152833) baseStart_152833 baseEnd_152833 := by
    simpa [prefixWord, tailWord_152833, baseEnd_152833] using wordTrace_append hprefix tailTrace_152833
  have hstable : (prefixWord ++ tailWord_152833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152833).length < 2 ^ (prefixWord ++ tailWord_152833).sum := by decide
  have hdescent : baseEnd_152833 < baseStart_152833 := by decide
  rcases family_descends (prefixWord ++ tailWord_152833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152837 : List Nat := [1, 3, 1, 1, 2, 1, 5, 4, 2]
def baseStart_152837 : Nat := 118140960795 + 152837 * 2 ^ 59
def prefixEnd_152837 : Nat := 4983230072969 + 3 ^ 40 * 152837 * 2
def baseEnd_152837 : Nat := 69758971370065562875219

theorem tailTrace_152837 : CollatzResearch.WordTrace tailWord_152837 prefixEnd_152837 69758971370065562875219 := by
  unfold tailWord_152837
  simp only [CollatzResearch.WordTrace]
  refine ⟨5574423347305126326584765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3716282231536750884389843 5574423347305126326584765)
  ·
    refine ⟨2090408755239422372469287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5574423347305126326584765 2090408755239422372469287)
    ·
      refine ⟨3135613132859133558703931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2090408755239422372469287 3135613132859133558703931)
      ·
        refine ⟨4703419699288700338055897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3135613132859133558703931 4703419699288700338055897)
        ·
          refine ⟨3527564774466525253541923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4703419699288700338055897 3527564774466525253541923)
          ·
            refine ⟨5291347161699787880312885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3527564774466525253541923 5291347161699787880312885)
            ·
              refine ⟨496063796409355113779333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5291347161699787880312885 496063796409355113779333)
              ·
                refine ⟨93011961826754083833625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 496063796409355113779333 93011961826754083833625)
                ·
                  refine ⟨69758971370065562875219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93011961826754083833625 69758971370065562875219)
                  ·
                    rfl

theorem cell20_152837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 2].length) (baseStart_152837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152837 prefixEnd_152837 := by exact prefixLift 152837
  have htrace : WordTrace (prefixWord ++ tailWord_152837) baseStart_152837 baseEnd_152837 := by
    simpa [prefixWord, tailWord_152837, baseEnd_152837] using wordTrace_append hprefix tailTrace_152837
  have hstable : (prefixWord ++ tailWord_152837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152837).length < 2 ^ (prefixWord ++ tailWord_152837).sum := by decide
  have hdescent : baseEnd_152837 < baseStart_152837 := by decide
  rcases family_descends (prefixWord ++ tailWord_152837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152844 : List Nat := [2, 2, 1, 2, 2, 5, 1, 5]
def baseStart_152844 : Nat := 118140960795 + 152844 * 2 ^ 59
def prefixEnd_152844 : Nat := 4983230072969 + 3 ^ 40 * 152844 * 2
def baseEnd_152844 : Nat := 23254055453601549880619

theorem tailTrace_152844 : CollatzResearch.WordTrace tailWord_152844 prefixEnd_152844 23254055453601549880619 := by
  unfold tailWord_152844
  simp only [CollatzResearch.WordTrace]
  refine ⟨2787339329139883261044793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3716452438853177681393057 2787339329139883261044793)
  ·
    refine ⟨2090504496854912445783595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2787339329139883261044793 2090504496854912445783595)
    ·
      refine ⟨3135756745282368668675393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2090504496854912445783595 3135756745282368668675393)
      ·
        refine ⟨2351817558961776501506545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3135756745282368668675393 2351817558961776501506545)
        ·
          refine ⟨1763863169221332376129909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2351817558961776501506545 1763863169221332376129909)
          ·
            refine ⟨165362172114499910262179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1763863169221332376129909 165362172114499910262179)
            ·
              refine ⟨248043258171749865393269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165362172114499910262179 248043258171749865393269)
              ·
                refine ⟨23254055453601549880619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 248043258171749865393269 23254055453601549880619)
                ·
                  rfl

theorem cell20_152844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 5].length) (baseStart_152844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152844 prefixEnd_152844 := by exact prefixLift 152844
  have htrace : WordTrace (prefixWord ++ tailWord_152844) baseStart_152844 baseEnd_152844 := by
    simpa [prefixWord, tailWord_152844, baseEnd_152844] using wordTrace_append hprefix tailTrace_152844
  have hstable : (prefixWord ++ tailWord_152844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152844).length < 2 ^ (prefixWord ++ tailWord_152844).sum := by decide
  have hdescent : baseEnd_152844 < baseStart_152844 := by decide
  rcases family_descends (prefixWord ++ tailWord_152844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152858 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 6]
def baseStart_152858 : Nat := 118140960795 + 152858 * 2 ^ 59
def prefixEnd_152858 : Nat := 4983230072969 + 3 ^ 40 * 152858 * 2
def baseEnd_152858 : Nat := 69768556342282823175133

theorem tailTrace_152858 : CollatzResearch.WordTrace tailWord_152858 prefixEnd_152858 69768556342282823175133 := by
  unfold tailWord_152858
  simp only [CollatzResearch.WordTrace]
  refine ⟨1393797320057261728274807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3716792853486031275399485 1393797320057261728274807)
  ·
    refine ⟨2090695980085892592412211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1393797320057261728274807 2090695980085892592412211)
    ·
      refine ⟨3136043970128838888618317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2090695980085892592412211 3136043970128838888618317)
      ·
        refine ⟨1176016488798314583231869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3136043970128838888618317 1176016488798314583231869)
        ·
          refine ⟨441006183299367968711951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1176016488798314583231869 441006183299367968711951)
          ·
            refine ⟨661509274949051953067927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441006183299367968711951 661509274949051953067927)
            ·
              refine ⟨992263912423577929601891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661509274949051953067927 992263912423577929601891)
              ·
                refine ⟨1488395868635366894402837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 992263912423577929601891 1488395868635366894402837)
                ·
                  refine ⟨69768556342282823175133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1488395868635366894402837 69768556342282823175133)
                  ·
                    rfl

theorem cell20_152858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_152858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152858 prefixEnd_152858 := by exact prefixLift 152858
  have htrace : WordTrace (prefixWord ++ tailWord_152858) baseStart_152858 baseEnd_152858 := by
    simpa [prefixWord, tailWord_152858, baseEnd_152858] using wordTrace_append hprefix tailTrace_152858
  have hstable : (prefixWord ++ tailWord_152858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152858).length < 2 ^ (prefixWord ++ tailWord_152858).sum := by decide
  have hdescent : baseEnd_152858 < baseStart_152858 := by decide
  rcases family_descends (prefixWord ++ tailWord_152858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152861 : List Nat := [1, 4, 2, 3, 1, 2, 3, 4]
def baseStart_152861 : Nat := 118140960795 + 152861 * 2 ^ 59
def prefixEnd_152861 : Nat := 4983230072969 + 3 ^ 40 * 152861 * 2
def baseEnd_152861 : Nat := 23256641874676048691707

theorem tailTrace_152861 : CollatzResearch.WordTrace tailWord_152861 prefixEnd_152861 23256641874676048691707 := by
  unfold tailWord_152861
  simp only [CollatzResearch.WordTrace]
  refine ⟨5575298699218178425458437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3716865799478785616972291 5575298699218178425458437)
  ·
    refine ⟨1045368506103408454773457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5575298699218178425458437 1045368506103408454773457)
    ·
      refine ⟨784026379577556341080093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1045368506103408454773457 784026379577556341080093)
      ·
        refine ⟨294009892341583627905035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 784026379577556341080093 294009892341583627905035)
        ·
          refine ⟨441014838512375441857553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294009892341583627905035 441014838512375441857553)
          ·
            refine ⟨330761128884281581393165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 441014838512375441857553 330761128884281581393165)
            ·
              refine ⟨124035423331605593022437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 330761128884281581393165 124035423331605593022437)
              ·
                refine ⟨23256641874676048691707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124035423331605593022437 23256641874676048691707)
                ·
                  rfl

theorem cell20_152861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 4].length) (baseStart_152861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152861 prefixEnd_152861 := by exact prefixLift 152861
  have htrace : WordTrace (prefixWord ++ tailWord_152861) baseStart_152861 baseEnd_152861 := by
    simpa [prefixWord, tailWord_152861, baseEnd_152861] using wordTrace_append hprefix tailTrace_152861
  have hstable : (prefixWord ++ tailWord_152861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152861).length < 2 ^ (prefixWord ++ tailWord_152861).sum := by decide
  have hdescent : baseEnd_152861 < baseStart_152861 := by decide
  rcases family_descends (prefixWord ++ tailWord_152861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152879 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 8]
def baseStart_152879 : Nat := 118140960795 + 152879 * 2 ^ 59
def prefixEnd_152879 : Nat := 4983230072969 + 3 ^ 40 * 152879 * 2
def baseEnd_152879 : Nat := 69778141314500083475047

theorem tailTrace_152879 : CollatzResearch.WordTrace tailWord_152879 prefixEnd_152879 69778141314500083475047 := by
  unfold tailWord_152879
  simp only [CollatzResearch.WordTrace]
  refine ⟨5575955213152967499613691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3717303475435311666409127 5575955213152967499613691)
  ·
    refine ⟨8363932819729451249420537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5575955213152967499613691 8363932819729451249420537)
    ·
      refine ⟨6272949614797088437065403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8363932819729451249420537 6272949614797088437065403)
      ·
        refine ⟨9409424422195632655598105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6272949614797088437065403 9409424422195632655598105)
        ·
          refine ⟨7057068316646724491698579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9409424422195632655598105 7057068316646724491698579)
          ·
            refine ⟨10585602474970086737547869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7057068316646724491698579 10585602474970086737547869)
            ·
              refine ⟨3969600928113782526580451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10585602474970086737547869 3969600928113782526580451)
              ·
                refine ⟨5954401392170673789870677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3969600928113782526580451 5954401392170673789870677)
                ·
                  refine ⟨69778141314500083475047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5954401392170673789870677 69778141314500083475047)
                  ·
                    rfl

theorem cell20_152879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_152879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152879 prefixEnd_152879 := by exact prefixLift 152879
  have htrace : WordTrace (prefixWord ++ tailWord_152879) baseStart_152879 baseEnd_152879 := by
    simpa [prefixWord, tailWord_152879, baseEnd_152879] using wordTrace_append hprefix tailTrace_152879
  have hstable : (prefixWord ++ tailWord_152879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152879).length < 2 ^ (prefixWord ++ tailWord_152879).sum := by decide
  have hdescent : baseEnd_152879 < baseStart_152879 := by decide
  rcases family_descends (prefixWord ++ tailWord_152879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152896 : List Nat := [2, 1, 1, 2, 2, 1, 6, 1, 4]
def baseStart_152896 : Nat := 118140960795 + 152896 * 2 ^ 59
def prefixEnd_152896 : Nat := 4983230072969 + 3 ^ 40 * 152896 * 2
def baseEnd_152896 : Nat := 69785900577723579908311

theorem tailTrace_152896 : CollatzResearch.WordTrace tailWord_152896 prefixEnd_152896 69785900577723579908311 := by
  unfold tailWord_152896
  simp only [CollatzResearch.WordTrace]
  refine ⟨2788287627045689701491271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3717716836060919601988361 2788287627045689701491271)
  ·
    refine ⟨4182431440568534552236907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2788287627045689701491271 4182431440568534552236907)
    ·
      refine ⟨6273647160852801828355361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4182431440568534552236907 6273647160852801828355361)
      ·
        refine ⟨4705235370639601371266521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6273647160852801828355361 4705235370639601371266521)
        ·
          refine ⟨3528926527979701028449891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4705235370639601371266521 3528926527979701028449891)
          ·
            refine ⟨5293389791969551542674837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3528926527979701028449891 5293389791969551542674837)
            ·
              refine ⟨248127646498572728562883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5293389791969551542674837 248127646498572728562883)
              ·
                refine ⟨372191469747859092844325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248127646498572728562883 372191469747859092844325)
                ·
                  refine ⟨69785900577723579908311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 372191469747859092844325 69785900577723579908311)
                  ·
                    rfl

theorem cell20_152896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_152896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152896 prefixEnd_152896 := by exact prefixLift 152896
  have htrace : WordTrace (prefixWord ++ tailWord_152896) baseStart_152896 baseEnd_152896 := by
    simpa [prefixWord, tailWord_152896, baseEnd_152896] using wordTrace_append hprefix tailTrace_152896
  have hstable : (prefixWord ++ tailWord_152896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152896).length < 2 ^ (prefixWord ++ tailWord_152896).sum := by decide
  have hdescent : baseEnd_152896 < baseStart_152896 := by decide
  rcases family_descends (prefixWord ++ tailWord_152896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152941 : List Nat := [1, 5, 1, 1, 1, 3, 8]
def baseStart_152941 : Nat := 118140960795 + 152941 * 2 ^ 59
def prefixEnd_152941 : Nat := 4983230072969 + 3 ^ 40 * 152941 * 2
def baseEnd_152941 : Nat := 7756271089322602600903

theorem tailTrace_152941 : CollatzResearch.WordTrace tailWord_152941 prefixEnd_152941 7756271089322602600903 := by
  unfold tailWord_152941
  simp only [CollatzResearch.WordTrace]
  refine ⟨5578216538928352088370677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3718811025952234725580451 5578216538928352088370677)
  ·
    refine ⟨522957800524533008284751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5578216538928352088370677 522957800524533008284751)
    ·
      refine ⟨784436700786799512427127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 522957800524533008284751 784436700786799512427127)
      ·
        refine ⟨1176655051180199268640691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 784436700786799512427127 1176655051180199268640691)
        ·
          refine ⟨1764982576770298902961037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1176655051180199268640691 1764982576770298902961037)
          ·
            refine ⟨661868466288862088610389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1764982576770298902961037 661868466288862088610389)
            ·
              refine ⟨7756271089322602600903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 661868466288862088610389 7756271089322602600903)
              ·
                rfl

theorem cell20_152941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 8].length) (baseStart_152941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_152941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_152941 prefixEnd_152941 := by exact prefixLift 152941
  have htrace : WordTrace (prefixWord ++ tailWord_152941) baseStart_152941 baseEnd_152941 := by
    simpa [prefixWord, tailWord_152941, baseEnd_152941] using wordTrace_append hprefix tailTrace_152941
  have hstable : (prefixWord ++ tailWord_152941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152941).length < 2 ^ (prefixWord ++ tailWord_152941).sum := by decide
  have hdescent : baseEnd_152941 < baseStart_152941 := by decide
  rcases family_descends (prefixWord ++ tailWord_152941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153026 : List Nat := [3, 5, 2, 1, 1, 1, 3, 4]
def baseStart_153026 : Nat := 118140960795 + 153026 * 2 ^ 59
def prefixEnd_153026 : Nat := 4983230072969 + 3 ^ 40 * 153026 * 2
def baseEnd_153026 : Nat := 23281745373340301858149

theorem tailTrace_153026 : CollatzResearch.WordTrace tailWord_153026 prefixEnd_153026 23281745373340301858149 := by
  unfold tailWord_153026
  simp only [CollatzResearch.WordTrace]
  refine ⟨1395329185905102901303733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3720877829080274403476621 1395329185905102901303733)
  ·
    refine ⟨130812111178603396997225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1395329185905102901303733 130812111178603396997225)
    ·
      refine ⟨98109083383952547747919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130812111178603396997225 98109083383952547747919)
      ·
        refine ⟨147163625075928821621879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98109083383952547747919 147163625075928821621879)
        ·
          refine ⟨220745437613893232432819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147163625075928821621879 220745437613893232432819)
          ·
            refine ⟨331118156420839848649229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220745437613893232432819 331118156420839848649229)
            ·
              refine ⟨124169308657814943243461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 331118156420839848649229 124169308657814943243461)
              ·
                refine ⟨23281745373340301858149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124169308657814943243461 23281745373340301858149)
                ·
                  rfl

theorem cell20_153026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_153026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153026 prefixEnd_153026 := by exact prefixLift 153026
  have htrace : WordTrace (prefixWord ++ tailWord_153026) baseStart_153026 baseEnd_153026 := by
    simpa [prefixWord, tailWord_153026, baseEnd_153026] using wordTrace_append hprefix tailTrace_153026
  have hstable : (prefixWord ++ tailWord_153026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153026).length < 2 ^ (prefixWord ++ tailWord_153026).sum := by decide
  have hdescent : baseEnd_153026 < baseStart_153026 := by decide
  rcases family_descends (prefixWord ++ tailWord_153026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153034 : List Nat := [3, 1, 2, 1, 2, 4, 3, 4]
def baseStart_153034 : Nat := 118140960795 + 153034 * 2 ^ 59
def prefixEnd_153034 : Nat := 4983230072969 + 3 ^ 40 * 153034 * 2
def baseEnd_153034 : Nat := 23282962512669477769249

theorem tailTrace_153034 : CollatzResearch.WordTrace tailWord_153034 prefixEnd_153034 23282962512669477769249 := by
  unfold tailWord_153034
  simp only [CollatzResearch.WordTrace]
  refine ⟨1395402131897857242876539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3721072351727619314337437 1395402131897857242876539)
  ·
    refine ⟨2093103197846785864314809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1395402131897857242876539 2093103197846785864314809)
    ·
      refine ⟨1569827398385089398236107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2093103197846785864314809 1569827398385089398236107)
      ·
        refine ⟨2354741097577634097354161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1569827398385089398236107 2354741097577634097354161)
        ·
          refine ⟨1766055823183225573015621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2354741097577634097354161 1766055823183225573015621)
          ·
            refine ⟨331135466846854794940429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1766055823183225573015621 331135466846854794940429)
            ·
              refine ⟨124175800067570548102661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 331135466846854794940429 124175800067570548102661)
              ·
                refine ⟨23282962512669477769249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124175800067570548102661 23282962512669477769249)
                ·
                  rfl

theorem cell20_153034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_153034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153034 prefixEnd_153034 := by exact prefixLift 153034
  have htrace : WordTrace (prefixWord ++ tailWord_153034) baseStart_153034 baseEnd_153034 := by
    simpa [prefixWord, tailWord_153034, baseEnd_153034] using wordTrace_append hprefix tailTrace_153034
  have hstable : (prefixWord ++ tailWord_153034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153034).length < 2 ^ (prefixWord ++ tailWord_153034).sum := by decide
  have hdescent : baseEnd_153034 < baseStart_153034 := by decide
  rcases family_descends (prefixWord ++ tailWord_153034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153089 : List Nat := [1, 2, 4, 1, 4, 2, 2, 4]
def baseStart_153089 : Nat := 118140960795 + 153089 * 2 ^ 59
def prefixEnd_153089 : Nat := 4983230072969 + 3 ^ 40 * 153089 * 2
def baseEnd_153089 : Nat := 23291330345557562158063

theorem tailTrace_153089 : CollatzResearch.WordTrace tailWord_153089 prefixEnd_153089 23291330345557562158063 := by
  unfold tailWord_153089
  simp only [CollatzResearch.WordTrace]
  refine ⟨5583614542392173364758321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3722409694928115576505547 5583614542392173364758321)
  ·
    refine ⟨4187710906794130023568741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5583614542392173364758321 4187710906794130023568741)
    ·
      refine ⟨785195795023899379419139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4187710906794130023568741 785195795023899379419139)
      ·
        refine ⟨1177793692535849069128709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 785195795023899379419139 1177793692535849069128709)
        ·
          refine ⟨220836317350471700461633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1177793692535849069128709 220836317350471700461633)
          ·
            refine ⟨165627238012853775346225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220836317350471700461633 165627238012853775346225)
            ·
              refine ⟨124220428509640331509669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165627238012853775346225 124220428509640331509669)
              ·
                refine ⟨23291330345557562158063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124220428509640331509669 23291330345557562158063)
                ·
                  rfl

theorem cell20_153089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 4].length) (baseStart_153089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153089 prefixEnd_153089 := by exact prefixLift 153089
  have htrace : WordTrace (prefixWord ++ tailWord_153089) baseStart_153089 baseEnd_153089 := by
    simpa [prefixWord, tailWord_153089, baseEnd_153089] using wordTrace_append hprefix tailTrace_153089
  have hstable : (prefixWord ++ tailWord_153089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153089).length < 2 ^ (prefixWord ++ tailWord_153089).sum := by decide
  have hdescent : baseEnd_153089 < baseStart_153089 := by decide
  rcases family_descends (prefixWord ++ tailWord_153089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153099 : List Nat := [1, 1, 1, 1, 9, 1, 1, 3, 2]
def baseStart_153099 : Nat := 118140960795 + 153099 * 2 ^ 59
def prefixEnd_153099 : Nat := 4983230072969 + 3 ^ 40 * 153099 * 2
def baseEnd_153099 : Nat := 69878555309157096140815

theorem tailTrace_153099 : CollatzResearch.WordTrace tailWord_153099 prefixEnd_153099 69878555309157096140815 := by
  unfold tailWord_153099
  simp only [CollatzResearch.WordTrace]
  refine ⟨5583979272355945072622351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3722652848237296715081567 5583979272355945072622351)
  ·
    refine ⟨8375968908533917608933527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5583979272355945072622351 8375968908533917608933527)
    ·
      refine ⟨12563953362800876413400291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8375968908533917608933527 12563953362800876413400291)
      ·
        refine ⟨18845930044201314620100437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12563953362800876413400291 18845930044201314620100437)
        ·
          refine ⟨110425371352742077852151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 18845930044201314620100437 110425371352742077852151)
          ·
            refine ⟨165638057029113116778227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110425371352742077852151 165638057029113116778227)
            ·
              refine ⟨248457085543669675167341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165638057029113116778227 248457085543669675167341)
              ·
                refine ⟨93171407078876128187753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 248457085543669675167341 93171407078876128187753)
                ·
                  refine ⟨69878555309157096140815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93171407078876128187753 69878555309157096140815)
                  ·
                    rfl

theorem cell20_153099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 2].length) (baseStart_153099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153099 prefixEnd_153099 := by exact prefixLift 153099
  have htrace : WordTrace (prefixWord ++ tailWord_153099) baseStart_153099 baseEnd_153099 := by
    simpa [prefixWord, tailWord_153099, baseEnd_153099] using wordTrace_append hprefix tailTrace_153099
  have hstable : (prefixWord ++ tailWord_153099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153099).length < 2 ^ (prefixWord ++ tailWord_153099).sum := by decide
  have hdescent : baseEnd_153099 < baseStart_153099 := by decide
  rcases family_descends (prefixWord ++ tailWord_153099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153117 : List Nat := [1, 4, 2, 2, 1, 1, 2, 4, 3]
def baseStart_153117 : Nat := 118140960795 + 153117 * 2 ^ 59
def prefixEnd_153117 : Nat := 4983230072969 + 3 ^ 40 * 153117 * 2
def baseEnd_153117 : Nat := 69886770999629033540741

theorem tailTrace_153117 : CollatzResearch.WordTrace tailWord_153117 prefixEnd_153117 69886770999629033540741 := by
  unfold tailWord_153117
  simp only [CollatzResearch.WordTrace]
  refine ⟨5584635786290734146777605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3723090524193822764518403 5584635786290734146777605)
  ·
    refine ⟨1047119209929512652520801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5584635786290734146777605 1047119209929512652520801)
    ·
      refine ⟨785339407447134489390601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1047119209929512652520801 785339407447134489390601)
      ·
        refine ⟨589004555585350867042951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 785339407447134489390601 589004555585350867042951)
        ·
          refine ⟨883506833378026300564427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589004555585350867042951 883506833378026300564427)
          ·
            refine ⟨1325260250067039450846641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 883506833378026300564427 1325260250067039450846641)
            ·
              refine ⟨993945187550279588134981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1325260250067039450846641 993945187550279588134981)
              ·
                refine ⟨186364722665677422775309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 993945187550279588134981 186364722665677422775309)
                ·
                  refine ⟨69886770999629033540741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 186364722665677422775309 69886770999629033540741)
                  ·
                    rfl

theorem cell20_153117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_153117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153117 prefixEnd_153117 := by exact prefixLift 153117
  have htrace : WordTrace (prefixWord ++ tailWord_153117) baseStart_153117 baseEnd_153117 := by
    simpa [prefixWord, tailWord_153117, baseEnd_153117] using wordTrace_append hprefix tailTrace_153117
  have hstable : (prefixWord ++ tailWord_153117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153117).length < 2 ^ (prefixWord ++ tailWord_153117).sum := by decide
  have hdescent : baseEnd_153117 < baseStart_153117 := by decide
  rcases family_descends (prefixWord ++ tailWord_153117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153134 : List Nat := [4, 1, 3, 1, 2, 2, 1, 3, 3]
def baseStart_153134 : Nat := 118140960795 + 153134 * 2 ^ 59
def prefixEnd_153134 : Nat := 4983230072969 + 3 ^ 40 * 153134 * 2
def baseEnd_153134 : Nat := 69894530262852529974005

theorem tailTrace_153134 : CollatzResearch.WordTrace tailWord_153134 prefixEnd_153134 69894530262852529974005 := by
  unfold tailWord_153134
  simp only [CollatzResearch.WordTrace]
  refine ⟨698156978403643256268307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3723503884819430700097637 698156978403643256268307)
  ·
    refine ⟨1047235467605464884402461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 698156978403643256268307 1047235467605464884402461)
    ·
      refine ⟨392713300352049331650923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1047235467605464884402461 392713300352049331650923)
      ·
        refine ⟨589069950528073997476385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392713300352049331650923 589069950528073997476385)
        ·
          refine ⟨441802462896055498107289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 589069950528073997476385 441802462896055498107289)
          ·
            refine ⟨331351847172041623580467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 441802462896055498107289 331351847172041623580467)
            ·
              refine ⟨497027770758062435370701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331351847172041623580467 497027770758062435370701)
              ·
                refine ⟨186385414034273413264013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 497027770758062435370701 186385414034273413264013)
                ·
                  refine ⟨69894530262852529974005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 186385414034273413264013 69894530262852529974005)
                  ·
                    rfl

theorem cell20_153134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_153134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153134 prefixEnd_153134 := by exact prefixLift 153134
  have htrace : WordTrace (prefixWord ++ tailWord_153134) baseStart_153134 baseEnd_153134 := by
    simpa [prefixWord, tailWord_153134, baseEnd_153134] using wordTrace_append hprefix tailTrace_153134
  have hstable : (prefixWord ++ tailWord_153134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153134).length < 2 ^ (prefixWord ++ tailWord_153134).sum := by decide
  have hdescent : baseEnd_153134 < baseStart_153134 := by decide
  rcases family_descends (prefixWord ++ tailWord_153134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153200 : List Nat := [2, 1, 1, 1, 6, 2, 1, 2, 4]
def baseStart_153200 : Nat := 118140960795 + 153200 * 2 ^ 59
def prefixEnd_153200 : Nat := 4983230072969 + 3 ^ 40 * 153200 * 2
def baseEnd_153200 : Nat := 69924654461249633773735

theorem tailTrace_153200 : CollatzResearch.WordTrace tailWord_153200 prefixEnd_153200 69924654461249633773735 := by
  unfold tailWord_153200
  simp only [CollatzResearch.WordTrace]
  refine ⟨2793831522495019661024527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3725108696660026214699369 2793831522495019661024527)
  ·
    refine ⟨4190747283742529491536791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2793831522495019661024527 4190747283742529491536791)
    ·
      refine ⟨6286120925613794237305187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4190747283742529491536791 6286120925613794237305187)
      ·
        refine ⟨9429181388420691355957781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6286120925613794237305187 9429181388420691355957781)
        ·
          refine ⟨441992877582219907310521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9429181388420691355957781 441992877582219907310521)
          ·
            refine ⟨331494658186664930482891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 441992877582219907310521 331494658186664930482891)
            ·
              refine ⟨497241987279997395724337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331494658186664930482891 497241987279997395724337)
              ·
                refine ⟨372931490459998046793253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 497241987279997395724337 372931490459998046793253)
                ·
                  refine ⟨69924654461249633773735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 372931490459998046793253 69924654461249633773735)
                  ·
                    rfl

theorem cell20_153200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_153200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153200 prefixEnd_153200 := by exact prefixLift 153200
  have htrace : WordTrace (prefixWord ++ tailWord_153200) baseStart_153200 baseEnd_153200 := by
    simpa [prefixWord, tailWord_153200, baseEnd_153200] using wordTrace_append hprefix tailTrace_153200
  have hstable : (prefixWord ++ tailWord_153200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153200).length < 2 ^ (prefixWord ++ tailWord_153200).sum := by decide
  have hdescent : baseEnd_153200 < baseStart_153200 := by decide
  rcases family_descends (prefixWord ++ tailWord_153200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153217 : List Nat := [1, 2, 4, 2, 1, 2, 1, 5, 2]
def baseStart_153217 : Nat := 118140960795 + 153217 * 2 ^ 59
def prefixEnd_153217 : Nat := 4983230072969 + 3 ^ 40 * 153217 * 2
def baseEnd_153217 : Nat := 69932413724473130206999

theorem tailTrace_153217 : CollatzResearch.WordTrace tailWord_153217 prefixEnd_153217 69932413724473130206999 := by
  unfold tailWord_153217
  simp only [CollatzResearch.WordTrace]
  refine ⟨5588283085928451225417905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3725522057285634150278603 5588283085928451225417905)
  ·
    refine ⟨4191212314446338419063429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5588283085928451225417905 4191212314446338419063429)
    ·
      refine ⟨785852308958688453574393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4191212314446338419063429 785852308958688453574393)
      ·
        refine ⟨589389231719016340180795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 785852308958688453574393 589389231719016340180795)
        ·
          refine ⟨884083847578524510271193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589389231719016340180795 884083847578524510271193)
          ·
            refine ⟨663062885683893382703395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 884083847578524510271193 663062885683893382703395)
            ·
              refine ⟨994594328525840074055093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 663062885683893382703395 994594328525840074055093)
              ·
                refine ⟨93243218299297506942665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 994594328525840074055093 93243218299297506942665)
                ·
                  refine ⟨69932413724473130206999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93243218299297506942665 69932413724473130206999)
                  ·
                    rfl

theorem cell20_153217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 2].length) (baseStart_153217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153217 prefixEnd_153217 := by exact prefixLift 153217
  have htrace : WordTrace (prefixWord ++ tailWord_153217) baseStart_153217 baseEnd_153217 := by
    simpa [prefixWord, tailWord_153217, baseEnd_153217] using wordTrace_append hprefix tailTrace_153217
  have hstable : (prefixWord ++ tailWord_153217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153217).length < 2 ^ (prefixWord ++ tailWord_153217).sum := by decide
  have hdescent : baseEnd_153217 < baseStart_153217 := by decide
  rcases family_descends (prefixWord ++ tailWord_153217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153221 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 6]
def baseStart_153221 : Nat := 118140960795 + 153221 * 2 ^ 59
def prefixEnd_153221 : Nat := 4983230072969 + 3 ^ 40 * 153221 * 2
def baseEnd_153221 : Nat := 69934239433466894073649

theorem tailTrace_153221 : CollatzResearch.WordTrace tailWord_153221 prefixEnd_153221 69934239433466894073649 := by
  unfold tailWord_153221
  simp only [CollatzResearch.WordTrace]
  refine ⟨5588428977913959908563517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3725619318609306605709011 5588428977913959908563517)
  ·
    refine ⟨2095660866717734965711319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5588428977913959908563517 2095660866717734965711319)
    ·
      refine ⟨3143491300076602448566979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2095660866717734965711319 3143491300076602448566979)
      ·
        refine ⟨4715236950114903672850469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3143491300076602448566979 4715236950114903672850469)
        ·
          refine ⟨884106928146544438659463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4715236950114903672850469 884106928146544438659463)
          ·
            refine ⟨1326160392219816657989195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 884106928146544438659463 1326160392219816657989195)
            ·
              refine ⟨1989240588329724986983793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1326160392219816657989195 1989240588329724986983793)
              ·
                refine ⟨1491930441247293740237845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1989240588329724986983793 1491930441247293740237845)
                ·
                  refine ⟨69934239433466894073649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1491930441247293740237845 69934239433466894073649)
                  ·
                    rfl

theorem cell20_153221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_153221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153221 prefixEnd_153221 := by exact prefixLift 153221
  have htrace : WordTrace (prefixWord ++ tailWord_153221) baseStart_153221 baseEnd_153221 := by
    simpa [prefixWord, tailWord_153221, baseEnd_153221] using wordTrace_append hprefix tailTrace_153221
  have hstable : (prefixWord ++ tailWord_153221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153221).length < 2 ^ (prefixWord ++ tailWord_153221).sum := by decide
  have hdescent : baseEnd_153221 < baseStart_153221 := by decide
  rcases family_descends (prefixWord ++ tailWord_153221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153224 : List Nat := [2, 1, 3, 5, 1, 1, 7]
def baseStart_153224 : Nat := 118140960795 + 153224 * 2 ^ 59
def prefixEnd_153224 : Nat := 4983230072969 + 3 ^ 40 * 153224 * 2
def baseEnd_153224 : Nat := 7770623190579135219293

theorem tailTrace_153224 : CollatzResearch.WordTrace tailWord_153224 prefixEnd_153224 7770623190579135219293 := by
  unfold tailWord_153224
  simp only [CollatzResearch.WordTrace]
  refine ⟨2794269198451545710461363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3725692264602060947281817 2794269198451545710461363)
  ·
    refine ⟨4191403797677318565692045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2794269198451545710461363 4191403797677318565692045)
    ·
      refine ⟨1571776424128994462134517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4191403797677318565692045 1571776424128994462134517)
      ·
        refine ⟨147354039762093230825111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1571776424128994462134517 147354039762093230825111)
        ·
          refine ⟨221031059643139846237667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147354039762093230825111 221031059643139846237667)
          ·
            refine ⟨331546589464709769356501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221031059643139846237667 331546589464709769356501)
            ·
              refine ⟨7770623190579135219293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 331546589464709769356501 7770623190579135219293)
              ·
                rfl

theorem cell20_153224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 7].length) (baseStart_153224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153224 prefixEnd_153224 := by exact prefixLift 153224
  have htrace : WordTrace (prefixWord ++ tailWord_153224) baseStart_153224 baseEnd_153224 := by
    simpa [prefixWord, tailWord_153224, baseEnd_153224] using wordTrace_append hprefix tailTrace_153224
  have hstable : (prefixWord ++ tailWord_153224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153224).length < 2 ^ (prefixWord ++ tailWord_153224).sum := by decide
  have hdescent : baseEnd_153224 < baseStart_153224 := by decide
  rcases family_descends (prefixWord ++ tailWord_153224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153228 : List Nat := [2, 2, 1, 2, 1, 1, 11]
def baseStart_153228 : Nat := 118140960795 + 153228 * 2 ^ 59
def prefixEnd_153228 : Nat := 4983230072969 + 3 ^ 40 * 153228 * 2
def baseEnd_153228 : Nat := 7770826047133997871143

theorem tailTrace_153228 : CollatzResearch.WordTrace tailWord_153228 prefixEnd_153228 7770826047133997871143 := by
  unfold tailWord_153228
  simp only [CollatzResearch.WordTrace]
  refine ⟨2794342144444300052034169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3725789525925733402712225 2794342144444300052034169)
  ·
    refine ⟨2095756608333225039025627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2794342144444300052034169 2095756608333225039025627)
    ·
      refine ⟨3143634912499837558538441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2095756608333225039025627 3143634912499837558538441)
      ·
        refine ⟨2357726184374878168903831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3143634912499837558538441 2357726184374878168903831)
        ·
          refine ⟨3536589276562317253355747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2357726184374878168903831 3536589276562317253355747)
          ·
            refine ⟨5304883914843475880033621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3536589276562317253355747 5304883914843475880033621)
            ·
              refine ⟨7770826047133997871143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5304883914843475880033621 7770826047133997871143)
              ·
                rfl

theorem cell20_153228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 11].length) (baseStart_153228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153228 prefixEnd_153228 := by exact prefixLift 153228
  have htrace : WordTrace (prefixWord ++ tailWord_153228) baseStart_153228 baseEnd_153228 := by
    simpa [prefixWord, tailWord_153228, baseEnd_153228] using wordTrace_append hprefix tailTrace_153228
  have hstable : (prefixWord ++ tailWord_153228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153228).length < 2 ^ (prefixWord ++ tailWord_153228).sum := by decide
  have hdescent : baseEnd_153228 < baseStart_153228 := by decide
  rcases family_descends (prefixWord ++ tailWord_153228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153248 : List Nat := [2, 1, 1, 4, 3, 2, 3, 1, 3]
def baseStart_153248 : Nat := 118140960795 + 153248 * 2 ^ 59
def prefixEnd_153248 : Nat := 4983230072969 + 3 ^ 40 * 153248 * 2
def baseEnd_153248 : Nat := 69946562969174800173539

theorem tailTrace_153248 : CollatzResearch.WordTrace tailWord_153248 prefixEnd_153248 69946562969174800173539 := by
  unfold tailWord_153248
  simp only [CollatzResearch.WordTrace]
  refine ⟨2794706874408071759898199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3726275832544095679864265 2794706874408071759898199)
  ·
    refine ⟨4192060311612107639847299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2794706874408071759898199 4192060311612107639847299)
    ·
      refine ⟨6288090467418161459770949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4192060311612107639847299 6288090467418161459770949)
      ·
        refine ⟨1179016962640905273707053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6288090467418161459770949 1179016962640905273707053)
        ·
          refine ⟨442131360990339477640145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1179016962640905273707053 442131360990339477640145)
          ·
            refine ⟨331598520742754608230109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 442131360990339477640145 331598520742754608230109)
            ·
              refine ⟨124349445278532978086291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 331598520742754608230109 124349445278532978086291)
              ·
                refine ⟨186524167917799467129437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124349445278532978086291 186524167917799467129437)
                ·
                  refine ⟨69946562969174800173539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 186524167917799467129437 69946562969174800173539)
                  ·
                    rfl

theorem cell20_153248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 3].length) (baseStart_153248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153248 prefixEnd_153248 := by exact prefixLift 153248
  have htrace : WordTrace (prefixWord ++ tailWord_153248) baseStart_153248 baseEnd_153248 := by
    simpa [prefixWord, tailWord_153248, baseEnd_153248] using wordTrace_append hprefix tailTrace_153248
  have hstable : (prefixWord ++ tailWord_153248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153248).length < 2 ^ (prefixWord ++ tailWord_153248).sum := by decide
  have hdescent : baseEnd_153248 < baseStart_153248 := by decide
  rcases family_descends (prefixWord ++ tailWord_153248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153300 : List Nat := [2, 4, 1, 3, 1, 2, 2, 5]
def baseStart_153300 : Nat := 118140960795 + 153300 * 2 ^ 59
def prefixEnd_153300 : Nat := 4983230072969 + 3 ^ 40 * 153300 * 2
def baseEnd_153300 : Nat := 23323432395364576813331

theorem tailTrace_153300 : CollatzResearch.WordTrace tailWord_153300 prefixEnd_153300 23323432395364576813331 := by
  unfold tailWord_153300
  simp only [CollatzResearch.WordTrace]
  refine ⟨2795655172313878200344677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3727540229751837600459569 2795655172313878200344677)
  ·
    refine ⟨524185344808852162564627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2795655172313878200344677 524185344808852162564627)
    ·
      refine ⟨786278017213278243846941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 524185344808852162564627 786278017213278243846941)
      ·
        refine ⟨294854256454979341442603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 786278017213278243846941 294854256454979341442603)
        ·
          refine ⟨442281384682469012163905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294854256454979341442603 442281384682469012163905)
          ·
            refine ⟨331711038511851759122929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 442281384682469012163905 331711038511851759122929)
            ·
              refine ⟨248783278883888819342197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 331711038511851759122929 248783278883888819342197)
              ·
                refine ⟨23323432395364576813331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 248783278883888819342197 23323432395364576813331)
                ·
                  rfl

theorem cell20_153300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_153300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153300 prefixEnd_153300 := by exact prefixLift 153300
  have htrace : WordTrace (prefixWord ++ tailWord_153300) baseStart_153300 baseEnd_153300 := by
    simpa [prefixWord, tailWord_153300, baseEnd_153300] using wordTrace_append hprefix tailTrace_153300
  have hstable : (prefixWord ++ tailWord_153300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153300).length < 2 ^ (prefixWord ++ tailWord_153300).sum := by decide
  have hdescent : baseEnd_153300 < baseStart_153300 := by decide
  rcases family_descends (prefixWord ++ tailWord_153300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153348 : List Nat := [2, 3, 2, 2, 1, 2, 4, 2, 2]
def baseStart_153348 : Nat := 118140960795 + 153348 * 2 ^ 59
def prefixEnd_153348 : Nat := 4983230072969 + 3 ^ 40 * 153348 * 2
def baseEnd_153348 : Nat := 69992205694018896839797

theorem tailTrace_153348 : CollatzResearch.WordTrace tailWord_153348 prefixEnd_153348 69992205694018896839797 := by
  unfold tailWord_153348
  simp only [CollatzResearch.WordTrace]
  refine ⟨2796530524226930299218349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3728707365635907065624465 2796530524226930299218349)
  ·
    refine ⟨1048698946585098862206881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2796530524226930299218349 1048698946585098862206881)
    ·
      refine ⟨786524209938824146655161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1048698946585098862206881 786524209938824146655161)
      ·
        refine ⟨589893157454118109991371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 786524209938824146655161 589893157454118109991371)
        ·
          refine ⟨884839736181177164987057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589893157454118109991371 884839736181177164987057)
          ·
            refine ⟨663629802135882873740293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 884839736181177164987057 663629802135882873740293)
            ·
              refine ⟨124430587900478038826305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 663629802135882873740293 124430587900478038826305)
              ·
                refine ⟨93322940925358529119729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124430587900478038826305 93322940925358529119729)
                ·
                  refine ⟨69992205694018896839797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93322940925358529119729 69992205694018896839797)
                  ·
                    rfl

theorem cell20_153348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_153348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153348 prefixEnd_153348 := by exact prefixLift 153348
  have htrace : WordTrace (prefixWord ++ tailWord_153348) baseStart_153348 baseEnd_153348 := by
    simpa [prefixWord, tailWord_153348, baseEnd_153348] using wordTrace_append hprefix tailTrace_153348
  have hstable : (prefixWord ++ tailWord_153348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153348).length < 2 ^ (prefixWord ++ tailWord_153348).sum := by decide
  have hdescent : baseEnd_153348 < baseStart_153348 := by decide
  rcases family_descends (prefixWord ++ tailWord_153348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153362 : List Nat := [3, 2, 4, 1, 1, 1, 2, 3, 3]
def baseStart_153362 : Nat := 118140960795 + 153362 * 2 ^ 59
def prefixEnd_153362 : Nat := 4983230072969 + 3 ^ 40 * 153362 * 2
def baseEnd_153362 : Nat := 69998595675497070373073

theorem tailTrace_153362 : CollatzResearch.WordTrace tailWord_153362 prefixEnd_153362 69998595675497070373073 := by
  unfold tailWord_153362
  simp only [CollatzResearch.WordTrace]
  refine ⟨1398392917600785247361585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3729047780268760659630893 1398392917600785247361585)
  ·
    refine ⟨1048794688200588935521189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1398392917600785247361585 1048794688200588935521189)
    ·
      refine ⟨196649004037610425410223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1048794688200588935521189 196649004037610425410223)
      ·
        refine ⟨294973506056415638115335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196649004037610425410223 294973506056415638115335)
        ·
          refine ⟨442460259084623457173003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294973506056415638115335 442460259084623457173003)
          ·
            refine ⟨663690388626935185759505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442460259084623457173003 663690388626935185759505)
            ·
              refine ⟨497767791470201389319629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 663690388626935185759505 497767791470201389319629)
              ·
                refine ⟨186662921801325520994861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 497767791470201389319629 186662921801325520994861)
                ·
                  refine ⟨69998595675497070373073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 186662921801325520994861 69998595675497070373073)
                  ·
                    rfl

theorem cell20_153362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_153362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153362 prefixEnd_153362 := by exact prefixLift 153362
  have htrace : WordTrace (prefixWord ++ tailWord_153362) baseStart_153362 baseEnd_153362 := by
    simpa [prefixWord, tailWord_153362, baseEnd_153362] using wordTrace_append hprefix tailTrace_153362
  have hstable : (prefixWord ++ tailWord_153362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153362).length < 2 ^ (prefixWord ++ tailWord_153362).sum := by decide
  have hdescent : baseEnd_153362 < baseStart_153362 := by decide
  rcases family_descends (prefixWord ++ tailWord_153362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153397 : List Nat := [1, 3, 3, 1, 4, 1, 7]
def baseStart_153397 : Nat := 118140960795 + 153397 * 2 ^ 59
def prefixEnd_153397 : Nat := 4983230072969 + 3 ^ 40 * 153397 * 2
def baseEnd_153397 : Nat := 7779396736576944911807

theorem tailTrace_153397 : CollatzResearch.WordTrace tailWord_153397 prefixEnd_153397 7779396736576944911807 := by
  unfold tailWord_153397
  simp only [CollatzResearch.WordTrace]
  refine ⟨5594848225276341966970445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3729898816850894644646963 5594848225276341966970445)
  ·
    refine ⟨2098068084478628237613917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5594848225276341966970445 2098068084478628237613917)
    ·
      refine ⟨786775531679485589105219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2098068084478628237613917 786775531679485589105219)
      ·
        refine ⟨1180163297519228383657829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 786775531679485589105219 1180163297519228383657829)
        ·
          refine ⟨221280618284855321935843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1180163297519228383657829 221280618284855321935843)
          ·
            refine ⟨331920927427282982903765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221280618284855321935843 331920927427282982903765)
            ·
              refine ⟨7779396736576944911807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 331920927427282982903765 7779396736576944911807)
              ·
                rfl

theorem cell20_153397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 7].length) (baseStart_153397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153397 prefixEnd_153397 := by exact prefixLift 153397
  have htrace : WordTrace (prefixWord ++ tailWord_153397) baseStart_153397 baseEnd_153397 := by
    simpa [prefixWord, tailWord_153397, baseEnd_153397] using wordTrace_append hprefix tailTrace_153397
  have hstable : (prefixWord ++ tailWord_153397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153397).length < 2 ^ (prefixWord ++ tailWord_153397).sum := by decide
  have hdescent : baseEnd_153397 < baseStart_153397 := by decide
  rcases family_descends (prefixWord ++ tailWord_153397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153411 : List Nat := [1, 1, 1, 3, 1, 5, 1, 3, 4]
def baseStart_153411 : Nat := 118140960795 + 153411 * 2 ^ 59
def prefixEnd_153411 : Nat := 4983230072969 + 3 ^ 40 * 153411 * 2
def baseEnd_153411 : Nat := 70020960610670677739539

theorem tailTrace_153411 : CollatzResearch.WordTrace tailWord_153411 prefixEnd_153411 70020960610670677739539 := by
  unfold tailWord_153411
  simp only [CollatzResearch.WordTrace]
  refine ⟨5595358847225622357980087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3730239231483748238653391 5595358847225622357980087)
  ·
    refine ⟨8393038270838433536970131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5595358847225622357980087 8393038270838433536970131)
    ·
      refine ⟨12589557406257650305455197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8393038270838433536970131 12589557406257650305455197)
      ·
        refine ⟨4721084027346618864545699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12589557406257650305455197 4721084027346618864545699)
        ·
          refine ⟨7081626041019928296818549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4721084027346618864545699 7081626041019928296818549)
          ·
            refine ⟨663902441345618277826739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7081626041019928296818549 663902441345618277826739)
            ·
              refine ⟨995853662018427416740109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 663902441345618277826739 995853662018427416740109)
              ·
                refine ⟨373445123256910281277541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 995853662018427416740109 373445123256910281277541)
                ·
                  refine ⟨70020960610670677739539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 373445123256910281277541 70020960610670677739539)
                  ·
                    rfl

theorem cell20_153411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 4].length) (baseStart_153411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153411 prefixEnd_153411 := by exact prefixLift 153411
  have htrace : WordTrace (prefixWord ++ tailWord_153411) baseStart_153411 baseEnd_153411 := by
    simpa [prefixWord, tailWord_153411, baseEnd_153411] using wordTrace_append hprefix tailTrace_153411
  have hstable : (prefixWord ++ tailWord_153411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153411).length < 2 ^ (prefixWord ++ tailWord_153411).sum := by decide
  have hdescent : baseEnd_153411 < baseStart_153411 := by decide
  rcases family_descends (prefixWord ++ tailWord_153411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153418 : List Nat := [3, 1, 2, 1, 1, 1, 4, 7]
def baseStart_153418 : Nat := 118140960795 + 153418 * 2 ^ 59
def prefixEnd_153418 : Nat := 4983230072969 + 3 ^ 40 * 153418 * 2
def baseEnd_153418 : Nat := 23341385200469921502059

theorem tailTrace_153418 : CollatzResearch.WordTrace tailWord_153418 prefixEnd_153418 23341385200469921502059 := by
  unfold tailWord_153418
  simp only [CollatzResearch.WordTrace]
  refine ⟨1398903539550065638371227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3730409438800175035656605 1398903539550065638371227)
  ·
    refine ⟨2098355309325098457556841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1398903539550065638371227 2098355309325098457556841)
    ·
      refine ⟨1573766481993823843167631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2098355309325098457556841 1573766481993823843167631)
      ·
        refine ⟨2360649722990735764751447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1573766481993823843167631 2360649722990735764751447)
        ·
          refine ⟨3540974584486103647127171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2360649722990735764751447 3540974584486103647127171)
          ·
            refine ⟨5311461876729155470690757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3540974584486103647127171 5311461876729155470690757)
            ·
              refine ⟨995899101886716650754517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5311461876729155470690757 995899101886716650754517)
              ·
                refine ⟨23341385200469921502059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 995899101886716650754517 23341385200469921502059)
                ·
                  rfl

theorem cell20_153418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_153418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153418 prefixEnd_153418 := by exact prefixLift 153418
  have htrace : WordTrace (prefixWord ++ tailWord_153418) baseStart_153418 baseEnd_153418 := by
    simpa [prefixWord, tailWord_153418, baseEnd_153418] using wordTrace_append hprefix tailTrace_153418
  have hstable : (prefixWord ++ tailWord_153418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153418).length < 2 ^ (prefixWord ++ tailWord_153418).sum := by decide
  have hdescent : baseEnd_153418 < baseStart_153418 := by decide
  rcases family_descends (prefixWord ++ tailWord_153418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153428 : List Nat := [2, 4, 1, 1, 3, 1, 2, 2, 4]
def baseStart_153428 : Nat := 118140960795 + 153428 * 2 ^ 59
def prefixEnd_153428 : Nat := 4983230072969 + 3 ^ 40 * 153428 * 2
def baseEnd_153428 : Nat := 70028719873894174172803

theorem tailTrace_153428 : CollatzResearch.WordTrace tailWord_153428 prefixEnd_153428 70028719873894174172803 := by
  unfold tailWord_153428
  simp only [CollatzResearch.WordTrace]
  refine ⟨2797989444082017130674469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3730652592109356174232625 2797989444082017130674469)
  ·
    refine ⟨524623020765378212001463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2797989444082017130674469 524623020765378212001463)
    ·
      refine ⟨786934531148067318002195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 524623020765378212001463 786934531148067318002195)
      ·
        refine ⟨1180401796722100977003293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 786934531148067318002195 1180401796722100977003293)
        ·
          refine ⟨442650673770787866376235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1180401796722100977003293 442650673770787866376235)
          ·
            refine ⟨663976010656181799564353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442650673770787866376235 663976010656181799564353)
            ·
              refine ⟨497982007992136349673265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 663976010656181799564353 497982007992136349673265)
              ·
                refine ⟨373486505994102262254949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 497982007992136349673265 373486505994102262254949)
                ·
                  refine ⟨70028719873894174172803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 373486505994102262254949 70028719873894174172803)
                  ·
                    rfl

theorem cell20_153428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_153428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153428 prefixEnd_153428 := by exact prefixLift 153428
  have htrace : WordTrace (prefixWord ++ tailWord_153428) baseStart_153428 baseEnd_153428 := by
    simpa [prefixWord, tailWord_153428, baseEnd_153428] using wordTrace_append hprefix tailTrace_153428
  have hstable : (prefixWord ++ tailWord_153428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153428).length < 2 ^ (prefixWord ++ tailWord_153428).sum := by decide
  have hdescent : baseEnd_153428 < baseStart_153428 := by decide
  rcases family_descends (prefixWord ++ tailWord_153428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153431 : List Nat := [1, 1, 3, 2, 6, 1, 2, 4]
def baseStart_153431 : Nat := 118140960795 + 153431 * 2 ^ 59
def prefixEnd_153431 : Nat := 4983230072969 + 3 ^ 40 * 153431 * 2
def baseEnd_153431 : Nat := 23343363051879832357597

theorem tailTrace_153431 : CollatzResearch.WordTrace tailWord_153431 prefixEnd_153431 23343363051879832357597 := by
  unfold tailWord_153431
  simp only [CollatzResearch.WordTrace]
  refine ⟨5596088307153165773708147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3730725538102110515805431 5596088307153165773708147)
  ·
    refine ⟨8394132460729748660562221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5596088307153165773708147 8394132460729748660562221)
    ·
      refine ⟨3147799672773655747710833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8394132460729748660562221 3147799672773655747710833)
      ·
        refine ⟨2360849754580241810783125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3147799672773655747710833 2360849754580241810783125)
        ·
          refine ⟨110664832245948834880459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2360849754580241810783125 110664832245948834880459)
          ·
            refine ⟨165997248368923252320689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110664832245948834880459 165997248368923252320689)
            ·
              refine ⟨124497936276692439240517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165997248368923252320689 124497936276692439240517)
              ·
                refine ⟨23343363051879832357597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124497936276692439240517 23343363051879832357597)
                ·
                  rfl

theorem cell20_153431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 4].length) (baseStart_153431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153431 prefixEnd_153431 := by exact prefixLift 153431
  have htrace : WordTrace (prefixWord ++ tailWord_153431) baseStart_153431 baseEnd_153431 := by
    simpa [prefixWord, tailWord_153431, baseEnd_153431] using wordTrace_append hprefix tailTrace_153431
  have hstable : (prefixWord ++ tailWord_153431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153431).length < 2 ^ (prefixWord ++ tailWord_153431).sum := by decide
  have hdescent : baseEnd_153431 < baseStart_153431 := by decide
  rcases family_descends (prefixWord ++ tailWord_153431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153462 : List Nat := [5, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_153462 : Nat := 118140960795 + 153462 * 2 ^ 59
def prefixEnd_153462 : Nat := 4983230072969 + 3 ^ 40 * 153462 * 2
def baseEnd_153462 : Nat := 70044238400341167039331

theorem tailTrace_153462 : CollatzResearch.WordTrace tailWord_153462 prefixEnd_153462 70044238400341167039331 := by
  unfold tailWord_153462
  simp only [CollatzResearch.WordTrace]
  refine ⟨349826185627553629255415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3731479313360572045391093 349826185627553629255415)
  ·
    refine ⟨524739278441330443883123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 349826185627553629255415 524739278441330443883123)
    ·
      refine ⟨787108917661995665824685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 524739278441330443883123 787108917661995665824685)
      ·
        refine ⟨295165844123248374684257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 787108917661995665824685 295165844123248374684257)
        ·
          refine ⟨221374383092436281013193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295165844123248374684257 221374383092436281013193)
          ·
            refine ⟨166030787319327210759895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221374383092436281013193 166030787319327210759895)
            ·
              refine ⟨249046180978990816139843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166030787319327210759895 249046180978990816139843)
              ·
                refine ⟨373569271468486224209765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249046180978990816139843 373569271468486224209765)
                ·
                  refine ⟨70044238400341167039331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 373569271468486224209765 70044238400341167039331)
                  ·
                    rfl

theorem cell20_153462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_153462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153462 prefixEnd_153462 := by exact prefixLift 153462
  have htrace : WordTrace (prefixWord ++ tailWord_153462) baseStart_153462 baseEnd_153462 := by
    simpa [prefixWord, tailWord_153462, baseEnd_153462] using wordTrace_append hprefix tailTrace_153462
  have hstable : (prefixWord ++ tailWord_153462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153462).length < 2 ^ (prefixWord ++ tailWord_153462).sum := by decide
  have hdescent : baseEnd_153462 < baseStart_153462 := by decide
  rcases family_descends (prefixWord ++ tailWord_153462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153466 : List Nat := [3, 1, 1, 1, 1, 1, 4, 6, 2]
def baseStart_153466 : Nat := 118140960795 + 153466 * 2 ^ 59
def prefixEnd_153466 : Nat := 4983230072969 + 3 ^ 40 * 153466 * 2
def baseEnd_153466 : Nat := 70046064109334930905981

theorem tailTrace_153466 : CollatzResearch.WordTrace tailWord_153466 prefixEnd_153466 70046064109334930905981 := by
  unfold tailWord_153466
  simp only [CollatzResearch.WordTrace]
  refine ⟨1399341215506591687808063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3731576574684244500821501 1399341215506591687808063)
  ·
    refine ⟨2099011823259887531712095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1399341215506591687808063 2099011823259887531712095)
    ·
      refine ⟨3148517734889831297568143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2099011823259887531712095 3148517734889831297568143)
      ·
        refine ⟨4722776602334746946352215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3148517734889831297568143 4722776602334746946352215)
        ·
          refine ⟨7084164903502120419528323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4722776602334746946352215 7084164903502120419528323)
          ·
            refine ⟨10626247355253180629292485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7084164903502120419528323 10626247355253180629292485)
            ·
              refine ⟨1992421379109971367992341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10626247355253180629292485 1992421379109971367992341)
              ·
                refine ⟨93394752145779907874641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1992421379109971367992341 93394752145779907874641)
                ·
                  refine ⟨70046064109334930905981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93394752145779907874641 70046064109334930905981)
                  ·
                    rfl

theorem cell20_153466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 2].length) (baseStart_153466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153466 prefixEnd_153466 := by exact prefixLift 153466
  have htrace : WordTrace (prefixWord ++ tailWord_153466) baseStart_153466 baseEnd_153466 := by
    simpa [prefixWord, tailWord_153466, baseEnd_153466] using wordTrace_append hprefix tailTrace_153466
  have hstable : (prefixWord ++ tailWord_153466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153466).length < 2 ^ (prefixWord ++ tailWord_153466).sum := by decide
  have hdescent : baseEnd_153466 < baseStart_153466 := by decide
  rcases family_descends (prefixWord ++ tailWord_153466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153504 : List Nat := [2, 1, 1, 4, 1, 1, 1, 7, 2]
def baseStart_153504 : Nat := 118140960795 + 153504 * 2 ^ 59
def prefixEnd_153504 : Nat := 4983230072969 + 3 ^ 40 * 153504 * 2
def baseEnd_153504 : Nat := 70063408344775687639159

theorem tailTrace_153504 : CollatzResearch.WordTrace tailWord_153504 prefixEnd_153504 70063408344775687639159 := by
  unfold tailWord_153504
  simp only [CollatzResearch.WordTrace]
  refine ⟨2799375417944349620557783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3732500557259132827410377 2799375417944349620557783)
  ·
    refine ⟨4199063126916524430836675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2799375417944349620557783 4199063126916524430836675)
    ·
      refine ⟨6298594690374786646255013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4199063126916524430836675 6298594690374786646255013)
      ·
        refine ⟨1180986504445272496172815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6298594690374786646255013 1180986504445272496172815)
        ·
          refine ⟨1771479756667908744259223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1180986504445272496172815 1771479756667908744259223)
          ·
            refine ⟨2657219635001863116388835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1771479756667908744259223 2657219635001863116388835)
            ·
              refine ⟨3985829452502794674583253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2657219635001863116388835 3985829452502794674583253)
              ·
                refine ⟨93417877793034250185545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3985829452502794674583253 93417877793034250185545)
                ·
                  refine ⟨70063408344775687639159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93417877793034250185545 70063408344775687639159)
                  ·
                    rfl

theorem cell20_153504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 2].length) (baseStart_153504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153504 prefixEnd_153504 := by exact prefixLift 153504
  have htrace : WordTrace (prefixWord ++ tailWord_153504) baseStart_153504 baseEnd_153504 := by
    simpa [prefixWord, tailWord_153504, baseEnd_153504] using wordTrace_append hprefix tailTrace_153504
  have hstable : (prefixWord ++ tailWord_153504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153504).length < 2 ^ (prefixWord ++ tailWord_153504).sum := by decide
  have hdescent : baseEnd_153504 < baseStart_153504 := by decide
  rcases family_descends (prefixWord ++ tailWord_153504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153521 : List Nat := [1, 2, 2, 4, 2, 2, 1, 4, 2]
def baseStart_153521 : Nat := 118140960795 + 153521 * 2 ^ 59
def prefixEnd_153521 : Nat := 4983230072969 + 3 ^ 40 * 153521 * 2
def baseEnd_153521 : Nat := 70071167607999184072423

theorem tailTrace_153521 : CollatzResearch.WordTrace tailWord_153521 prefixEnd_153521 70071167607999184072423 := by
  unfold tailWord_153521
  simp only [CollatzResearch.WordTrace]
  refine ⟨5599370876827111144484417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3732913917884740762989611 5599370876827111144484417)
  ·
    refine ⟨4199528157620333358363313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5599370876827111144484417 4199528157620333358363313)
    ·
      refine ⟨3149646118215250018772485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4199528157620333358363313 3149646118215250018772485)
      ·
        refine ⟨590558647165359378519841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3149646118215250018772485 590558647165359378519841)
        ·
          refine ⟨442918985374019533889881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 590558647165359378519841 442918985374019533889881)
          ·
            refine ⟨332189239030514650417411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 442918985374019533889881 332189239030514650417411)
            ·
              refine ⟨498283858545771975626117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332189239030514650417411 498283858545771975626117)
              ·
                refine ⟨93428223477332245429897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 498283858545771975626117 93428223477332245429897)
                ·
                  refine ⟨70071167607999184072423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93428223477332245429897 70071167607999184072423)
                  ·
                    rfl

theorem cell20_153521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 2].length) (baseStart_153521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153521 prefixEnd_153521 := by exact prefixLift 153521
  have htrace : WordTrace (prefixWord ++ tailWord_153521) baseStart_153521 baseEnd_153521 := by
    simpa [prefixWord, tailWord_153521, baseEnd_153521] using wordTrace_append hprefix tailTrace_153521
  have hstable : (prefixWord ++ tailWord_153521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153521).length < 2 ^ (prefixWord ++ tailWord_153521).sum := by decide
  have hdescent : baseEnd_153521 < baseStart_153521 := by decide
  rcases family_descends (prefixWord ++ tailWord_153521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153524 : List Nat := [2, 5, 2, 1, 3, 1, 1, 5]
def baseStart_153524 : Nat := 118140960795 + 153524 * 2 ^ 59
def prefixEnd_153524 : Nat := 4983230072969 + 3 ^ 40 * 153524 * 2
def baseEnd_153524 : Nat := 23357512296581502324137

theorem tailTrace_153524 : CollatzResearch.WordTrace tailWord_153524 prefixEnd_153524 23357512296581502324137 := by
  unfold tailWord_153524
  simp only [CollatzResearch.WordTrace]
  refine ⟨2799740147908121328421813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3732986863877495104562417 2799740147908121328421813)
  ·
    refine ⟨262475638866386374539545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2799740147908121328421813 262475638866386374539545)
    ·
      refine ⟨196856729149789780904659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262475638866386374539545 196856729149789780904659)
      ·
        refine ⟨295285093724684671356989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196856729149789780904659 295285093724684671356989)
        ·
          refine ⟨110731910146756751758871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 295285093724684671356989 110731910146756751758871)
          ·
            refine ⟨166097865220135127638307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110731910146756751758871 166097865220135127638307)
            ·
              refine ⟨249146797830202691457461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166097865220135127638307 249146797830202691457461)
              ·
                refine ⟨23357512296581502324137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 249146797830202691457461 23357512296581502324137)
                ·
                  rfl

theorem cell20_153524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 5].length) (baseStart_153524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153524 prefixEnd_153524 := by exact prefixLift 153524
  have htrace : WordTrace (prefixWord ++ tailWord_153524) baseStart_153524 baseEnd_153524 := by
    simpa [prefixWord, tailWord_153524, baseEnd_153524] using wordTrace_append hprefix tailTrace_153524
  have hstable : (prefixWord ++ tailWord_153524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153524).length < 2 ^ (prefixWord ++ tailWord_153524).sum := by decide
  have hdescent : baseEnd_153524 < baseStart_153524 := by decide
  rcases family_descends (prefixWord ++ tailWord_153524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153556 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 5]
def baseStart_153556 : Nat := 118140960795 + 153556 * 2 ^ 59
def prefixEnd_153556 : Nat := 4983230072969 + 3 ^ 40 * 153556 * 2
def baseEnd_153556 : Nat := 70087142561694617905613

theorem tailTrace_153556 : CollatzResearch.WordTrace tailWord_153556 prefixEnd_153556 70087142561694617905613 := by
  unfold tailWord_153556
  simp only [CollatzResearch.WordTrace]
  refine ⟨2800323715850156061004261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3733764954466874748005681 2800323715850156061004261)
  ·
    refine ⟨525060696721904261438299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2800323715850156061004261 525060696721904261438299)
    ·
      refine ⟨787591045082856392157449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 525060696721904261438299 787591045082856392157449)
      ·
        refine ⟨590693283812142294118087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 787591045082856392157449 590693283812142294118087)
        ·
          refine ⟨886039925718213441177131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590693283812142294118087 886039925718213441177131)
          ·
            refine ⟨1329059888577320161765697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 886039925718213441177131 1329059888577320161765697)
            ·
              refine ⟨996794916432990121324273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1329059888577320161765697 996794916432990121324273)
              ·
                refine ⟨747596187324742590993205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 996794916432990121324273 747596187324742590993205)
                ·
                  refine ⟨70087142561694617905613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 747596187324742590993205 70087142561694617905613)
                  ·
                    rfl

theorem cell20_153556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_153556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153556 prefixEnd_153556 := by exact prefixLift 153556
  have htrace : WordTrace (prefixWord ++ tailWord_153556) baseStart_153556 baseEnd_153556 := by
    simpa [prefixWord, tailWord_153556, baseEnd_153556] using wordTrace_append hprefix tailTrace_153556
  have hstable : (prefixWord ++ tailWord_153556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153556).length < 2 ^ (prefixWord ++ tailWord_153556).sum := by decide
  have hdescent : baseEnd_153556 < baseStart_153556 := by decide
  rcases family_descends (prefixWord ++ tailWord_153556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153601 : List Nat := [1, 2, 4, 1, 2, 1, 1, 4, 4]
def baseStart_153601 : Nat := 118140960795 + 153601 * 2 ^ 59
def prefixEnd_153601 : Nat := 4983230072969 + 3 ^ 40 * 153601 * 2
def baseEnd_153601 : Nat := 70107681787874461405429

theorem tailTrace_153601 : CollatzResearch.WordTrace tailWord_153601 prefixEnd_153601 70107681787874461405429 := by
  unfold tailWord_153601
  simp only [CollatzResearch.WordTrace]
  refine ⟨5602288716537284807396657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3734859144358189871597771 5602288716537284807396657)
  ·
    refine ⟨4201716537402963605547493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5602288716537284807396657 4201716537402963605547493)
    ·
      refine ⟨787821850763055676040155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4201716537402963605547493 787821850763055676040155)
      ·
        refine ⟨1181732776144583514060233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 787821850763055676040155 1181732776144583514060233)
        ·
          refine ⟨886299582108437635545175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1181732776144583514060233 886299582108437635545175)
          ·
            refine ⟨1329449373162656453317763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 886299582108437635545175 1329449373162656453317763)
            ·
              refine ⟨1994174059743984679976645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1329449373162656453317763 1994174059743984679976645)
              ·
                refine ⟨373907636201997127495621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1994174059743984679976645 373907636201997127495621)
                ·
                  refine ⟨70107681787874461405429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 373907636201997127495621 70107681787874461405429)
                  ·
                    rfl

theorem cell20_153601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_153601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153601 prefixEnd_153601 := by exact prefixLift 153601
  have htrace : WordTrace (prefixWord ++ tailWord_153601) baseStart_153601 baseEnd_153601 := by
    simpa [prefixWord, tailWord_153601, baseEnd_153601] using wordTrace_append hprefix tailTrace_153601
  have hstable : (prefixWord ++ tailWord_153601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153601).length < 2 ^ (prefixWord ++ tailWord_153601).sum := by decide
  have hdescent : baseEnd_153601 < baseStart_153601 := by decide
  rcases family_descends (prefixWord ++ tailWord_153601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153604 : List Nat := [2, 3, 2, 4, 1, 1, 1, 6]
def baseStart_153604 : Nat := 118140960795 + 153604 * 2 ^ 59
def prefixEnd_153604 : Nat := 4983230072969 + 3 ^ 40 * 153604 * 2
def baseEnd_153604 : Nat := 23369683689873261435139

theorem tailTrace_153604 : CollatzResearch.WordTrace tailWord_153604 prefixEnd_153604 23369683689873261435139 := by
  unfold tailWord_153604
  simp only [CollatzResearch.WordTrace]
  refine ⟨2801199067763208159877933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3734932090350944213170577 2801199067763208159877933)
  ·
    refine ⟨1050449650411203059954225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2801199067763208159877933 1050449650411203059954225)
    ·
      refine ⟨787837237808402294965669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1050449650411203059954225 787837237808402294965669)
      ·
        refine ⟨147719482089075430306063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 787837237808402294965669 147719482089075430306063)
        ·
          refine ⟨221579223133613145459095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147719482089075430306063 221579223133613145459095)
          ·
            refine ⟨332368834700419718188643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221579223133613145459095 332368834700419718188643)
            ·
              refine ⟨498553252050629577282965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332368834700419718188643 498553252050629577282965)
              ·
                refine ⟨23369683689873261435139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 498553252050629577282965 23369683689873261435139)
                ·
                  rfl

theorem cell20_153604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 6].length) (baseStart_153604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153604 prefixEnd_153604 := by exact prefixLift 153604
  have htrace : WordTrace (prefixWord ++ tailWord_153604) baseStart_153604 baseEnd_153604 := by
    simpa [prefixWord, tailWord_153604, baseEnd_153604] using wordTrace_append hprefix tailTrace_153604
  have hstable : (prefixWord ++ tailWord_153604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153604).length < 2 ^ (prefixWord ++ tailWord_153604).sum := by decide
  have hdescent : baseEnd_153604 < baseStart_153604 := by decide
  rcases family_descends (prefixWord ++ tailWord_153604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153606 : List Nat := [6, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_153606 : Nat := 118140960795 + 153606 * 2 ^ 59
def prefixEnd_153606 : Nat := 4983230072969 + 3 ^ 40 * 153606 * 2
def baseEnd_153606 : Nat := 70109963924116666238743

theorem tailTrace_153606 : CollatzResearch.WordTrace tailWord_153606 prefixEnd_153606 70109963924116666238743 := by
  unfold tailWord_153606
  simp only [CollatzResearch.WordTrace]
  refine ⟨175077221297474083166521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3734980721012780440885781 175077221297474083166521)
  ·
    refine ⟨131307915973105562374891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175077221297474083166521 131307915973105562374891)
    ·
      refine ⟨196961873959658343562337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131307915973105562374891 196961873959658343562337)
      ·
        refine ⟨147721405469743757671753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196961873959658343562337 147721405469743757671753)
        ·
          refine ⟨110791054102307818253815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147721405469743757671753 110791054102307818253815)
          ·
            refine ⟨166186581153461727380723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110791054102307818253815 166186581153461727380723)
            ·
              refine ⟨249279871730192591071085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166186581153461727380723 249279871730192591071085)
              ·
                refine ⟨93479951898822221651657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 249279871730192591071085 93479951898822221651657)
                ·
                  refine ⟨70109963924116666238743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93479951898822221651657 70109963924116666238743)
                  ·
                    rfl

theorem cell20_153606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_153606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153606 prefixEnd_153606 := by exact prefixLift 153606
  have htrace : WordTrace (prefixWord ++ tailWord_153606) baseStart_153606 baseEnd_153606 := by
    simpa [prefixWord, tailWord_153606, baseEnd_153606] using wordTrace_append hprefix tailTrace_153606
  have hstable : (prefixWord ++ tailWord_153606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153606).length < 2 ^ (prefixWord ++ tailWord_153606).sum := by decide
  have hdescent : baseEnd_153606 < baseStart_153606 := by decide
  rcases family_descends (prefixWord ++ tailWord_153606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153608 : List Nat := [2, 1, 3, 2, 1, 2, 3, 6]
def baseStart_153608 : Nat := 118140960795 + 153608 * 2 ^ 59
def prefixEnd_153608 : Nat := 4983230072969 + 3 ^ 40 * 153608 * 2
def baseEnd_153608 : Nat := 23370292259537849390689

theorem tailTrace_153608 : CollatzResearch.WordTrace tailWord_153608 prefixEnd_153608 23370292259537849390689 := by
  unfold tailWord_153608
  simp only [CollatzResearch.WordTrace]
  refine ⟨2801272013755962501450739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3735029351674616668600985 2801272013755962501450739)
  ·
    refine ⟨4201908020633943752176109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2801272013755962501450739 4201908020633943752176109)
    ·
      refine ⟨1575715507737728907066041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4201908020633943752176109 1575715507737728907066041)
      ·
        refine ⟨1181786630803296680299531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1575715507737728907066041 1181786630803296680299531)
        ·
          refine ⟨1772679946204945020449297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1181786630803296680299531 1772679946204945020449297)
          ·
            refine ⟨1329509959653708765336973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1772679946204945020449297 1329509959653708765336973)
            ·
              refine ⟨498566234870140787001365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1329509959653708765336973 498566234870140787001365)
              ·
                refine ⟨23370292259537849390689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 498566234870140787001365 23370292259537849390689)
                ·
                  rfl

theorem cell20_153608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_153608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153608 prefixEnd_153608 := by exact prefixLift 153608
  have htrace : WordTrace (prefixWord ++ tailWord_153608) baseStart_153608 baseEnd_153608 := by
    simpa [prefixWord, tailWord_153608, baseEnd_153608] using wordTrace_append hprefix tailTrace_153608
  have hstable : (prefixWord ++ tailWord_153608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153608).length < 2 ^ (prefixWord ++ tailWord_153608).sum := by decide
  have hdescent : baseEnd_153608 < baseStart_153608 := by decide
  rcases family_descends (prefixWord ++ tailWord_153608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153635 : List Nat := [1, 1, 1, 4, 3, 1, 5, 2, 2]
def baseStart_153635 : Nat := 118140960795 + 153635 * 2 ^ 59
def prefixEnd_153635 : Nat := 4983230072969 + 3 ^ 40 * 153635 * 2
def baseEnd_153635 : Nat := 70123200314321454271957

theorem tailTrace_153635 : CollatzResearch.WordTrace tailWord_153635 prefixEnd_153635 70123200314321454271957 := by
  unfold tailWord_153635
  simp only [CollatzResearch.WordTrace]
  refine ⟨5603528798414108614134359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3735685865609405742756239 5603528798414108614134359)
  ·
    refine ⟨8405293197621162921201539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5603528798414108614134359 8405293197621162921201539)
    ·
      refine ⟨12607939796431744381802309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8405293197621162921201539 12607939796431744381802309)
      ·
        refine ⟨2363988711830952071587933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12607939796431744381802309 2363988711830952071587933)
        ·
          refine ⟨886495766936607026845475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2363988711830952071587933 886495766936607026845475)
          ·
            refine ⟨1329743650404910540268213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 886495766936607026845475 1329743650404910540268213)
            ·
              refine ⟨124663467225460363150145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1329743650404910540268213 124663467225460363150145)
              ·
                refine ⟨93497600419095272362609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124663467225460363150145 93497600419095272362609)
                ·
                  refine ⟨70123200314321454271957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93497600419095272362609 70123200314321454271957)
                  ·
                    rfl

theorem cell20_153635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 2].length) (baseStart_153635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153635 prefixEnd_153635 := by exact prefixLift 153635
  have htrace : WordTrace (prefixWord ++ tailWord_153635) baseStart_153635 baseEnd_153635 := by
    simpa [prefixWord, tailWord_153635, baseEnd_153635] using wordTrace_append hprefix tailTrace_153635
  have hstable : (prefixWord ++ tailWord_153635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153635).length < 2 ^ (prefixWord ++ tailWord_153635).sum := by decide
  have hdescent : baseEnd_153635 < baseStart_153635 := by decide
  rcases family_descends (prefixWord ++ tailWord_153635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153649 : List Nat := [1, 2, 2, 3, 1, 3, 4, 1, 3]
def baseStart_153649 : Nat := 118140960795 + 153649 * 2 ^ 59
def prefixEnd_153649 : Nat := 4983230072969 + 3 ^ 40 * 153649 * 2
def baseEnd_153649 : Nat := 70129590295799627805233

theorem tailTrace_153649 : CollatzResearch.WordTrace tailWord_153649 prefixEnd_153649 70129590295799627805233 := by
  unfold tailWord_153649
  simp only [CollatzResearch.WordTrace]
  refine ⟨5604039420363389005144001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3736026280242259336762667 5604039420363389005144001)
  ·
    refine ⟨4203029565272541753858001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5604039420363389005144001 4203029565272541753858001)
    ·
      refine ⟨3152272173954406315393501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4203029565272541753858001 3152272173954406315393501)
      ·
        refine ⟨1182102065232902368272563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3152272173954406315393501 1182102065232902368272563)
        ·
          refine ⟨1773153097849353552408845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1182102065232902368272563 1773153097849353552408845)
          ·
            refine ⟨664932411693507582153317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1773153097849353552408845 664932411693507582153317)
            ·
              refine ⟨124674827192532671653747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 664932411693507582153317 124674827192532671653747)
              ·
                refine ⟨187012240788799007480621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124674827192532671653747 187012240788799007480621)
                ·
                  refine ⟨70129590295799627805233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 187012240788799007480621 70129590295799627805233)
                  ·
                    rfl

theorem cell20_153649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 3].length) (baseStart_153649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153649 prefixEnd_153649 := by exact prefixLift 153649
  have htrace : WordTrace (prefixWord ++ tailWord_153649) baseStart_153649 baseEnd_153649 := by
    simpa [prefixWord, tailWord_153649, baseEnd_153649] using wordTrace_append hprefix tailTrace_153649
  have hstable : (prefixWord ++ tailWord_153649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153649).length < 2 ^ (prefixWord ++ tailWord_153649).sum := by decide
  have hdescent : baseEnd_153649 < baseStart_153649 := by decide
  rcases family_descends (prefixWord ++ tailWord_153649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153686 : List Nat := [5, 2, 2, 1, 1, 3, 2, 2, 2]
def baseStart_153686 : Nat := 118140960795 + 153686 * 2 ^ 59
def prefixEnd_153686 : Nat := 4983230072969 + 3 ^ 40 * 153686 * 2
def baseEnd_153686 : Nat := 70146478103991943571749

theorem tailTrace_153686 : CollatzResearch.WordTrace tailWord_153686 prefixEnd_153686 70146478103991943571749 := by
  unfold tailWord_153686
  simp only [CollatzResearch.WordTrace]
  refine ⟨350336807576834020265057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3736925947486229549493941 350336807576834020265057)
  ·
    refine ⟨262752605682625515198793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 350336807576834020265057 262752605682625515198793)
    ·
      refine ⟨197064454261969136399095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262752605682625515198793 197064454261969136399095)
      ·
        refine ⟨295596681392953704598643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197064454261969136399095 295596681392953704598643)
        ·
          refine ⟨443395022089430556897965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295596681392953704598643 443395022089430556897965)
          ·
            refine ⟨166273133283536458836737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 443395022089430556897965 166273133283536458836737)
            ·
              refine ⟨124704849962652344127553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166273133283536458836737 124704849962652344127553)
              ·
                refine ⟨93528637471989258095665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124704849962652344127553 93528637471989258095665)
                ·
                  refine ⟨70146478103991943571749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93528637471989258095665 70146478103991943571749)
                  ·
                    rfl

theorem cell20_153686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_153686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153686 prefixEnd_153686 := by exact prefixLift 153686
  have htrace : WordTrace (prefixWord ++ tailWord_153686) baseStart_153686 baseEnd_153686 := by
    simpa [prefixWord, tailWord_153686, baseEnd_153686] using wordTrace_append hprefix tailTrace_153686
  have hstable : (prefixWord ++ tailWord_153686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153686).length < 2 ^ (prefixWord ++ tailWord_153686).sum := by decide
  have hdescent : baseEnd_153686 < baseStart_153686 := by decide
  rcases family_descends (prefixWord ++ tailWord_153686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153701 : List Nat := [1, 3, 1, 3, 2, 4, 1, 5]
def baseStart_153701 : Nat := 118140960795 + 153701 * 2 ^ 59
def prefixEnd_153701 : Nat := 4983230072969 + 3 ^ 40 * 153701 * 2
def baseEnd_153701 : Nat := 23384441504239519357229

theorem tailTrace_153701 : CollatzResearch.WordTrace tailWord_153701 prefixEnd_153701 23384441504239519357229 := by
  unfold tailWord_153701
  simp only [CollatzResearch.WordTrace]
  refine ⟨5605936016175001886036957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3737290677450001257357971 5605936016175001886036957)
  ·
    refine ⟨2102226006065625707263859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5605936016175001886036957 2102226006065625707263859)
    ·
      refine ⟨3153339009098438560895789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2102226006065625707263859 3153339009098438560895789)
      ·
        refine ⟨1182502128411914460335921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3153339009098438560895789 1182502128411914460335921)
        ·
          refine ⟨886876596308935845251941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1182502128411914460335921 886876596308935845251941)
          ·
            refine ⟨166289361807925470984739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 886876596308935845251941 166289361807925470984739)
            ·
              refine ⟨249434042711888206477109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166289361807925470984739 249434042711888206477109)
              ·
                refine ⟨23384441504239519357229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 249434042711888206477109 23384441504239519357229)
                ·
                  rfl

theorem cell20_153701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 5].length) (baseStart_153701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153701 prefixEnd_153701 := by exact prefixLift 153701
  have htrace : WordTrace (prefixWord ++ tailWord_153701) baseStart_153701 baseEnd_153701 := by
    simpa [prefixWord, tailWord_153701, baseEnd_153701] using wordTrace_append hprefix tailTrace_153701
  have hstable : (prefixWord ++ tailWord_153701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153701).length < 2 ^ (prefixWord ++ tailWord_153701).sum := by decide
  have hdescent : baseEnd_153701 < baseStart_153701 := by decide
  rcases family_descends (prefixWord ++ tailWord_153701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153708 : List Nat := [2, 2, 1, 1, 3, 3, 2, 3, 3]
def baseStart_153708 : Nat := 118140960795 + 153708 * 2 ^ 59
def prefixEnd_153708 : Nat := 4983230072969 + 3 ^ 40 * 153708 * 2
def baseEnd_153708 : Nat := 70156519503457644838325

theorem tailTrace_153708 : CollatzResearch.WordTrace tailWord_153708 prefixEnd_153708 70156519503457644838325 := by
  unfold tailWord_153708
  simp only [CollatzResearch.WordTrace]
  refine ⟨2803095663574821040770889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3737460884766428054361185 2803095663574821040770889)
  ·
    refine ⟨2102321747681115780578167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2803095663574821040770889 2102321747681115780578167)
    ·
      refine ⟨3153482621521673670867251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2102321747681115780578167 3153482621521673670867251)
      ·
        refine ⟨4730223932282510506300877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3153482621521673670867251 4730223932282510506300877)
        ·
          refine ⟨1773833974605941439862829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4730223932282510506300877 1773833974605941439862829)
          ·
            refine ⟨665187740477228039948561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1773833974605941439862829 665187740477228039948561)
            ·
              refine ⟨498890805357921029961421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 665187740477228039948561 498890805357921029961421)
              ·
                refine ⟨187084052009220386235533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 498890805357921029961421 187084052009220386235533)
                ·
                  refine ⟨70156519503457644838325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 187084052009220386235533 70156519503457644838325)
                  ·
                    rfl

theorem cell20_153708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_153708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153708 prefixEnd_153708 := by exact prefixLift 153708
  have htrace : WordTrace (prefixWord ++ tailWord_153708) baseStart_153708 baseEnd_153708 := by
    simpa [prefixWord, tailWord_153708, baseEnd_153708] using wordTrace_append hprefix tailTrace_153708
  have hstable : (prefixWord ++ tailWord_153708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153708).length < 2 ^ (prefixWord ++ tailWord_153708).sum := by decide
  have hdescent : baseEnd_153708 < baseStart_153708 := by decide
  rcases family_descends (prefixWord ++ tailWord_153708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153718 : List Nat := [5, 1, 1, 2, 1, 3, 3, 4]
def baseStart_153718 : Nat := 118140960795 + 153718 * 2 ^ 59
def prefixEnd_153718 : Nat := 4983230072969 + 3 ^ 40 * 153718 * 2
def baseEnd_153718 : Nat := 23387027925314018168317

theorem tailTrace_153718 : CollatzResearch.WordTrace tailWord_153718 prefixEnd_153718 23387027925314018168317 := by
  unfold tailWord_153718
  simp only [CollatzResearch.WordTrace]
  refine ⟨350409753569588361837863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3737704038075609192937205 350409753569588361837863)
  ·
    refine ⟨525614630354382542756795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 350409753569588361837863 525614630354382542756795)
    ·
      refine ⟨788421945531573814135193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 525614630354382542756795 788421945531573814135193)
      ·
        refine ⟨591316459148680360601395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 788421945531573814135193 591316459148680360601395)
        ·
          refine ⟨886974688723020540902093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591316459148680360601395 886974688723020540902093)
          ·
            refine ⟨332615508271132702838285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 886974688723020540902093 332615508271132702838285)
            ·
              refine ⟨124730815601674763564357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 332615508271132702838285 124730815601674763564357)
              ·
                refine ⟨23387027925314018168317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124730815601674763564357 23387027925314018168317)
                ·
                  rfl

theorem cell20_153718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_153718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153718 prefixEnd_153718 := by exact prefixLift 153718
  have htrace : WordTrace (prefixWord ++ tailWord_153718) baseStart_153718 baseEnd_153718 := by
    simpa [prefixWord, tailWord_153718, baseEnd_153718] using wordTrace_append hprefix tailTrace_153718
  have hstable : (prefixWord ++ tailWord_153718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153718).length < 2 ^ (prefixWord ++ tailWord_153718).sum := by decide
  have hdescent : baseEnd_153718 < baseStart_153718 := by decide
  rcases family_descends (prefixWord ++ tailWord_153718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153742 : List Nat := [4, 1, 1, 3, 3, 2, 1, 2, 3]
def baseStart_153742 : Nat := 118140960795 + 153742 * 2 ^ 59
def prefixEnd_153742 : Nat := 4983230072969 + 3 ^ 40 * 153742 * 2
def baseEnd_153742 : Nat := 70172038029904637704853

theorem tailTrace_153742 : CollatzResearch.WordTrace tailWord_153742 prefixEnd_153742 70172038029904637704853 := by
  unfold tailWord_153742
  simp only [CollatzResearch.WordTrace]
  refine ⟨700928926128308236034935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3738287606017643925519653 700928926128308236034935)
  ·
    refine ⟨1051393389192462354052403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 700928926128308236034935 1051393389192462354052403)
    ·
      refine ⟨1577090083788693531078605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1051393389192462354052403 1577090083788693531078605)
      ·
        refine ⟨591408781420760074154477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1577090083788693531078605 591408781420760074154477)
        ·
          refine ⟨221778293032785027807929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 591408781420760074154477 221778293032785027807929)
          ·
            refine ⟨166333719774588770855947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221778293032785027807929 166333719774588770855947)
            ·
              refine ⟨249500579661883156283921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166333719774588770855947 249500579661883156283921)
              ·
                refine ⟨187125434746412367212941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249500579661883156283921 187125434746412367212941)
                ·
                  refine ⟨70172038029904637704853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 187125434746412367212941 70172038029904637704853)
                  ·
                    rfl

theorem cell20_153742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_153742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153742 prefixEnd_153742 := by exact prefixLift 153742
  have htrace : WordTrace (prefixWord ++ tailWord_153742) baseStart_153742 baseEnd_153742 := by
    simpa [prefixWord, tailWord_153742, baseEnd_153742] using wordTrace_append hprefix tailTrace_153742
  have hstable : (prefixWord ++ tailWord_153742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153742).length < 2 ^ (prefixWord ++ tailWord_153742).sum := by decide
  have hdescent : baseEnd_153742 < baseStart_153742 := by decide
  rcases family_descends (prefixWord ++ tailWord_153742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153746 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 5]
def baseStart_153746 : Nat := 118140960795 + 153746 * 2 ^ 59
def prefixEnd_153746 : Nat := 4983230072969 + 3 ^ 40 * 153746 * 2
def baseEnd_153746 : Nat := 70173863738898401571503

theorem tailTrace_153746 : CollatzResearch.WordTrace tailWord_153746 prefixEnd_153746 70173863738898401571503 := by
  unfold tailWord_153746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1401894325252993642856273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3738384867341316380950061 1401894325252993642856273)
  ·
    refine ⟨1051420743939745232142205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1401894325252993642856273 1051420743939745232142205)
    ·
      refine ⟨394282778977404462053327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1051420743939745232142205 394282778977404462053327)
      ·
        refine ⟨591424168466106693079991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394282778977404462053327 591424168466106693079991)
        ·
          refine ⟨887136252699160039619987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591424168466106693079991 887136252699160039619987)
          ·
            refine ⟨1330704379048740059429981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 887136252699160039619987 1330704379048740059429981)
            ·
              refine ⟨499014142143277522286243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1330704379048740059429981 499014142143277522286243)
              ·
                refine ⟨748521213214916283429365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499014142143277522286243 748521213214916283429365)
                ·
                  refine ⟨70173863738898401571503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 748521213214916283429365 70173863738898401571503)
                  ·
                    rfl

theorem cell20_153746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_153746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153746 prefixEnd_153746 := by exact prefixLift 153746
  have htrace : WordTrace (prefixWord ++ tailWord_153746) baseStart_153746 baseEnd_153746 := by
    simpa [prefixWord, tailWord_153746, baseEnd_153746] using wordTrace_append hprefix tailTrace_153746
  have hstable : (prefixWord ++ tailWord_153746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153746).length < 2 ^ (prefixWord ++ tailWord_153746).sum := by decide
  have hdescent : baseEnd_153746 < baseStart_153746 := by decide
  rcases family_descends (prefixWord ++ tailWord_153746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153777 : List Nat := [1, 2, 2, 5, 2, 1, 1, 6]
def baseStart_153777 : Nat := 118140960795 + 153777 * 2 ^ 59
def prefixEnd_153777 : Nat := 4983230072969 + 3 ^ 40 * 153777 * 2
def baseEnd_153777 : Nat := 23396004327866690512681

theorem tailTrace_153777 : CollatzResearch.WordTrace tailWord_153777 prefixEnd_153777 23396004327866690512681 := by
  unfold tailWord_153777
  simp only [CollatzResearch.WordTrace]
  refine ⟨5608707963899666865803585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3739138642599777910535723 5608707963899666865803585)
  ·
    refine ⟨4206530972924750149352689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5608707963899666865803585 4206530972924750149352689)
    ·
      refine ⟨3154898229693562612014517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4206530972924750149352689 3154898229693562612014517)
      ·
        refine ⟨295771709033771494876361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3154898229693562612014517 295771709033771494876361)
        ·
          refine ⟨221828781775328621157271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295771709033771494876361 221828781775328621157271)
          ·
            refine ⟨332743172662992931735907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221828781775328621157271 332743172662992931735907)
            ·
              refine ⟨499114758994489397603861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332743172662992931735907 499114758994489397603861)
              ·
                refine ⟨23396004327866690512681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 499114758994489397603861 23396004327866690512681)
                ·
                  rfl

theorem cell20_153777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 6].length) (baseStart_153777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153777 prefixEnd_153777 := by exact prefixLift 153777
  have htrace : WordTrace (prefixWord ++ tailWord_153777) baseStart_153777 baseEnd_153777 := by
    simpa [prefixWord, tailWord_153777, baseEnd_153777] using wordTrace_append hprefix tailTrace_153777
  have hstable : (prefixWord ++ tailWord_153777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153777).length < 2 ^ (prefixWord ++ tailWord_153777).sum := by decide
  have hdescent : baseEnd_153777 < baseStart_153777 := by decide
  rcases family_descends (prefixWord ++ tailWord_153777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153794 : List Nat := [3, 5, 1, 1, 1, 1, 8]
def baseStart_153794 : Nat := 118140960795 + 153794 * 2 ^ 59
def prefixEnd_153794 : Nat := 4983230072969 + 3 ^ 40 * 153794 * 2
def baseEnd_153794 : Nat := 7799530249647063107923

theorem tailTrace_153794 : CollatzResearch.WordTrace tailWord_153794 prefixEnd_153794 7799530249647063107923 := by
  unfold tailWord_153794
  simp only [CollatzResearch.WordTrace]
  refine ⟨1402332001209519692293109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3739552003225385846114957 1402332001209519692293109)
  ·
    refine ⟨131468625113392471152479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1402332001209519692293109 131468625113392471152479)
    ·
      refine ⟨197202937670088706728719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131468625113392471152479 197202937670088706728719)
      ·
        refine ⟨295804406505133060093079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197202937670088706728719 295804406505133060093079)
        ·
          refine ⟨443706609757699590139619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295804406505133060093079 443706609757699590139619)
          ·
            refine ⟨665559914636549385209429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443706609757699590139619 665559914636549385209429)
            ·
              refine ⟨7799530249647063107923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 665559914636549385209429 7799530249647063107923)
              ·
                rfl

theorem cell20_153794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 8].length) (baseStart_153794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153794 prefixEnd_153794 := by exact prefixLift 153794
  have htrace : WordTrace (prefixWord ++ tailWord_153794) baseStart_153794 baseEnd_153794 := by
    simpa [prefixWord, tailWord_153794, baseEnd_153794] using wordTrace_append hprefix tailTrace_153794
  have hstable : (prefixWord ++ tailWord_153794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153794).length < 2 ^ (prefixWord ++ tailWord_153794).sum := by decide
  have hdescent : baseEnd_153794 < baseStart_153794 := by decide
  rcases family_descends (prefixWord ++ tailWord_153794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153804 : List Nat := [2, 2, 1, 6, 2, 1, 1, 1, 4]
def baseStart_153804 : Nat := 118140960795 + 153804 * 2 ^ 59
def prefixEnd_153804 : Nat := 4983230072969 + 3 ^ 40 * 153804 * 2
def baseEnd_153804 : Nat := 70200336519307977637933

theorem tailTrace_153804 : CollatzResearch.WordTrace tailWord_153804 prefixEnd_153804 70200336519307977637933 := by
  unfold tailWord_153804
  simp only [CollatzResearch.WordTrace]
  refine ⟨2804846367400925238518233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3739795156534566984690977 2804846367400925238518233)
  ·
    refine ⟨2103634775550693928888675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2804846367400925238518233 2103634775550693928888675)
    ·
      refine ⟨3155452163326040893333013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2103634775550693928888675 3155452163326040893333013)
      ·
        refine ⟨147911820155908166874985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3155452163326040893333013 147911820155908166874985)
        ·
          refine ⟨110933865116931125156239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147911820155908166874985 110933865116931125156239)
          ·
            refine ⟨166400797675396687734359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110933865116931125156239 166400797675396687734359)
            ·
              refine ⟨249601196513095031601539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166400797675396687734359 249601196513095031601539)
              ·
                refine ⟨374401794769642547402309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249601196513095031601539 374401794769642547402309)
                ·
                  refine ⟨70200336519307977637933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 374401794769642547402309 70200336519307977637933)
                  ·
                    rfl

theorem cell20_153804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 4].length) (baseStart_153804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153804 prefixEnd_153804 := by exact prefixLift 153804
  have htrace : WordTrace (prefixWord ++ tailWord_153804) baseStart_153804 baseEnd_153804 := by
    simpa [prefixWord, tailWord_153804, baseEnd_153804] using wordTrace_append hprefix tailTrace_153804
  have hstable : (prefixWord ++ tailWord_153804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153804).length < 2 ^ (prefixWord ++ tailWord_153804).sum := by decide
  have hdescent : baseEnd_153804 < baseStart_153804 := by decide
  rcases family_descends (prefixWord ++ tailWord_153804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153819 : List Nat := [1, 1, 1, 1, 1, 1, 1, 13]
def baseStart_153819 : Nat := 118140960795 + 153819 * 2 ^ 59
def prefixEnd_153819 : Nat := 4983230072969 + 3 ^ 40 * 153819 * 2
def baseEnd_153819 : Nat := 23402394309344864045957

theorem tailTrace_153819 : CollatzResearch.WordTrace tailWord_153819 prefixEnd_153819 23402394309344864045957 := by
  unfold tailWord_153819
  simp only [CollatzResearch.WordTrace]
  refine ⟨5610239829747508038832511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3740159886498338692555007 5610239829747508038832511)
  ·
    refine ⟨8415359744621262058248767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5610239829747508038832511 8415359744621262058248767)
    ·
      refine ⟨12623039616931893087373151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8415359744621262058248767 12623039616931893087373151)
      ·
        refine ⟨18934559425397839631059727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12623039616931893087373151 18934559425397839631059727)
        ·
          refine ⟨28401839138096759446589591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18934559425397839631059727 28401839138096759446589591)
          ·
            refine ⟨42602758707145139169884387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28401839138096759446589591 42602758707145139169884387)
            ·
              refine ⟨63904138060717708754826581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42602758707145139169884387 63904138060717708754826581)
              ·
                refine ⟨23402394309344864045957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 63904138060717708754826581 23402394309344864045957)
                ·
                  rfl

theorem cell20_153819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 13].length) (baseStart_153819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153819 prefixEnd_153819 := by exact prefixLift 153819
  have htrace : WordTrace (prefixWord ++ tailWord_153819) baseStart_153819 baseEnd_153819 := by
    simpa [prefixWord, tailWord_153819, baseEnd_153819] using wordTrace_append hprefix tailTrace_153819
  have hstable : (prefixWord ++ tailWord_153819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153819).length < 2 ^ (prefixWord ++ tailWord_153819).sum := by decide
  have hdescent : baseEnd_153819 < baseStart_153819 := by decide
  rcases family_descends (prefixWord ++ tailWord_153819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153919 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 5]
def baseStart_153919 : Nat := 118140960795 + 153919 * 2 ^ 59
def prefixEnd_153919 : Nat := 4983230072969 + 3 ^ 40 * 153919 * 2
def baseEnd_153919 : Nat := 70252825652878688804129

theorem tailTrace_153919 : CollatzResearch.WordTrace tailWord_153919 prefixEnd_153919 70252825652878688804129 := by
  unfold tailWord_153919
  simp only [CollatzResearch.WordTrace]
  refine ⟨5613887129385225117472811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3742591419590150078315207 5613887129385225117472811)
  ·
    refine ⟨8420830694077837676209217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5613887129385225117472811 8420830694077837676209217)
    ·
      refine ⟨6315623020558378257156913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8420830694077837676209217 6315623020558378257156913)
      ·
        refine ⟨4736717265418783692867685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6315623020558378257156913 4736717265418783692867685)
        ·
          refine ⟨888134487266021942412691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4736717265418783692867685 888134487266021942412691)
          ·
            refine ⟨1332201730899032913619037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888134487266021942412691 1332201730899032913619037)
            ·
              refine ⟨499575649087137342607139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1332201730899032913619037 499575649087137342607139)
              ·
                refine ⟨749363473630706013910709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499575649087137342607139 749363473630706013910709)
                ·
                  refine ⟨70252825652878688804129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 749363473630706013910709 70252825652878688804129)
                  ·
                    rfl

theorem cell20_153919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 5].length) (baseStart_153919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153919 prefixEnd_153919 := by exact prefixLift 153919
  have htrace : WordTrace (prefixWord ++ tailWord_153919) baseStart_153919 baseEnd_153919 := by
    simpa [prefixWord, tailWord_153919, baseEnd_153919] using wordTrace_append hprefix tailTrace_153919
  have hstable : (prefixWord ++ tailWord_153919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153919).length < 2 ^ (prefixWord ++ tailWord_153919).sum := by decide
  have hdescent : baseEnd_153919 < baseStart_153919 := by decide
  rcases family_descends (prefixWord ++ tailWord_153919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153957 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 5]
def baseStart_153957 : Nat := 118140960795 + 153957 * 2 ^ 59
def prefixEnd_153957 : Nat := 4983230072969 + 3 ^ 40 * 153957 * 2
def baseEnd_153957 : Nat := 70270169888319445537307

theorem tailTrace_153957 : CollatzResearch.WordTrace tailWord_153957 prefixEnd_153957 70270169888319445537307 := by
  unfold tailWord_153957
  simp only [CollatzResearch.WordTrace]
  refine ⟨5615273103247557607356125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3743515402165038404904083 5615273103247557607356125)
  ·
    refine ⟨2105727413717834102758547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5615273103247557607356125 2105727413717834102758547)
    ·
      refine ⟨3158591120576751154137821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2105727413717834102758547 3158591120576751154137821)
      ·
        refine ⟨1184471670216281682801683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3158591120576751154137821 1184471670216281682801683)
        ·
          refine ⟨1776707505324422524202525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1184471670216281682801683 1776707505324422524202525)
          ·
            refine ⟨666265314496658446575947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1776707505324422524202525 666265314496658446575947)
            ·
              refine ⟨999397971744987669863921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 666265314496658446575947 999397971744987669863921)
              ·
                refine ⟨749548478808740752397941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 999397971744987669863921 749548478808740752397941)
                ·
                  refine ⟨70270169888319445537307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 749548478808740752397941 70270169888319445537307)
                  ·
                    rfl

theorem cell20_153957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_153957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153957 prefixEnd_153957 := by exact prefixLift 153957
  have htrace : WordTrace (prefixWord ++ tailWord_153957) baseStart_153957 baseEnd_153957 := by
    simpa [prefixWord, tailWord_153957, baseEnd_153957] using wordTrace_append hprefix tailTrace_153957
  have hstable : (prefixWord ++ tailWord_153957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153957).length < 2 ^ (prefixWord ++ tailWord_153957).sum := by decide
  have hdescent : baseEnd_153957 < baseStart_153957 := by decide
  rcases family_descends (prefixWord ++ tailWord_153957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153981 : List Nat := [1, 4, 1, 1, 2, 3, 3, 1, 4]
def baseStart_153981 : Nat := 118140960795 + 153981 * 2 ^ 59
def prefixEnd_153981 : Nat := 4983230072969 + 3 ^ 40 * 153981 * 2
def baseEnd_153981 : Nat := 70281124142282028737209

theorem tailTrace_153981 : CollatzResearch.WordTrace tailWord_153981 prefixEnd_153981 70281124142282028737209 := by
  unfold tailWord_153981
  simp only [CollatzResearch.WordTrace]
  refine ⟨5616148455160609706229797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3744098970107073137486531 5616148455160609706229797)
  ·
    refine ⟨1053027835342614319918087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5616148455160609706229797 1053027835342614319918087)
    ·
      refine ⟨1579541753013921479877131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1053027835342614319918087 1579541753013921479877131)
      ·
        refine ⟨2369312629520882219815697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1579541753013921479877131 2369312629520882219815697)
        ·
          refine ⟨1776984472140661664861773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2369312629520882219815697 1776984472140661664861773)
          ·
            refine ⟨666369177052748124323165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1776984472140661664861773 666369177052748124323165)
            ·
              refine ⟨249888441394780546621187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 666369177052748124323165 249888441394780546621187)
              ·
                refine ⟨374832662092170819931781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249888441394780546621187 374832662092170819931781)
                ·
                  refine ⟨70281124142282028737209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 374832662092170819931781 70281124142282028737209)
                  ·
                    rfl

theorem cell20_153981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_153981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153981 prefixEnd_153981 := by exact prefixLift 153981
  have htrace : WordTrace (prefixWord ++ tailWord_153981) baseStart_153981 baseEnd_153981 := by
    simpa [prefixWord, tailWord_153981, baseEnd_153981] using wordTrace_append hprefix tailTrace_153981
  have hstable : (prefixWord ++ tailWord_153981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153981).length < 2 ^ (prefixWord ++ tailWord_153981).sum := by decide
  have hdescent : baseEnd_153981 < baseStart_153981 := by decide
  rcases family_descends (prefixWord ++ tailWord_153981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153988 : List Nat := [2, 3, 2, 1, 1, 2, 4, 5]
def baseStart_153988 : Nat := 118140960795 + 153988 * 2 ^ 59
def prefixEnd_153988 : Nat := 4983230072969 + 3 ^ 40 * 153988 * 2
def baseEnd_153988 : Nat := 23428106377673705167949

theorem tailTrace_153988 : CollatzResearch.WordTrace tailWord_153988 prefixEnd_153988 23428106377673705167949 := by
  unfold tailWord_153988
  simp only [CollatzResearch.WordTrace]
  refine ⟨2808201883067624950867309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3744269177423499934489745 2808201883067624950867309)
  ·
    refine ⟨1053075706150359356575241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2808201883067624950867309 1053075706150359356575241)
    ·
      refine ⟨789806779612769517431431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1053075706150359356575241 789806779612769517431431)
      ·
        refine ⟨1184710169419154276147147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 789806779612769517431431 1184710169419154276147147)
        ·
          refine ⟨1777065254128731414220721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1184710169419154276147147 1777065254128731414220721)
          ·
            refine ⟨1332798940596548560665541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1777065254128731414220721 1332798940596548560665541)
            ·
              refine ⟨249899801361852855124789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1332798940596548560665541 249899801361852855124789)
              ·
                refine ⟨23428106377673705167949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 249899801361852855124789 23428106377673705167949)
                ·
                  rfl

theorem cell20_153988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_153988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_153988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_153988 prefixEnd_153988 := by exact prefixLift 153988
  have htrace : WordTrace (prefixWord ++ tailWord_153988) baseStart_153988 baseEnd_153988 := by
    simpa [prefixWord, tailWord_153988, baseEnd_153988] using wordTrace_append hprefix tailTrace_153988
  have hstable : (prefixWord ++ tailWord_153988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153988).length < 2 ^ (prefixWord ++ tailWord_153988).sum := by decide
  have hdescent : baseEnd_153988 < baseStart_153988 := by decide
  rcases family_descends (prefixWord ++ tailWord_153988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154009 : List Nat := [1, 2, 1, 2, 1, 4, 1, 8]
def baseStart_154009 : Nat := 118140960795 + 154009 * 2 ^ 59
def prefixEnd_154009 : Nat := 4983230072969 + 3 ^ 40 * 154009 * 2
def baseEnd_154009 : Nat := 23431301368412791934587

theorem tailTrace_154009 : CollatzResearch.WordTrace tailWord_154009 prefixEnd_154009 23431301368412791934587 := by
  unfold tailWord_154009
  simp only [CollatzResearch.WordTrace]
  refine ⟨5617169699059170488249081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3744779799372780325499387 5617169699059170488249081)
  ·
    refine ⟨4212877274294377866186811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5617169699059170488249081 4212877274294377866186811)
    ·
      refine ⟨6319315911441566799280217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4212877274294377866186811 6319315911441566799280217)
      ·
        refine ⟨4739486933581175099460163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6319315911441566799280217 4739486933581175099460163)
        ·
          refine ⟨7109230400371762649190245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4739486933581175099460163 7109230400371762649190245)
          ·
            refine ⟨1332980700069705496723171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7109230400371762649190245 1332980700069705496723171)
            ·
              refine ⟨1999471050104558245084757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1332980700069705496723171 1999471050104558245084757)
              ·
                refine ⟨23431301368412791934587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1999471050104558245084757 23431301368412791934587)
                ·
                  rfl

theorem cell20_154009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 8].length) (baseStart_154009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154009 prefixEnd_154009 := by exact prefixLift 154009
  have htrace : WordTrace (prefixWord ++ tailWord_154009) baseStart_154009 baseEnd_154009 := by
    simpa [prefixWord, tailWord_154009, baseEnd_154009] using wordTrace_append hprefix tailTrace_154009
  have hstable : (prefixWord ++ tailWord_154009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154009).length < 2 ^ (prefixWord ++ tailWord_154009).sum := by decide
  have hdescent : baseEnd_154009 < baseStart_154009 := by decide
  rcases family_descends (prefixWord ++ tailWord_154009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154040 : List Nat := [2, 1, 2, 1, 2, 2, 1, 5, 4]
def baseStart_154040 : Nat := 118140960795 + 154040 * 2 ^ 59
def prefixEnd_154040 : Nat := 4983230072969 + 3 ^ 40 * 154040 * 2
def baseEnd_154040 : Nat := 70308053349940045770301

theorem tailTrace_154040 : CollatzResearch.WordTrace tailWord_154040 prefixEnd_154040 70308053349940045770301 := by
  unfold tailWord_154040
  simp only [CollatzResearch.WordTrace]
  refine ⟨2809150180973431391313787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3745533574631241855085049 2809150180973431391313787)
  ·
    refine ⟨4213725271460147086970681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2809150180973431391313787 4213725271460147086970681)
    ·
      refine ⟨3160293953595110315228011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4213725271460147086970681 3160293953595110315228011)
      ·
        refine ⟨4740440930392665472842017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3160293953595110315228011 4740440930392665472842017)
        ·
          refine ⟨3555330697794499104631513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4740440930392665472842017 3555330697794499104631513)
          ·
            refine ⟨2666498023345874328473635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3555330697794499104631513 2666498023345874328473635)
            ·
              refine ⟨3999747035018811492710453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2666498023345874328473635 3999747035018811492710453)
              ·
                refine ⟨374976284533013577441605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3999747035018811492710453 374976284533013577441605)
                ·
                  refine ⟨70308053349940045770301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 374976284533013577441605 70308053349940045770301)
                  ·
                    rfl

theorem cell20_154040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_154040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154040 prefixEnd_154040 := by exact prefixLift 154040
  have htrace : WordTrace (prefixWord ++ tailWord_154040) baseStart_154040 baseEnd_154040 := by
    simpa [prefixWord, tailWord_154040, baseEnd_154040] using wordTrace_append hprefix tailTrace_154040
  have hstable : (prefixWord ++ tailWord_154040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154040).length < 2 ^ (prefixWord ++ tailWord_154040).sum := by decide
  have hdescent : baseEnd_154040 < baseStart_154040 := by decide
  rcases family_descends (prefixWord ++ tailWord_154040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154074 : List Nat := [3, 1, 1, 2, 3, 1, 4, 3, 2]
def baseStart_154074 : Nat := 118140960795 + 154074 * 2 ^ 59
def prefixEnd_154074 : Nat := 4983230072969 + 3 ^ 40 * 154074 * 2
def baseEnd_154074 : Nat := 70323571876387038636829

theorem tailTrace_154074 : CollatzResearch.WordTrace tailWord_154074 prefixEnd_154074 70323571876387038636829 := by
  unfold tailWord_154074
  simp only [CollatzResearch.WordTrace]
  refine ⟨1404885110955921647341319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3746360295882457726243517 1404885110955921647341319)
  ·
    refine ⟨2107327666433882471011979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1404885110955921647341319 2107327666433882471011979)
    ·
      refine ⟨3160991499650823706517969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2107327666433882471011979 3160991499650823706517969)
      ·
        refine ⟨2370743624738117779888477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3160991499650823706517969 2370743624738117779888477)
        ·
          refine ⟨889028859276794167458179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2370743624738117779888477 889028859276794167458179)
          ·
            refine ⟨1333543288915191251187269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889028859276794167458179 1333543288915191251187269)
            ·
              refine ⟨250039366671598359597613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1333543288915191251187269 250039366671598359597613)
              ·
                refine ⟨93764762501849384849105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 250039366671598359597613 93764762501849384849105)
                ·
                  refine ⟨70323571876387038636829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93764762501849384849105 70323571876387038636829)
                  ·
                    rfl

theorem cell20_154074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 2].length) (baseStart_154074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154074 prefixEnd_154074 := by exact prefixLift 154074
  have htrace : WordTrace (prefixWord ++ tailWord_154074) baseStart_154074 baseEnd_154074 := by
    simpa [prefixWord, tailWord_154074, baseEnd_154074] using wordTrace_append hprefix tailTrace_154074
  have hstable : (prefixWord ++ tailWord_154074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154074).length < 2 ^ (prefixWord ++ tailWord_154074).sum := by decide
  have hdescent : baseEnd_154074 < baseStart_154074 := by decide
  rcases family_descends (prefixWord ++ tailWord_154074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154088 : List Nat := [2, 1, 4, 1, 1, 3, 3, 2, 3]
def baseStart_154088 : Nat := 118140960795 + 154088 * 2 ^ 59
def prefixEnd_154088 : Nat := 4983230072969 + 3 ^ 40 * 154088 * 2
def baseEnd_154088 : Nat := 70329961857865212170105

theorem tailTrace_154088 : CollatzResearch.WordTrace tailWord_154088 prefixEnd_154088 70329961857865212170105 := by
  unfold tailWord_154088
  simp only [CollatzResearch.WordTrace]
  refine ⟨2810025532886483490187459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3746700710515311320249945 2810025532886483490187459)
  ·
    refine ⟨4215038299329725235281189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2810025532886483490187459 4215038299329725235281189)
    ·
      refine ⟨790319681124323481615223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4215038299329725235281189 790319681124323481615223)
      ·
        refine ⟨1185479521686485222422835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 790319681124323481615223 1185479521686485222422835)
        ·
          refine ⟨1778219282529727833634253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1185479521686485222422835 1778219282529727833634253)
          ·
            refine ⟨666832230948647937612845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1778219282529727833634253 666832230948647937612845)
            ·
              refine ⟨250062086605742976604817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 666832230948647937612845 250062086605742976604817)
              ·
                refine ⟨187546564954307232453613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 250062086605742976604817 187546564954307232453613)
                ·
                  refine ⟨70329961857865212170105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 187546564954307232453613 70329961857865212170105)
                  ·
                    rfl

theorem cell20_154088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 3].length) (baseStart_154088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154088 prefixEnd_154088 := by exact prefixLift 154088
  have htrace : WordTrace (prefixWord ++ tailWord_154088) baseStart_154088 baseEnd_154088 := by
    simpa [prefixWord, tailWord_154088, baseEnd_154088] using wordTrace_append hprefix tailTrace_154088
  have hstable : (prefixWord ++ tailWord_154088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154088).length < 2 ^ (prefixWord ++ tailWord_154088).sum := by decide
  have hdescent : baseEnd_154088 < baseStart_154088 := by decide
  rcases family_descends (prefixWord ++ tailWord_154088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154102 : List Nat := [5, 1, 1, 1, 2, 1, 2, 7]
def baseStart_154102 : Nat := 118140960795 + 154102 * 2 ^ 59
def prefixEnd_154102 : Nat := 4983230072969 + 3 ^ 40 * 154102 * 2
def baseEnd_154102 : Nat := 23445450613114461901127

theorem tailTrace_154102 : CollatzResearch.WordTrace tailWord_154102 prefixEnd_154102 23445450613114461901127 := by
  unfold tailWord_154102
  simp only [CollatzResearch.WordTrace]
  refine ⟨351285105482640460711535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3747041125148164914256373 351285105482640460711535)
  ·
    refine ⟨526927658223960691067303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 351285105482640460711535 526927658223960691067303)
    ·
      refine ⟨790391487335941036600955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 526927658223960691067303 790391487335941036600955)
      ·
        refine ⟨1185587231003911554901433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 790391487335941036600955 1185587231003911554901433)
        ·
          refine ⟨889190423252933666176075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1185587231003911554901433 889190423252933666176075)
          ·
            refine ⟨1333785634879400499264113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889190423252933666176075 1333785634879400499264113)
            ·
              refine ⟨1000339226159550374448085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1333785634879400499264113 1000339226159550374448085)
              ·
                refine ⟨23445450613114461901127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1000339226159550374448085 23445450613114461901127)
                ·
                  rfl

theorem cell20_154102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_154102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154102 prefixEnd_154102 := by exact prefixLift 154102
  have htrace : WordTrace (prefixWord ++ tailWord_154102) baseStart_154102 baseEnd_154102 := by
    simpa [prefixWord, tailWord_154102, baseEnd_154102] using wordTrace_append hprefix tailTrace_154102
  have hstable : (prefixWord ++ tailWord_154102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154102).length < 2 ^ (prefixWord ++ tailWord_154102).sum := by decide
  have hdescent : baseEnd_154102 < baseStart_154102 := by decide
  rcases family_descends (prefixWord ++ tailWord_154102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154125 : List Nat := [1, 7, 1, 1, 1, 3, 1, 3, 2]
def baseStart_154125 : Nat := 118140960795 + 154125 * 2 ^ 59
def prefixEnd_154125 : Nat := 4983230072969 + 3 ^ 40 * 154125 * 2
def baseEnd_154125 : Nat := 70346849666057527936621

theorem tailTrace_154125 : CollatzResearch.WordTrace tailWord_154125 prefixEnd_154125 70346849666057527936621 := by
  unfold tailWord_154125
  simp only [CollatzResearch.WordTrace]
  refine ⟨5621400566638922299471829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3747600377759281532981219 5621400566638922299471829)
  ·
    refine ⟨131751575780599741393871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 5621400566638922299471829 131751575780599741393871)
    ·
      refine ⟨197627363670899612090807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131751575780599741393871 197627363670899612090807)
      ·
        refine ⟨296441045506349418136211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197627363670899612090807 296441045506349418136211)
        ·
          refine ⟨444661568259524127204317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296441045506349418136211 444661568259524127204317)
          ·
            refine ⟨166748088097321547701619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 444661568259524127204317 166748088097321547701619)
            ·
              refine ⟨250122132145982321552429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166748088097321547701619 250122132145982321552429)
              ·
                refine ⟨93795799554743370582161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 250122132145982321552429 93795799554743370582161)
                ·
                  refine ⟨70346849666057527936621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93795799554743370582161 70346849666057527936621)
                  ·
                    rfl

theorem cell20_154125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_154125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154125 prefixEnd_154125 := by exact prefixLift 154125
  have htrace : WordTrace (prefixWord ++ tailWord_154125) baseStart_154125 baseEnd_154125 := by
    simpa [prefixWord, tailWord_154125, baseEnd_154125] using wordTrace_append hprefix tailTrace_154125
  have hstable : (prefixWord ++ tailWord_154125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154125).length < 2 ^ (prefixWord ++ tailWord_154125).sum := by decide
  have hdescent : baseEnd_154125 < baseStart_154125 := by decide
  rcases family_descends (prefixWord ++ tailWord_154125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154140 : List Nat := [2, 2, 3, 1, 2, 4, 6]
def baseStart_154140 : Nat := 118140960795 + 154140 * 2 ^ 59
def prefixEnd_154140 : Nat := 4983230072969 + 3 ^ 40 * 154140 * 2
def baseEnd_154140 : Nat := 7817077341642682492951

theorem tailTrace_154140 : CollatzResearch.WordTrace tailWord_154140 prefixEnd_154140 7817077341642682492951 := by
  unfold tailWord_154140
  simp only [CollatzResearch.WordTrace]
  refine ⟨2810973830792289930633937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3747965107723053240845249 2810973830792289930633937)
  ·
    refine ⟨2108230373094217447975453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2810973830792289930633937 2108230373094217447975453)
    ·
      refine ⟨790586389910331542990795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2108230373094217447975453 790586389910331542990795)
      ·
        refine ⟨1185879584865497314486193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 790586389910331542990795 1185879584865497314486193)
        ·
          refine ⟨889409688649122985864645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1185879584865497314486193 889409688649122985864645)
          ·
            refine ⟨166764316621710559849621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 889409688649122985864645 166764316621710559849621)
            ·
              refine ⟨7817077341642682492951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 166764316621710559849621 7817077341642682492951)
              ·
                rfl

theorem cell20_154140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 6].length) (baseStart_154140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154140 prefixEnd_154140 := by exact prefixLift 154140
  have htrace : WordTrace (prefixWord ++ tailWord_154140) baseStart_154140 baseEnd_154140 := by
    simpa [prefixWord, tailWord_154140, baseEnd_154140] using wordTrace_append hprefix tailTrace_154140
  have hstable : (prefixWord ++ tailWord_154140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154140).length < 2 ^ (prefixWord ++ tailWord_154140).sum := by decide
  have hdescent : baseEnd_154140 < baseStart_154140 := by decide
  rcases family_descends (prefixWord ++ tailWord_154140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154147 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 5]
def baseStart_154147 : Nat := 118140960795 + 154147 * 2 ^ 59
def prefixEnd_154147 : Nat := 4983230072969 + 3 ^ 40 * 154147 * 2
def baseEnd_154147 : Nat := 70356891065523229203197

theorem tailTrace_154147 : CollatzResearch.WordTrace tailWord_154147 prefixEnd_154147 70356891065523229203197 := by
  unfold tailWord_154147
  simp only [CollatzResearch.WordTrace]
  refine ⟨5622202972559220056772695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3748135315039480037848463 5622202972559220056772695)
  ·
    refine ⟨8433304458838830085159043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5622202972559220056772695 8433304458838830085159043)
    ·
      refine ⟨12649956688258245127738565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8433304458838830085159043 12649956688258245127738565)
      ·
        refine ⟨2371866879048420961450981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12649956688258245127738565 2371866879048420961450981)
        ·
          refine ⟨444725039821578930272059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2371866879048420961450981 444725039821578930272059)
          ·
            refine ⟨667087559732368395408089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444725039821578930272059 667087559732368395408089)
            ·
              refine ⟨500315669799276296556067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 667087559732368395408089 500315669799276296556067)
              ·
                refine ⟨750473504698914444834101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 500315669799276296556067 750473504698914444834101)
                ·
                  refine ⟨70356891065523229203197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 750473504698914444834101 70356891065523229203197)
                  ·
                    rfl

theorem cell20_154147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 5].length) (baseStart_154147 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154147 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154147 prefixEnd_154147 := by exact prefixLift 154147
  have htrace : WordTrace (prefixWord ++ tailWord_154147) baseStart_154147 baseEnd_154147 := by
    simpa [prefixWord, tailWord_154147, baseEnd_154147] using wordTrace_append hprefix tailTrace_154147
  have hstable : (prefixWord ++ tailWord_154147).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154147).length < 2 ^ (prefixWord ++ tailWord_154147).sum := by decide
  have hdescent : baseEnd_154147 < baseStart_154147 := by decide
  rcases family_descends (prefixWord ++ tailWord_154147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154161 : List Nat := [1, 2, 2, 3, 1, 1, 3, 7]
def baseStart_154161 : Nat := 118140960795 + 154161 * 2 ^ 59
def prefixEnd_154161 : Nat := 4983230072969 + 3 ^ 40 * 154161 * 2
def baseEnd_154161 : Nat := 23454427015667134245491

theorem tailTrace_154161 : CollatzResearch.WordTrace tailWord_154161 prefixEnd_154161 23454427015667134245491 := by
  unfold tailWord_154161
  simp only [CollatzResearch.WordTrace]
  refine ⟨5622713594508500447782337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3748475729672333631854891 5622713594508500447782337)
  ·
    refine ⟨4217035195881375335836753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5622713594508500447782337 4217035195881375335836753)
    ·
      refine ⟨3162776396911031501877565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4217035195881375335836753 3162776396911031501877565)
      ·
        refine ⟨1186041148841636813204087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3162776396911031501877565 1186041148841636813204087)
        ·
          refine ⟨1779061723262455219806131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1186041148841636813204087 1779061723262455219806131)
          ·
            refine ⟨2668592584893682829709197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1779061723262455219806131 2668592584893682829709197)
            ·
              refine ⟨1000722219335131061140949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2668592584893682829709197 1000722219335131061140949)
              ·
                refine ⟨23454427015667134245491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1000722219335131061140949 23454427015667134245491)
                ·
                  rfl

theorem cell20_154161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 7].length) (baseStart_154161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154161 prefixEnd_154161 := by exact prefixLift 154161
  have htrace : WordTrace (prefixWord ++ tailWord_154161) baseStart_154161 baseEnd_154161 := by
    simpa [prefixWord, tailWord_154161, baseEnd_154161] using wordTrace_append hprefix tailTrace_154161
  have hstable : (prefixWord ++ tailWord_154161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154161).length < 2 ^ (prefixWord ++ tailWord_154161).sum := by decide
  have hdescent : baseEnd_154161 < baseStart_154161 := by decide
  rcases family_descends (prefixWord ++ tailWord_154161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154223 : List Nat := [1, 1, 2, 1, 3, 2, 4, 3, 3]
def baseStart_154223 : Nat := 118140960795 + 154223 * 2 ^ 59
def prefixEnd_154223 : Nat := 4983230072969 + 3 ^ 40 * 154223 * 2
def baseEnd_154223 : Nat := 70391579536404742669553

theorem tailTrace_154223 : CollatzResearch.WordTrace tailWord_154223 prefixEnd_154223 70391579536404742669553 := by
  unfold tailWord_154223
  simp only [CollatzResearch.WordTrace]
  refine ⟨5624974920283885036539323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3749983280189256691026215 5624974920283885036539323)
  ·
    refine ⟨8437462380425827554808985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5624974920283885036539323 8437462380425827554808985)
    ·
      refine ⟨6328096785319370666106739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8437462380425827554808985 6328096785319370666106739)
      ·
        refine ⟨9492145177979055999160109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6328096785319370666106739 9492145177979055999160109)
        ·
          refine ⟨3559554441742145999685041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9492145177979055999160109 3559554441742145999685041)
          ·
            refine ⟨2669665831306609499763781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3559554441742145999685041 2669665831306609499763781)
            ·
              refine ⟨500562343369989281205709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2669665831306609499763781 500562343369989281205709)
              ·
                refine ⟨187710878763745980452141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 500562343369989281205709 187710878763745980452141)
                ·
                  refine ⟨70391579536404742669553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 187710878763745980452141 70391579536404742669553)
                  ·
                    rfl

theorem cell20_154223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 3].length) (baseStart_154223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154223 prefixEnd_154223 := by exact prefixLift 154223
  have htrace : WordTrace (prefixWord ++ tailWord_154223) baseStart_154223 baseEnd_154223 := by
    simpa [prefixWord, tailWord_154223, baseEnd_154223] using wordTrace_append hprefix tailTrace_154223
  have hstable : (prefixWord ++ tailWord_154223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154223).length < 2 ^ (prefixWord ++ tailWord_154223).sum := by decide
  have hdescent : baseEnd_154223 < baseStart_154223 := by decide
  rcases family_descends (prefixWord ++ tailWord_154223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154285 : List Nat := [1, 5, 2, 1, 1, 2, 2, 2, 4]
def baseStart_154285 : Nat := 118140960795 + 154285 * 2 ^ 59
def prefixEnd_154285 : Nat := 4983230072969 + 3 ^ 40 * 154285 * 2
def baseEnd_154285 : Nat := 70419878025808082602633

theorem tailTrace_154285 : CollatzResearch.WordTrace tailWord_154285 prefixEnd_154285 70419878025808082602633 := by
  unfold tailWord_154285
  simp only [CollatzResearch.WordTrace]
  refine ⟨5627236246059269625296309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3751490830706179750197539 5627236246059269625296309)
  ·
    refine ⟨527553398068056527371529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5627236246059269625296309 527553398068056527371529)
    ·
      refine ⟨395665048551042395528647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 527553398068056527371529 395665048551042395528647)
      ·
        refine ⟨593497572826563593292971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395665048551042395528647 593497572826563593292971)
        ·
          refine ⟨890246359239845389939457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 593497572826563593292971 890246359239845389939457)
          ·
            refine ⟨667684769429884042454593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 890246359239845389939457 667684769429884042454593)
            ·
              refine ⟨500763577072413031840945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 667684769429884042454593 500763577072413031840945)
              ·
                refine ⟨375572682804309773880709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 500763577072413031840945 375572682804309773880709)
                ·
                  refine ⟨70419878025808082602633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 375572682804309773880709 70419878025808082602633)
                  ·
                    rfl

theorem cell20_154285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_154285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154285 prefixEnd_154285 := by exact prefixLift 154285
  have htrace : WordTrace (prefixWord ++ tailWord_154285) baseStart_154285 baseEnd_154285 := by
    simpa [prefixWord, tailWord_154285, baseEnd_154285] using wordTrace_append hprefix tailTrace_154285
  have hstable : (prefixWord ++ tailWord_154285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154285).length < 2 ^ (prefixWord ++ tailWord_154285).sum := by decide
  have hdescent : baseEnd_154285 < baseStart_154285 := by decide
  rcases family_descends (prefixWord ++ tailWord_154285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154351 : List Nat := [1, 1, 2, 1, 5, 2, 2, 6]
def baseStart_154351 : Nat := 118140960795 + 154351 * 2 ^ 59
def prefixEnd_154351 : Nat := 4983230072969 + 3 ^ 40 * 154351 * 2
def baseEnd_154351 : Nat := 23483334074735062134121

theorem tailTrace_154351 : CollatzResearch.WordTrace tailWord_154351 prefixEnd_154351 23483334074735062134121 := by
  unfold tailWord_154351
  simp only [CollatzResearch.WordTrace]
  refine ⟨5629643463820162897198907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3753095642546775264799271 5629643463820162897198907)
  ·
    refine ⟨8444465195730244345798361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5629643463820162897198907 8444465195730244345798361)
    ·
      refine ⟨6333348896797683259348771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8444465195730244345798361 6333348896797683259348771)
      ·
        refine ⟨9500023345196524889023157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6333348896797683259348771 9500023345196524889023157)
        ·
          refine ⟨890627188612174208345921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9500023345196524889023157 890627188612174208345921)
          ·
            refine ⟨667970391459130656259441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 890627188612174208345921 667970391459130656259441)
            ·
              refine ⟨500977793594347992194581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 667970391459130656259441 500977793594347992194581)
              ·
                refine ⟨23483334074735062134121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 500977793594347992194581 23483334074735062134121)
                ·
                  rfl

theorem cell20_154351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 6].length) (baseStart_154351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154351 prefixEnd_154351 := by exact prefixLift 154351
  have htrace : WordTrace (prefixWord ++ tailWord_154351) baseStart_154351 baseEnd_154351 := by
    simpa [prefixWord, tailWord_154351, baseEnd_154351] using wordTrace_append hprefix tailTrace_154351
  have hstable : (prefixWord ++ tailWord_154351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154351).length < 2 ^ (prefixWord ++ tailWord_154351).sum := by decide
  have hdescent : baseEnd_154351 < baseStart_154351 := by decide
  rcases family_descends (prefixWord ++ tailWord_154351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154382 : List Nat := [4, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_154382 : Nat := 118140960795 + 154382 * 2 ^ 59
def prefixEnd_154382 : Nat := 4983230072969 + 3 ^ 40 * 154382 * 2
def baseEnd_154382 : Nat := 70464151468906856368903

theorem tailTrace_154382 : CollatzResearch.WordTrace tailWord_154382 prefixEnd_154382 70464151468906856368903 := by
  unfold tailWord_154382
  simp only [CollatzResearch.WordTrace]
  refine ⟨703846765838481898947175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3753849417805236794384933 703846765838481898947175)
  ·
    refine ⟨1055770148757722848420763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 703846765838481898947175 1055770148757722848420763)
    ·
      refine ⟨1583655223136584272631145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1055770148757722848420763 1583655223136584272631145)
      ·
        refine ⟨1187741417352438204473359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1583655223136584272631145 1187741417352438204473359)
        ·
          refine ⟨1781612126028657306710039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1187741417352438204473359 1781612126028657306710039)
          ·
            refine ⟨2672418189042985960065059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1781612126028657306710039 2672418189042985960065059)
            ·
              refine ⟨4008627283564478940097589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2672418189042985960065059 4008627283564478940097589)
              ·
                refine ⟨375808807834169900634149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4008627283564478940097589 375808807834169900634149)
                ·
                  refine ⟨70464151468906856368903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 375808807834169900634149 70464151468906856368903)
                  ·
                    rfl

theorem cell20_154382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_154382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154382 prefixEnd_154382 := by exact prefixLift 154382
  have htrace : WordTrace (prefixWord ++ tailWord_154382) baseStart_154382 baseEnd_154382 := by
    simpa [prefixWord, tailWord_154382, baseEnd_154382] using wordTrace_append hprefix tailTrace_154382
  have hstable : (prefixWord ++ tailWord_154382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154382).length < 2 ^ (prefixWord ++ tailWord_154382).sum := by decide
  have hdescent : baseEnd_154382 < baseStart_154382 := by decide
  rcases family_descends (prefixWord ++ tailWord_154382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154430 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 5]
def baseStart_154430 : Nat := 118140960795 + 154430 * 2 ^ 59
def prefixEnd_154430 : Nat := 4983230072969 + 3 ^ 40 * 154430 * 2
def baseEnd_154430 : Nat := 70486059976832022768707

theorem tailTrace_154430 : CollatzResearch.WordTrace tailWord_154430 prefixEnd_154430 70486059976832022768707 := by
  unfold tailWord_154430
  simp only [CollatzResearch.WordTrace]
  refine ⟨704065603816744923665593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3755016553689306259549829 704065603816744923665593)
  ·
    refine ⟨528049202862558692749195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 704065603816744923665593 528049202862558692749195)
    ·
      refine ⟨792073804293838039123793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 528049202862558692749195 792073804293838039123793)
      ·
        refine ⟨594055353220378529342845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 792073804293838039123793 594055353220378529342845)
        ·
          refine ⟨222770757457641948503567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 594055353220378529342845 222770757457641948503567)
          ·
            refine ⟨334156136186462922755351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222770757457641948503567 334156136186462922755351)
            ·
              refine ⟨501234204279694384133027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334156136186462922755351 501234204279694384133027)
              ·
                refine ⟨751851306419541576199541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 501234204279694384133027 751851306419541576199541)
                ·
                  refine ⟨70486059976832022768707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 751851306419541576199541 70486059976832022768707)
                  ·
                    rfl

theorem cell20_154430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_154430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154430 prefixEnd_154430 := by exact prefixLift 154430
  have htrace : WordTrace (prefixWord ++ tailWord_154430) baseStart_154430 baseEnd_154430 := by
    simpa [prefixWord, tailWord_154430, baseEnd_154430] using wordTrace_append hprefix tailTrace_154430
  have hstable : (prefixWord ++ tailWord_154430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154430).length < 2 ^ (prefixWord ++ tailWord_154430).sum := by decide
  have hdescent : baseEnd_154430 < baseStart_154430 := by decide
  rcases family_descends (prefixWord ++ tailWord_154430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154458 : List Nat := [3, 1, 1, 2, 1, 4, 2, 2, 4]
def baseStart_154458 : Nat := 118140960795 + 154458 * 2 ^ 59
def prefixEnd_154458 : Nat := 4983230072969 + 3 ^ 40 * 154458 * 2
def baseEnd_154458 : Nat := 70498839939788369835259

theorem tailTrace_154458 : CollatzResearch.WordTrace tailWord_154458 prefixEnd_154458 70498839939788369835259 := by
  unfold tailWord_154458
  simp only [CollatzResearch.WordTrace]
  refine ⟨1408386518608130042836007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3755697382955013447562685 1408386518608130042836007)
  ·
    refine ⟨2112579777912195064254011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1408386518608130042836007 2112579777912195064254011)
    ·
      refine ⟨3168869666868292596381017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2112579777912195064254011 3168869666868292596381017)
      ·
        refine ⟨2376652250151219447285763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3168869666868292596381017 2376652250151219447285763)
        ·
          refine ⟨3564978375226829170928645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2376652250151219447285763 3564978375226829170928645)
          ·
            refine ⟨668433445355030469549121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3564978375226829170928645 668433445355030469549121)
            ·
              refine ⟨501325084016272852161841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 668433445355030469549121 501325084016272852161841)
              ·
                refine ⟨375993813012204639121381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 501325084016272852161841 375993813012204639121381)
                ·
                  refine ⟨70498839939788369835259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 375993813012204639121381 70498839939788369835259)
                  ·
                    rfl

theorem cell20_154458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_154458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154458 prefixEnd_154458 := by exact prefixLift 154458
  have htrace : WordTrace (prefixWord ++ tailWord_154458) baseStart_154458 baseEnd_154458 := by
    simpa [prefixWord, tailWord_154458, baseEnd_154458] using wordTrace_append hprefix tailTrace_154458
  have hstable : (prefixWord ++ tailWord_154458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154458).length < 2 ^ (prefixWord ++ tailWord_154458).sum := by decide
  have hdescent : baseEnd_154458 < baseStart_154458 := by decide
  rcases family_descends (prefixWord ++ tailWord_154458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154475 : List Nat := [1, 1, 1, 1, 2, 2, 7, 3, 2]
def baseStart_154475 : Nat := 118140960795 + 154475 * 2 ^ 59
def prefixEnd_154475 : Nat := 4983230072969 + 3 ^ 40 * 154475 * 2
def baseEnd_154475 : Nat := 70506599203011866268523

theorem tailTrace_154475 : CollatzResearch.WordTrace tailWord_154475 prefixEnd_154475 70506599203011866268523 := by
  unfold tailWord_154475
  simp only [CollatzResearch.WordTrace]
  refine ⟨5634166115370932074712879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3756110743580621383141919 5634166115370932074712879)
  ·
    refine ⟨8451249173056398112069319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5634166115370932074712879 8451249173056398112069319)
    ·
      refine ⟨12676873759584597168103979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8451249173056398112069319 12676873759584597168103979)
      ·
        refine ⟨19015310639376895752155969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12676873759584597168103979 19015310639376895752155969)
        ·
          refine ⟨14261482979532671814116977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19015310639376895752155969 14261482979532671814116977)
          ·
            refine ⟨10696112234649503860587733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14261482979532671814116977 10696112234649503860587733)
            ·
              refine ⟨250690130499597746732525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10696112234649503860587733 250690130499597746732525)
              ·
                refine ⟨94008798937349155024697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 250690130499597746732525 94008798937349155024697)
                ·
                  refine ⟨70506599203011866268523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94008798937349155024697 70506599203011866268523)
                  ·
                    rfl

theorem cell20_154475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 2].length) (baseStart_154475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154475 prefixEnd_154475 := by exact prefixLift 154475
  have htrace : WordTrace (prefixWord ++ tailWord_154475) baseStart_154475 baseEnd_154475 := by
    simpa [prefixWord, tailWord_154475, baseEnd_154475] using wordTrace_append hprefix tailTrace_154475
  have hstable : (prefixWord ++ tailWord_154475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154475).length < 2 ^ (prefixWord ++ tailWord_154475).sum := by decide
  have hdescent : baseEnd_154475 < baseStart_154475 := by decide
  rcases family_descends (prefixWord ++ tailWord_154475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154479 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 6]
def baseStart_154479 : Nat := 118140960795 + 154479 * 2 ^ 59
def prefixEnd_154479 : Nat := 4983230072969 + 3 ^ 40 * 154479 * 2
def baseEnd_154479 : Nat := 70508424912005630135173

theorem tailTrace_154479 : CollatzResearch.WordTrace tailWord_154479 prefixEnd_154479 70508424912005630135173 := by
  unfold tailWord_154479
  simp only [CollatzResearch.WordTrace]
  refine ⟨5634312007356440757858491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3756208004904293838572327 5634312007356440757858491)
  ·
    refine ⟨8451468011034661136787737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5634312007356440757858491 8451468011034661136787737)
    ·
      refine ⟨6338601008275995852590803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8451468011034661136787737 6338601008275995852590803)
      ·
        refine ⟨9507901512413993778886205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6338601008275995852590803 9507901512413993778886205)
        ·
          refine ⟨3565463067155247667082327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9507901512413993778886205 3565463067155247667082327)
          ·
            refine ⟨5348194600732871500623491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3565463067155247667082327 5348194600732871500623491)
            ·
              refine ⟨8022291901099307250935237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5348194600732871500623491 8022291901099307250935237)
              ·
                refine ⟨1504179731456120109550357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8022291901099307250935237 1504179731456120109550357)
                ·
                  refine ⟨70508424912005630135173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1504179731456120109550357 70508424912005630135173)
                  ·
                    rfl

theorem cell20_154479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_154479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154479 prefixEnd_154479 := by exact prefixLift 154479
  have htrace : WordTrace (prefixWord ++ tailWord_154479) baseStart_154479 baseEnd_154479 := by
    simpa [prefixWord, tailWord_154479, baseEnd_154479] using wordTrace_append hprefix tailTrace_154479
  have hstable : (prefixWord ++ tailWord_154479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154479).length < 2 ^ (prefixWord ++ tailWord_154479).sum := by decide
  have hdescent : baseEnd_154479 < baseStart_154479 := by decide
  rcases family_descends (prefixWord ++ tailWord_154479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154498 : List Nat := [3, 4, 2, 2, 2, 1, 2, 1, 3]
def baseStart_154498 : Nat := 118140960795 + 154498 * 2 ^ 59
def prefixEnd_154498 : Nat := 4983230072969 + 3 ^ 40 * 154498 * 2
def baseEnd_154498 : Nat := 70517097029726008501763

theorem tailTrace_154498 : CollatzResearch.WordTrace tailWord_154498 prefixEnd_154498 70517097029726008501763 := by
  unfold tailWord_154498
  simp only [CollatzResearch.WordTrace]
  refine ⟨1408751248571901750700037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3756669996191738001866765 1408751248571901750700037)
  ·
    refine ⟨264140859107231578256257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1408751248571901750700037 264140859107231578256257)
    ·
      refine ⟨198105644330423683692193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264140859107231578256257 198105644330423683692193)
      ·
        refine ⟨148579233247817762769145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198105644330423683692193 148579233247817762769145)
        ·
          refine ⟨111434424935863322076859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148579233247817762769145 111434424935863322076859)
          ·
            refine ⟨167151637403794983115289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111434424935863322076859 167151637403794983115289)
            ·
              refine ⟨125363728052846237336467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167151637403794983115289 125363728052846237336467)
              ·
                refine ⟨188045592079269356004701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125363728052846237336467 188045592079269356004701)
                ·
                  refine ⟨70517097029726008501763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188045592079269356004701 70517097029726008501763)
                  ·
                    rfl

theorem cell20_154498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_154498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154498 prefixEnd_154498 := by exact prefixLift 154498
  have htrace : WordTrace (prefixWord ++ tailWord_154498) baseStart_154498 baseEnd_154498 := by
    simpa [prefixWord, tailWord_154498, baseEnd_154498] using wordTrace_append hprefix tailTrace_154498
  have hstable : (prefixWord ++ tailWord_154498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154498).length < 2 ^ (prefixWord ++ tailWord_154498).sum := by decide
  have hdescent : baseEnd_154498 < baseStart_154498 := by decide
  rcases family_descends (prefixWord ++ tailWord_154498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154503 : List Nat := [1, 1, 4, 2, 3, 1, 1, 7]
def baseStart_154503 : Nat := 118140960795 + 154503 * 2 ^ 59
def prefixEnd_154503 : Nat := 4983230072969 + 3 ^ 40 * 154503 * 2
def baseEnd_154503 : Nat := 23506459721989404445025

theorem tailTrace_154503 : CollatzResearch.WordTrace tailWord_154503 prefixEnd_154503 23506459721989404445025 := by
  unfold tailWord_154503
  simp only [CollatzResearch.WordTrace]
  refine ⟨5635187359269492856732163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3756791572846328571154775 5635187359269492856732163)
  ·
    refine ⟨8452781038904239285098245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5635187359269492856732163 8452781038904239285098245)
    ·
      refine ⟨1584896444794544865955921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8452781038904239285098245 1584896444794544865955921)
      ·
        refine ⟨1188672333595908649466941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1584896444794544865955921 1188672333595908649466941)
        ·
          refine ⟨445752125098465743550103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1188672333595908649466941 445752125098465743550103)
          ·
            refine ⟨668628187647698615325155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445752125098465743550103 668628187647698615325155)
            ·
              refine ⟨1002942281471547922987733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 668628187647698615325155 1002942281471547922987733)
              ·
                refine ⟨23506459721989404445025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1002942281471547922987733 23506459721989404445025)
                ·
                  rfl

theorem cell20_154503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 7].length) (baseStart_154503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154503 prefixEnd_154503 := by exact prefixLift 154503
  have htrace : WordTrace (prefixWord ++ tailWord_154503) baseStart_154503 baseEnd_154503 := by
    simpa [prefixWord, tailWord_154503, baseEnd_154503] using wordTrace_append hprefix tailTrace_154503
  have hstable : (prefixWord ++ tailWord_154503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154503).length < 2 ^ (prefixWord ++ tailWord_154503).sum := by decide
  have hdescent : baseEnd_154503 < baseStart_154503 := by decide
  rcases family_descends (prefixWord ++ tailWord_154503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154506 : List Nat := [3, 1, 2, 4, 1, 2, 1, 3, 3]
def baseStart_154506 : Nat := 118140960795 + 154506 * 2 ^ 59
def prefixEnd_154506 : Nat := 4983230072969 + 3 ^ 40 * 154506 * 2
def baseEnd_154506 : Nat := 70520748447713536235063

theorem tailTrace_154506 : CollatzResearch.WordTrace tailWord_154506 prefixEnd_154506 70520748447713536235063 := by
  unfold tailWord_154506
  simp only [CollatzResearch.WordTrace]
  refine ⟨1408824194564656092272843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3756864518839082912727581 1408824194564656092272843)
  ·
    refine ⟨2113236291846984138409265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1408824194564656092272843 2113236291846984138409265)
    ·
      refine ⟨1584927218885238103806949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2113236291846984138409265 1584927218885238103806949)
      ·
        refine ⟨297173853540982144463803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1584927218885238103806949 297173853540982144463803)
        ·
          refine ⟨445760780311473216695705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297173853540982144463803 445760780311473216695705)
          ·
            refine ⟨334320585233604912521779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 445760780311473216695705 334320585233604912521779)
            ·
              refine ⟨501480877850407368782669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334320585233604912521779 501480877850407368782669)
              ·
                refine ⟨188055329193902763293501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 501480877850407368782669 188055329193902763293501)
                ·
                  refine ⟨70520748447713536235063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188055329193902763293501 70520748447713536235063)
                  ·
                    rfl

theorem cell20_154506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_154506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154506 prefixEnd_154506 := by exact prefixLift 154506
  have htrace : WordTrace (prefixWord ++ tailWord_154506) baseStart_154506 baseEnd_154506 := by
    simpa [prefixWord, tailWord_154506, baseEnd_154506] using wordTrace_append hprefix tailTrace_154506
  have hstable : (prefixWord ++ tailWord_154506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154506).length < 2 ^ (prefixWord ++ tailWord_154506).sum := by decide
  have hdescent : baseEnd_154506 < baseStart_154506 := by decide
  rcases family_descends (prefixWord ++ tailWord_154506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154550 : List Nat := [5, 1, 4, 1, 2, 1, 1, 5]
def baseStart_154550 : Nat := 118140960795 + 154550 * 2 ^ 59
def prefixEnd_154550 : Nat := 4983230072969 + 3 ^ 40 * 154550 * 2
def baseEnd_154550 : Nat := 23513610415548312922739

theorem tailTrace_154550 : CollatzResearch.WordTrace tailWord_154550 prefixEnd_154550 23513610415548312922739 := by
  unfold tailWord_154550
  simp only [CollatzResearch.WordTrace]
  refine ⟨352306349381201242730819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3757934393399479922462069 352306349381201242730819)
  ·
    refine ⟨528459524071801864096229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 352306349381201242730819 528459524071801864096229)
    ·
      refine ⟨99086160763462849518043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 528459524071801864096229 99086160763462849518043)
      ·
        refine ⟨148629241145194274277065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99086160763462849518043 148629241145194274277065)
        ·
          refine ⟨111471930858895705707799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148629241145194274277065 111471930858895705707799)
          ·
            refine ⟨167207896288343558561699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111471930858895705707799 167207896288343558561699)
            ·
              refine ⟨250811844432515337842549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167207896288343558561699 250811844432515337842549)
              ·
                refine ⟨23513610415548312922739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 250811844432515337842549 23513610415548312922739)
                ·
                  rfl

theorem cell20_154550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_154550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154550 prefixEnd_154550 := by exact prefixLift 154550
  have htrace : WordTrace (prefixWord ++ tailWord_154550) baseStart_154550 baseEnd_154550 := by
    simpa [prefixWord, tailWord_154550, baseEnd_154550] using wordTrace_append hprefix tailTrace_154550
  have hstable : (prefixWord ++ tailWord_154550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154550).length < 2 ^ (prefixWord ++ tailWord_154550).sum := by decide
  have hdescent : baseEnd_154550 < baseStart_154550 := by decide
  rcases family_descends (prefixWord ++ tailWord_154550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154572 : List Nat := [2, 2, 1, 4, 1, 1, 3, 2, 4]
def baseStart_154572 : Nat := 118140960795 + 154572 * 2 ^ 59
def prefixEnd_154572 : Nat := 4983230072969 + 3 ^ 40 * 154572 * 2
def baseEnd_154572 : Nat := 70550872646110640034793

theorem tailTrace_154572 : CollatzResearch.WordTrace tailWord_154572 prefixEnd_154572 70550872646110640034793 := by
  unfold tailWord_154572
  simp only [CollatzResearch.WordTrace]
  refine ⟨2818851998009758820496985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3758469330679678427329313 2818851998009758820496985)
  ·
    refine ⟨2114138998507319115372739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2818851998009758820496985 2114138998507319115372739)
    ·
      refine ⟨3171208497760978673059109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2114138998507319115372739 3171208497760978673059109)
      ·
        refine ⟨594601593330183501198583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3171208497760978673059109 594601593330183501198583)
        ·
          refine ⟨891902389995275251797875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 594601593330183501198583 891902389995275251797875)
          ·
            refine ⟨1337853584992912877696813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 891902389995275251797875 1337853584992912877696813)
            ·
              refine ⟨501695094372342329136305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1337853584992912877696813 501695094372342329136305)
              ·
                refine ⟨376271320779256746852229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 501695094372342329136305 376271320779256746852229)
                ·
                  refine ⟨70550872646110640034793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 376271320779256746852229 70550872646110640034793)
                  ·
                    rfl

theorem cell20_154572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_154572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154572 prefixEnd_154572 := by exact prefixLift 154572
  have htrace : WordTrace (prefixWord ++ tailWord_154572) baseStart_154572 baseEnd_154572 := by
    simpa [prefixWord, tailWord_154572, baseEnd_154572] using wordTrace_append hprefix tailTrace_154572
  have hstable : (prefixWord ++ tailWord_154572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154572).length < 2 ^ (prefixWord ++ tailWord_154572).sum := by decide
  have hdescent : baseEnd_154572 < baseStart_154572 := by decide
  rcases family_descends (prefixWord ++ tailWord_154572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154593 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 8]
def baseStart_154593 : Nat := 118140960795 + 154593 * 2 ^ 59
def prefixEnd_154593 : Nat := 4983230072969 + 3 ^ 40 * 154593 * 2
def baseEnd_154593 : Nat := 70560457618327900334707

theorem tailTrace_154593 : CollatzResearch.WordTrace tailWord_154593 prefixEnd_154593 70560457618327900334707 := by
  unfold tailWord_154593
  simp only [CollatzResearch.WordTrace]
  refine ⟨5638469928943438227508433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3758979952628958818338955 5638469928943438227508433)
  ·
    refine ⟨4228852446707578670631325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5638469928943438227508433 4228852446707578670631325)
    ·
      refine ⟨1585819667515342001486747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4228852446707578670631325 1585819667515342001486747)
      ·
        refine ⟨2378729501273013002230121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1585819667515342001486747 2378729501273013002230121)
        ·
          refine ⟨1784047125954759751672591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2378729501273013002230121 1784047125954759751672591)
          ·
            refine ⟨2676070688932139627508887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1784047125954759751672591 2676070688932139627508887)
            ·
              refine ⟨4014106033398209441263331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2676070688932139627508887 4014106033398209441263331)
              ·
                refine ⟨6021159050097314161894997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4014106033398209441263331 6021159050097314161894997)
                ·
                  refine ⟨70560457618327900334707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6021159050097314161894997 70560457618327900334707)
                  ·
                    rfl

theorem cell20_154593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_154593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154593 prefixEnd_154593 := by exact prefixLift 154593
  have htrace : WordTrace (prefixWord ++ tailWord_154593) baseStart_154593 baseEnd_154593 := by
    simpa [prefixWord, tailWord_154593, baseEnd_154593] using wordTrace_append hprefix tailTrace_154593
  have hstable : (prefixWord ++ tailWord_154593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154593).length < 2 ^ (prefixWord ++ tailWord_154593).sum := by decide
  have hdescent : baseEnd_154593 < baseStart_154593 := by decide
  rcases family_descends (prefixWord ++ tailWord_154593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154612 : List Nat := [2, 6, 2, 1, 1, 1, 3, 1, 3]
def baseStart_154612 : Nat := 118140960795 + 154612 * 2 ^ 59
def prefixEnd_154612 : Nat := 4983230072969 + 3 ^ 40 * 154612 * 2
def baseEnd_154612 : Nat := 70569129736048278701297

theorem tailTrace_154612 : CollatzResearch.WordTrace tailWord_154612 prefixEnd_154612 70569129736048278701297 := by
  unfold tailWord_154612
  simp only [CollatzResearch.WordTrace]
  refine ⟨2819581457937302236225045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3759441943916402981633393 2819581457937302236225045)
  ·
    refine ⟨132167880840811042323049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2819581457937302236225045 132167880840811042323049)
    ·
      refine ⟨99125910630608281742287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132167880840811042323049 99125910630608281742287)
      ·
        refine ⟨148688865945912422613431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99125910630608281742287 148688865945912422613431)
        ·
          refine ⟨223033298918868633920147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148688865945912422613431 223033298918868633920147)
          ·
            refine ⟨334549948378302950880221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223033298918868633920147 334549948378302950880221)
            ·
              refine ⟨125456230641863606580083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 334549948378302950880221 125456230641863606580083)
              ·
                refine ⟨188184345962795409870125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125456230641863606580083 188184345962795409870125)
                ·
                  refine ⟨70569129736048278701297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188184345962795409870125 70569129736048278701297)
                  ·
                    rfl

theorem cell20_154612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_154612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154612 prefixEnd_154612 := by exact prefixLift 154612
  have htrace : WordTrace (prefixWord ++ tailWord_154612) baseStart_154612 baseEnd_154612 := by
    simpa [prefixWord, tailWord_154612, baseEnd_154612] using wordTrace_append hprefix tailTrace_154612
  have hstable : (prefixWord ++ tailWord_154612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154612).length < 2 ^ (prefixWord ++ tailWord_154612).sum := by decide
  have hdescent : baseEnd_154612 < baseStart_154612 := by decide
  rcases family_descends (prefixWord ++ tailWord_154612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154620 : List Nat := [2, 2, 2, 1, 2, 4, 3, 1, 3]
def baseStart_154620 : Nat := 118140960795 + 154620 * 2 ^ 59
def prefixEnd_154620 : Nat := 4983230072969 + 3 ^ 40 * 154620 * 2
def baseEnd_154620 : Nat := 70572781154035806434597

theorem tailTrace_154620 : CollatzResearch.WordTrace tailWord_154620 prefixEnd_154620 70572781154035806434597 := by
  unfold tailWord_154620
  simp only [CollatzResearch.WordTrace]
  refine ⟨2819727349922810919370657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3759636466563747892494209 2819727349922810919370657)
  ·
    refine ⟨2114795512442108189527993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2819727349922810919370657 2114795512442108189527993)
    ·
      refine ⟨1586096634331581142145995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2114795512442108189527993 1586096634331581142145995)
      ·
        refine ⟨2379144951497371713218993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1586096634331581142145995 2379144951497371713218993)
        ·
          refine ⟨1784358713623028784914245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2379144951497371713218993 1784358713623028784914245)
          ·
            refine ⟨334567258804317897171421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1784358713623028784914245 334567258804317897171421)
            ·
              refine ⟨125462722051619211439283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 334567258804317897171421 125462722051619211439283)
              ·
                refine ⟨188194083077428817158925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125462722051619211439283 188194083077428817158925)
                ·
                  refine ⟨70572781154035806434597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188194083077428817158925 70572781154035806434597)
                  ·
                    rfl

theorem cell20_154620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_154620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154620 prefixEnd_154620 := by exact prefixLift 154620
  have htrace : WordTrace (prefixWord ++ tailWord_154620) baseStart_154620 baseEnd_154620 := by
    simpa [prefixWord, tailWord_154620, baseEnd_154620] using wordTrace_append hprefix tailTrace_154620
  have hstable : (prefixWord ++ tailWord_154620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154620).length < 2 ^ (prefixWord ++ tailWord_154620).sum := by decide
  have hdescent : baseEnd_154620 < baseStart_154620 := by decide
  rcases family_descends (prefixWord ++ tailWord_154620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154634 : List Nat := [3, 1, 2, 2, 3, 1, 4, 4]
def baseStart_154634 : Nat := 118140960795 + 154634 * 2 ^ 59
def prefixEnd_154634 : Nat := 4983230072969 + 3 ^ 40 * 154634 * 2
def baseEnd_154634 : Nat := 23526390378504659989291

theorem tailTrace_154634 : CollatzResearch.WordTrace tailWord_154634 prefixEnd_154634 23526390378504659989291 := by
  unfold tailWord_154634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1409991330448725557437739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3759976881196601486500637 1409991330448725557437739)
  ·
    refine ⟨2114986995673088336156609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1409991330448725557437739 2114986995673088336156609)
    ·
      refine ⟨1586240246754816252117457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2114986995673088336156609 1586240246754816252117457)
      ·
        refine ⟨1189680185066112189088093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1586240246754816252117457 1189680185066112189088093)
        ·
          refine ⟨446130069399792070908035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1189680185066112189088093 446130069399792070908035)
          ·
            refine ⟨669195104099688106362053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446130069399792070908035 669195104099688106362053)
            ·
              refine ⟨125474082018691519942885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 669195104099688106362053 125474082018691519942885)
              ·
                refine ⟨23526390378504659989291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125474082018691519942885 23526390378504659989291)
                ·
                  rfl

theorem cell20_154634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_154634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154634 prefixEnd_154634 := by exact prefixLift 154634
  have htrace : WordTrace (prefixWord ++ tailWord_154634) baseStart_154634 baseEnd_154634 := by
    simpa [prefixWord, tailWord_154634, baseEnd_154634] using wordTrace_append hprefix tailTrace_154634
  have hstable : (prefixWord ++ tailWord_154634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154634).length < 2 ^ (prefixWord ++ tailWord_154634).sum := by decide
  have hdescent : baseEnd_154634 < baseStart_154634 := by decide
  rcases family_descends (prefixWord ++ tailWord_154634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154655 : List Nat := [1, 1, 2, 4, 1, 5, 6]
def baseStart_154655 : Nat := 118140960795 + 154655 * 2 ^ 59
def prefixEnd_154655 : Nat := 4983230072969 + 3 ^ 40 * 154655 * 2
def baseEnd_154655 : Nat := 7843195123081248918643

theorem tailTrace_154655 : CollatzResearch.WordTrace tailWord_154655 prefixEnd_154655 7843195123081248918643 := by
  unfold tailWord_154655
  simp only [CollatzResearch.WordTrace]
  refine ⟨5640731254718822816265419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3760487503145881877510279 5640731254718822816265419)
  ·
    refine ⟨8461096882078234224398129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5640731254718822816265419 8461096882078234224398129)
    ·
      refine ⟨6345822661558675668298597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8461096882078234224398129 6345822661558675668298597)
      ·
        refine ⟨1189841749042251687805987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6345822661558675668298597 1189841749042251687805987)
        ·
          refine ⟨1784762623563377531708981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1189841749042251687805987 1784762623563377531708981)
          ·
            refine ⟨167321495959066643597717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1784762623563377531708981 167321495959066643597717)
            ·
              refine ⟨7843195123081248918643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 167321495959066643597717 7843195123081248918643)
              ·
                rfl

theorem cell20_154655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 6].length) (baseStart_154655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154655 prefixEnd_154655 := by exact prefixLift 154655
  have htrace : WordTrace (prefixWord ++ tailWord_154655) baseStart_154655 baseEnd_154655 := by
    simpa [prefixWord, tailWord_154655, baseEnd_154655] using wordTrace_append hprefix tailTrace_154655
  have hstable : (prefixWord ++ tailWord_154655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154655).length < 2 ^ (prefixWord ++ tailWord_154655).sum := by decide
  have hdescent : baseEnd_154655 < baseStart_154655 := by decide
  rcases family_descends (prefixWord ++ tailWord_154655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154710 : List Nat := [5, 2, 2, 1, 10]
def baseStart_154710 : Nat := 118140960795 + 154710 * 2 ^ 59
def prefixEnd_154710 : Nat := 4983230072969 + 3 ^ 40 * 154710 * 2
def baseEnd_154710 : Nat := 871776044523401153509

theorem tailTrace_154710 : CollatzResearch.WordTrace tailWord_154710 prefixEnd_154710 871776044523401153509 := by
  unfold tailWord_154710
  simp only [CollatzResearch.WordTrace]
  refine ⟨352671079344972950594849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3761824846346378139678389 352671079344972950594849)
  ·
    refine ⟨264503309508729712946137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 352671079344972950594849 264503309508729712946137)
    ·
      refine ⟨198377482131547284709603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264503309508729712946137 198377482131547284709603)
      ·
        refine ⟨297566223197320927064405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198377482131547284709603 297566223197320927064405)
        ·
          refine ⟨871776044523401153509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 297566223197320927064405 871776044523401153509)
          ·
            rfl

theorem cell20_154710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 10].length) (baseStart_154710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154710 prefixEnd_154710 := by exact prefixLift 154710
  have htrace : WordTrace (prefixWord ++ tailWord_154710) baseStart_154710 baseEnd_154710 := by
    simpa [prefixWord, tailWord_154710, baseEnd_154710] using wordTrace_append hprefix tailTrace_154710
  have hstable : (prefixWord ++ tailWord_154710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154710).length < 2 ^ (prefixWord ++ tailWord_154710).sum := by decide
  have hdescent : baseEnd_154710 < baseStart_154710 := by decide
  rcases family_descends (prefixWord ++ tailWord_154710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154752 : List Nat := [2, 1, 1, 2, 1, 3, 2, 8]
def baseStart_154752 : Nat := 118140960795 + 154752 * 2 ^ 59
def prefixEnd_154752 : Nat := 4983230072969 + 3 ^ 40 * 154752 * 2
def baseEnd_154752 : Nat := 23544343183610004678019

theorem tailTrace_154752 : CollatzResearch.WordTrace tailWord_154752 prefixEnd_154752 23544343183610004678019 := by
  unfold tailWord_154752
  simp only [CollatzResearch.WordTrace]
  refine ⟨2822134567683704191273255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3762846090244938921697673 2822134567683704191273255)
  ·
    refine ⟨4233201851525556286909883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2822134567683704191273255 4233201851525556286909883)
    ·
      refine ⟨6349802777288334430364825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4233201851525556286909883 6349802777288334430364825)
      ·
        refine ⟨4762352082966250822773619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6349802777288334430364825 4762352082966250822773619)
        ·
          refine ⟨7143528124449376234160429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4762352082966250822773619 7143528124449376234160429)
          ·
            refine ⟨2678823046668516087810161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7143528124449376234160429 2678823046668516087810161)
            ·
              refine ⟨2009117285001387065857621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2678823046668516087810161 2009117285001387065857621)
              ·
                refine ⟨23544343183610004678019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2009117285001387065857621 23544343183610004678019)
                ·
                  rfl

theorem cell20_154752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_154752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154752 prefixEnd_154752 := by exact prefixLift 154752
  have htrace : WordTrace (prefixWord ++ tailWord_154752) baseStart_154752 baseEnd_154752 := by
    simpa [prefixWord, tailWord_154752, baseEnd_154752] using wordTrace_append hprefix tailTrace_154752
  have hstable : (prefixWord ++ tailWord_154752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154752).length < 2 ^ (prefixWord ++ tailWord_154752).sum := by decide
  have hdescent : baseEnd_154752 < baseStart_154752 := by decide
  rcases family_descends (prefixWord ++ tailWord_154752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154834 : List Nat := [3, 2, 2, 2, 1, 1, 5, 2, 2]
def baseStart_154834 : Nat := 118140960795 + 154834 * 2 ^ 59
def prefixEnd_154834 : Nat := 4983230072969 + 3 ^ 40 * 154834 * 2
def baseEnd_154834 : Nat := 70670456585202173300389

theorem tailTrace_154834 : CollatzResearch.WordTrace tailWord_154834 prefixEnd_154834 70670456585202173300389 := by
  unfold tailWord_154834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1411814980267584096757889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3764839947380224258021037 1411814980267584096757889)
  ·
    refine ⟨1058861235200688072568417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1411814980267584096757889 1058861235200688072568417)
    ·
      refine ⟨794145926400516054426313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1058861235200688072568417 794145926400516054426313)
      ·
        refine ⟨595609444800387040819735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 794145926400516054426313 595609444800387040819735)
        ·
          refine ⟨893414167200580561229603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 595609444800387040819735 893414167200580561229603)
          ·
            refine ⟨1340121250800870841844405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 893414167200580561229603 1340121250800870841844405)
            ·
              refine ⟨125636367262581641422913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1340121250800870841844405 125636367262581641422913)
              ·
                refine ⟨94227275446936231067185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125636367262581641422913 94227275446936231067185)
                ·
                  refine ⟨70670456585202173300389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94227275446936231067185 70670456585202173300389)
                  ·
                    rfl

theorem cell20_154834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_154834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154834 prefixEnd_154834 := by exact prefixLift 154834
  have htrace : WordTrace (prefixWord ++ tailWord_154834) baseStart_154834 baseEnd_154834 := by
    simpa [prefixWord, tailWord_154834, baseEnd_154834] using wordTrace_append hprefix tailTrace_154834
  have hstable : (prefixWord ++ tailWord_154834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154834).length < 2 ^ (prefixWord ++ tailWord_154834).sum := by decide
  have hdescent : baseEnd_154834 < baseStart_154834 := by decide
  rcases family_descends (prefixWord ++ tailWord_154834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154848 : List Nat := [2, 1, 1, 3, 1, 6, 2, 1, 3]
def baseStart_154848 : Nat := 118140960795 + 154848 * 2 ^ 59
def prefixEnd_154848 : Nat := 4983230072969 + 3 ^ 40 * 154848 * 2
def baseEnd_154848 : Nat := 70676846566680346833665

theorem tailTrace_154848 : CollatzResearch.WordTrace tailWord_154848 prefixEnd_154848 70676846566680346833665 := by
  unfold tailWord_154848
  simp only [CollatzResearch.WordTrace]
  refine ⟨2823885271509808389020599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3765180362013077852027465 2823885271509808389020599)
  ·
    refine ⟨4235827907264712583530899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2823885271509808389020599 4235827907264712583530899)
    ·
      refine ⟨6353741860897068875296349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4235827907264712583530899 6353741860897068875296349)
      ·
        refine ⟨2382653197836400828236131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6353741860897068875296349 2382653197836400828236131)
        ·
          refine ⟨3573979796754601242354197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2382653197836400828236131 3573979796754601242354197)
          ·
            refine ⟨167530302972871933235353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3573979796754601242354197 167530302972871933235353)
            ·
              refine ⟨125647727229653949926515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167530302972871933235353 125647727229653949926515)
              ·
                refine ⟨188471590844480924889773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125647727229653949926515 188471590844480924889773)
                ·
                  refine ⟨70676846566680346833665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188471590844480924889773 70676846566680346833665)
                  ·
                    rfl

theorem cell20_154848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 3].length) (baseStart_154848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154848 prefixEnd_154848 := by exact prefixLift 154848
  have htrace : WordTrace (prefixWord ++ tailWord_154848) baseStart_154848 baseEnd_154848 := by
    simpa [prefixWord, tailWord_154848, baseEnd_154848] using wordTrace_append hprefix tailTrace_154848
  have hstable : (prefixWord ++ tailWord_154848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154848).length < 2 ^ (prefixWord ++ tailWord_154848).sum := by decide
  have hdescent : baseEnd_154848 < baseStart_154848 := by decide
  rcases family_descends (prefixWord ++ tailWord_154848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154897 : List Nat := [1, 2, 2, 1, 1, 4, 2, 3, 4]
def baseStart_154897 : Nat := 118140960795 + 154897 * 2 ^ 59
def prefixEnd_154897 : Nat := 4983230072969 + 3 ^ 40 * 154897 * 2
def baseEnd_154897 : Nat := 70699211501853954200131

theorem tailTrace_154897 : CollatzResearch.WordTrace tailWord_154897 prefixEnd_154897 70699211501853954200131 := by
  unfold tailWord_154897
  simp only [CollatzResearch.WordTrace]
  refine ⟨5649557719842098146574945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3766371813228065431049963 5649557719842098146574945)
  ·
    refine ⟨4237168289881573609931209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5649557719842098146574945 4237168289881573609931209)
    ·
      refine ⟨3177876217411180207448407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4237168289881573609931209 3177876217411180207448407)
      ·
        refine ⟨4766814326116770311172611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3177876217411180207448407 4766814326116770311172611)
        ·
          refine ⟨7150221489175155466758917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4766814326116770311172611 7150221489175155466758917)
          ·
            refine ⟨1340666529220341650017297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7150221489175155466758917 1340666529220341650017297)
            ·
              refine ⟨1005499896915256237512973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1340666529220341650017297 1005499896915256237512973)
              ·
                refine ⟨377062461343221089067365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1005499896915256237512973 377062461343221089067365)
                ·
                  refine ⟨70699211501853954200131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 377062461343221089067365 70699211501853954200131)
                  ·
                    rfl

theorem cell20_154897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_154897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154897 prefixEnd_154897 := by exact prefixLift 154897
  have htrace : WordTrace (prefixWord ++ tailWord_154897) baseStart_154897 baseEnd_154897 := by
    simpa [prefixWord, tailWord_154897, baseEnd_154897] using wordTrace_append hprefix tailTrace_154897
  have hstable : (prefixWord ++ tailWord_154897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154897).length < 2 ^ (prefixWord ++ tailWord_154897).sum := by decide
  have hdescent : baseEnd_154897 < baseStart_154897 := by decide
  rcases family_descends (prefixWord ++ tailWord_154897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154910 : List Nat := [4, 3, 2, 1, 2, 1, 1, 2, 4]
def baseStart_154910 : Nat := 118140960795 + 154910 * 2 ^ 59
def prefixEnd_154910 : Nat := 4983230072969 + 3 ^ 40 * 154910 * 2
def baseEnd_154910 : Nat := 70705145056083686766745

theorem tailTrace_154910 : CollatzResearch.WordTrace tailWord_154910 prefixEnd_154910 70705145056083686766745 := by
  unfold tailWord_154910
  simp only [CollatzResearch.WordTrace]
  refine ⟨706253983599375170849773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3766687912530000911198789 706253983599375170849773)
  ·
    refine ⟨264845243849765689068665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 706253983599375170849773 264845243849765689068665)
    ·
      refine ⟨198633932887324266801499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264845243849765689068665 198633932887324266801499)
      ·
        refine ⟨297950899330986400202249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198633932887324266801499 297950899330986400202249)
        ·
          refine ⟨223463174498239800151687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297950899330986400202249 223463174498239800151687)
          ·
            refine ⟨335194761747359700227531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223463174498239800151687 335194761747359700227531)
            ·
              refine ⟨502792142621039550341297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335194761747359700227531 502792142621039550341297)
              ·
                refine ⟨377094106965779662755973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 502792142621039550341297 377094106965779662755973)
                ·
                  refine ⟨70705145056083686766745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 377094106965779662755973 70705145056083686766745)
                  ·
                    rfl

theorem cell20_154910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_154910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154910 prefixEnd_154910 := by exact prefixLift 154910
  have htrace : WordTrace (prefixWord ++ tailWord_154910) baseStart_154910 baseEnd_154910 := by
    simpa [prefixWord, tailWord_154910, baseEnd_154910] using wordTrace_append hprefix tailTrace_154910
  have hstable : (prefixWord ++ tailWord_154910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154910).length < 2 ^ (prefixWord ++ tailWord_154910).sum := by decide
  have hdescent : baseEnd_154910 < baseStart_154910 := by decide
  rcases family_descends (prefixWord ++ tailWord_154910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154931 : List Nat := [1, 1, 1, 2, 5, 3, 2, 3, 2]
def baseStart_154931 : Nat := 118140960795 + 154931 * 2 ^ 59
def prefixEnd_154931 : Nat := 4983230072969 + 3 ^ 40 * 154931 * 2
def baseEnd_154931 : Nat := 70714730028300947066659

theorem tailTrace_154931 : CollatzResearch.WordTrace tailWord_154931 prefixEnd_154931 70714730028300947066659 := by
  unfold tailWord_154931
  simp only [CollatzResearch.WordTrace]
  refine ⟨5650797801718921953312647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3767198534479281302208431 5650797801718921953312647)
  ·
    refine ⟨8476196702578382929968971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5650797801718921953312647 8476196702578382929968971)
    ·
      refine ⟨12714295053867574394953457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8476196702578382929968971 12714295053867574394953457)
      ·
        refine ⟨9535721290400680796215093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12714295053867574394953457 9535721290400680796215093)
        ·
          refine ⟨893973870975063824645165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9535721290400680796215093 893973870975063824645165)
          ·
            refine ⟨335240201615648934241937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 893973870975063824645165 335240201615648934241937)
            ·
              refine ⟨251430151211736700681453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335240201615648934241937 251430151211736700681453)
              ·
                refine ⟨94286306704401262755545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 251430151211736700681453 94286306704401262755545)
                ·
                  refine ⟨70714730028300947066659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94286306704401262755545 70714730028300947066659)
                  ·
                    rfl

theorem cell20_154931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 2].length) (baseStart_154931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154931 prefixEnd_154931 := by exact prefixLift 154931
  have htrace : WordTrace (prefixWord ++ tailWord_154931) baseStart_154931 baseEnd_154931 := by
    simpa [prefixWord, tailWord_154931, baseEnd_154931] using wordTrace_append hprefix tailTrace_154931
  have hstable : (prefixWord ++ tailWord_154931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154931).length < 2 ^ (prefixWord ++ tailWord_154931).sum := by decide
  have hdescent : baseEnd_154931 < baseStart_154931 := by decide
  rcases family_descends (prefixWord ++ tailWord_154931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154941 : List Nat := [1, 4, 1, 5, 1, 2, 1, 2, 3]
def baseStart_154941 : Nat := 118140960795 + 154941 * 2 ^ 59
def prefixEnd_154941 : Nat := 4983230072969 + 3 ^ 40 * 154941 * 2
def baseEnd_154941 : Nat := 70719294300785356733285

theorem tailTrace_154941 : CollatzResearch.WordTrace tailWord_154941 prefixEnd_154941 70719294300785356733285 := by
  unfold tailWord_154941
  simp only [CollatzResearch.WordTrace]
  refine ⟨5651162531682693661176677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3767441687788462440784451 5651162531682693661176677)
  ·
    refine ⟨1059592974690505061470627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5651162531682693661176677 1059592974690505061470627)
    ·
      refine ⟨1589389462035757592205941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1059592974690505061470627 1589389462035757592205941)
      ·
        refine ⟨149005262065852274269307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1589389462035757592205941 149005262065852274269307)
        ·
          refine ⟨223507893098778411403961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149005262065852274269307 223507893098778411403961)
          ·
            refine ⟨167630919824083808552971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223507893098778411403961 167630919824083808552971)
            ·
              refine ⟨251446379736125712829457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167630919824083808552971 251446379736125712829457)
              ·
                refine ⟨188584784802094284622093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251446379736125712829457 188584784802094284622093)
                ·
                  refine ⟨70719294300785356733285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188584784802094284622093 70719294300785356733285)
                  ·
                    rfl

theorem cell20_154941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_154941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154941 prefixEnd_154941 := by exact prefixLift 154941
  have htrace : WordTrace (prefixWord ++ tailWord_154941) baseStart_154941 baseEnd_154941 := by
    simpa [prefixWord, tailWord_154941, baseEnd_154941] using wordTrace_append hprefix tailTrace_154941
  have hstable : (prefixWord ++ tailWord_154941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154941).length < 2 ^ (prefixWord ++ tailWord_154941).sum := by decide
  have hdescent : baseEnd_154941 < baseStart_154941 := by decide
  rcases family_descends (prefixWord ++ tailWord_154941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154945 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 5]
def baseStart_154945 : Nat := 118140960795 + 154945 * 2 ^ 59
def prefixEnd_154945 : Nat := 4983230072969 + 3 ^ 40 * 154945 * 2
def baseEnd_154945 : Nat := 70721120009779120599935

theorem tailTrace_154945 : CollatzResearch.WordTrace tailWord_154945 prefixEnd_154945 70721120009779120599935 := by
  unfold tailWord_154945
  simp only [CollatzResearch.WordTrace]
  refine ⟨5651308423668202344322289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3767538949112134896214859 5651308423668202344322289)
  ·
    refine ⟨4238481317751151758241717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5651308423668202344322289 4238481317751151758241717)
    ·
      refine ⟨397357623539170477335161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4238481317751151758241717 397357623539170477335161)
      ·
        refine ⟨298018217654377858001371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 397357623539170477335161 298018217654377858001371)
        ·
          refine ⟨447027326481566787002057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298018217654377858001371 447027326481566787002057)
          ·
            refine ⟨335270494861175090251543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 447027326481566787002057 335270494861175090251543)
            ·
              refine ⟨502905742291762635377315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335270494861175090251543 502905742291762635377315)
              ·
                refine ⟨754358613437643953065973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 502905742291762635377315 754358613437643953065973)
                ·
                  refine ⟨70721120009779120599935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 754358613437643953065973 70721120009779120599935)
                  ·
                    rfl

theorem cell20_154945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_154945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154945 prefixEnd_154945 := by exact prefixLift 154945
  have htrace : WordTrace (prefixWord ++ tailWord_154945) baseStart_154945 baseEnd_154945 := by
    simpa [prefixWord, tailWord_154945, baseEnd_154945] using wordTrace_append hprefix tailTrace_154945
  have hstable : (prefixWord ++ tailWord_154945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154945).length < 2 ^ (prefixWord ++ tailWord_154945).sum := by decide
  have hdescent : baseEnd_154945 < baseStart_154945 := by decide
  rcases family_descends (prefixWord ++ tailWord_154945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154948 : List Nat := [2, 3, 4, 1, 1, 1, 2, 4, 2]
def baseStart_154948 : Nat := 118140960795 + 154948 * 2 ^ 59
def prefixEnd_154948 : Nat := 4983230072969 + 3 ^ 40 * 154948 * 2
def baseEnd_154948 : Nat := 70722489291524443499923

theorem tailTrace_154948 : CollatzResearch.WordTrace tailWord_154948 prefixEnd_154948 70722489291524443499923 := by
  unfold tailWord_154948
  simp only [CollatzResearch.WordTrace]
  refine ⟨2825708921328666928340749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3767611895104889237787665 2825708921328666928340749)
  ·
    refine ⟨1059640845498250098127781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2825708921328666928340749 1059640845498250098127781)
    ·
      refine ⟨198682658530921893398959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1059640845498250098127781 198682658530921893398959)
      ·
        refine ⟨298023987796382840098439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198682658530921893398959 298023987796382840098439)
        ·
          refine ⟨447035981694574260147659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298023987796382840098439 447035981694574260147659)
          ·
            refine ⟨670553972541861390221489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447035981694574260147659 670553972541861390221489)
            ·
              refine ⟨502915479406396042666117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 670553972541861390221489 502915479406396042666117)
              ·
                refine ⟨94296652388699257999897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 502915479406396042666117 94296652388699257999897)
                ·
                  refine ⟨70722489291524443499923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94296652388699257999897 70722489291524443499923)
                  ·
                    rfl

theorem cell20_154948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_154948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154948 prefixEnd_154948 := by exact prefixLift 154948
  have htrace : WordTrace (prefixWord ++ tailWord_154948) baseStart_154948 baseEnd_154948 := by
    simpa [prefixWord, tailWord_154948, baseEnd_154948] using wordTrace_append hprefix tailTrace_154948
  have hstable : (prefixWord ++ tailWord_154948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154948).length < 2 ^ (prefixWord ++ tailWord_154948).sum := by decide
  have hdescent : baseEnd_154948 < baseStart_154948 := by decide
  rcases family_descends (prefixWord ++ tailWord_154948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154976 : List Nat := [2, 1, 1, 3, 4, 3, 2, 4]
def baseStart_154976 : Nat := 118140960795 + 154976 * 2 ^ 59
def prefixEnd_154976 : Nat := 4983230072969 + 3 ^ 40 * 154976 * 2
def baseEnd_154976 : Nat := 23578423084826930188825

theorem tailTrace_154976 : CollatzResearch.WordTrace tailWord_154976 prefixEnd_154976 23578423084826930188825 := by
  unfold tailWord_154976
  simp only [CollatzResearch.WordTrace]
  refine ⟨2826219543277947319350391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3768292724370596425800521 2826219543277947319350391)
  ·
    refine ⟨4239329314916920979025587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2826219543277947319350391 4239329314916920979025587)
    ·
      refine ⟨6358993972375381468538381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4239329314916920979025587 6358993972375381468538381)
      ·
        refine ⟨2384622739640768050701893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6358993972375381468538381 2384622739640768050701893)
        ·
          refine ⟨447116763682644009506605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2384622739640768050701893 447116763682644009506605)
          ·
            refine ⟨167668786380991503564977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 447116763682644009506605 167668786380991503564977)
            ·
              refine ⟨125751589785743627673733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167668786380991503564977 125751589785743627673733)
              ·
                refine ⟨23578423084826930188825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125751589785743627673733 23578423084826930188825)
                ·
                  rfl

theorem cell20_154976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 4].length) (baseStart_154976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_154976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_154976 prefixEnd_154976 := by exact prefixLift 154976
  have htrace : WordTrace (prefixWord ++ tailWord_154976) baseStart_154976 baseEnd_154976 := by
    simpa [prefixWord, tailWord_154976, baseEnd_154976] using wordTrace_append hprefix tailTrace_154976
  have hstable : (prefixWord ++ tailWord_154976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154976).length < 2 ^ (prefixWord ++ tailWord_154976).sum := by decide
  have hdescent : baseEnd_154976 < baseStart_154976 := by decide
  rcases family_descends (prefixWord ++ tailWord_154976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155004 : List Nat := [2, 2, 2, 1, 1, 1, 4, 4, 3]
def baseStart_155004 : Nat := 118140960795 + 155004 * 2 ^ 59
def prefixEnd_155004 : Nat := 4983230072969 + 3 ^ 40 * 155004 * 2
def baseEnd_155004 : Nat := 70748049217437137633027

theorem tailTrace_155004 : CollatzResearch.WordTrace tailWord_155004 prefixEnd_155004 70748049217437137633027 := by
  unfold tailWord_155004
  simp only [CollatzResearch.WordTrace]
  refine ⟨2826730165227227710360033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3768973553636303613813377 2826730165227227710360033)
  ·
    refine ⟨2120047623920420782770025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2826730165227227710360033 2120047623920420782770025)
    ·
      refine ⟨1590035717940315587077519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2120047623920420782770025 1590035717940315587077519)
      ·
        refine ⟨2385053576910473380616279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1590035717940315587077519 2385053576910473380616279)
        ·
          refine ⟨3577580365365710070924419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2385053576910473380616279 3577580365365710070924419)
          ·
            refine ⟨5366370548048565106386629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3577580365365710070924419 5366370548048565106386629)
            ·
              refine ⟨1006194477759105957447493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5366370548048565106386629 1006194477759105957447493)
              ·
                refine ⟨188661464579832367021405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1006194477759105957447493 188661464579832367021405)
                ·
                  refine ⟨70748049217437137633027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188661464579832367021405 70748049217437137633027)
                  ·
                    rfl

theorem cell20_155004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_155004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155004 prefixEnd_155004 := by exact prefixLift 155004
  have htrace : WordTrace (prefixWord ++ tailWord_155004) baseStart_155004 baseEnd_155004 := by
    simpa [prefixWord, tailWord_155004, baseEnd_155004] using wordTrace_append hprefix tailTrace_155004
  have hstable : (prefixWord ++ tailWord_155004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155004).length < 2 ^ (prefixWord ++ tailWord_155004).sum := by decide
  have hdescent : baseEnd_155004 < baseStart_155004 := by decide
  rcases family_descends (prefixWord ++ tailWord_155004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155017 : List Nat := [1, 2, 1, 1, 8, 1, 2, 1, 3]
def baseStart_155017 : Nat := 118140960795 + 155017 * 2 ^ 59
def prefixEnd_155017 : Nat := 4983230072969 + 3 ^ 40 * 155017 * 2
def baseEnd_155017 : Nat := 70753982771666870199641

theorem tailTrace_155017 : CollatzResearch.WordTrace tailWord_155017 prefixEnd_155017 70753982771666870199641 := by
  unfold tailWord_155017
  simp only [CollatzResearch.WordTrace]
  refine ⟨5653934479407358640943305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3769289652938239093962203 5653934479407358640943305)
  ·
    refine ⟨4240450859555518980707479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5653934479407358640943305 4240450859555518980707479)
    ·
      refine ⟨6360676289333278471061219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4240450859555518980707479 6360676289333278471061219)
      ·
        refine ⟨9541014433999917706591829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6360676289333278471061219 9541014433999917706591829)
        ·
          refine ⟨111808762898436535624123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 9541014433999917706591829 111808762898436535624123)
          ·
            refine ⟨167713144347654803436185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111808762898436535624123 167713144347654803436185)
            ·
              refine ⟨125784858260741102577139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167713144347654803436185 125784858260741102577139)
              ·
                refine ⟨188677287391111653865709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125784858260741102577139 188677287391111653865709)
                ·
                  refine ⟨70753982771666870199641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188677287391111653865709 70753982771666870199641)
                  ·
                    rfl

theorem cell20_155017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 3].length) (baseStart_155017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155017 prefixEnd_155017 := by exact prefixLift 155017
  have htrace : WordTrace (prefixWord ++ tailWord_155017) baseStart_155017 baseEnd_155017 := by
    simpa [prefixWord, tailWord_155017, baseEnd_155017] using wordTrace_append hprefix tailTrace_155017
  have hstable : (prefixWord ++ tailWord_155017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155017).length < 2 ^ (prefixWord ++ tailWord_155017).sum := by decide
  have hdescent : baseEnd_155017 < baseStart_155017 := by decide
  rcases family_descends (prefixWord ++ tailWord_155017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155080 : List Nat := [2, 1, 3, 1, 3, 1, 1, 5, 3]
def baseStart_155080 : Nat := 118140960795 + 155080 * 2 ^ 59
def prefixEnd_155080 : Nat := 4983230072969 + 3 ^ 40 * 155080 * 2
def baseEnd_155080 : Nat := 70782737688318651099383

theorem tailTrace_155080 : CollatzResearch.WordTrace tailWord_155080 prefixEnd_155080 70782737688318651099383 := by
  unfold tailWord_155080
  simp only [CollatzResearch.WordTrace]
  refine ⟨2828116139089560200243347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3770821518786080266991129 2828116139089560200243347)
  ·
    refine ⟨4242174208634340300365021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2828116139089560200243347 4242174208634340300365021)
    ·
      refine ⟨1590815328237877612636883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4242174208634340300365021 1590815328237877612636883)
      ·
        refine ⟨2386222992356816418955325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1590815328237877612636883 2386222992356816418955325)
        ·
          refine ⟨894833622133806157108247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2386222992356816418955325 894833622133806157108247)
          ·
            refine ⟨1342250433200709235662371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894833622133806157108247 1342250433200709235662371)
            ·
              refine ⟨2013375649801063853493557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1342250433200709235662371 2013375649801063853493557)
              ·
                refine ⟨188753967168849736265021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2013375649801063853493557 188753967168849736265021)
                ·
                  refine ⟨70782737688318651099383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188753967168849736265021 70782737688318651099383)
                  ·
                    rfl

theorem cell20_155080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 3].length) (baseStart_155080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155080 prefixEnd_155080 := by exact prefixLift 155080
  have htrace : WordTrace (prefixWord ++ tailWord_155080) baseStart_155080 baseEnd_155080 := by
    simpa [prefixWord, tailWord_155080, baseEnd_155080] using wordTrace_append hprefix tailTrace_155080
  have hstable : (prefixWord ++ tailWord_155080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155080).length < 2 ^ (prefixWord ++ tailWord_155080).sum := by decide
  have hdescent : baseEnd_155080 < baseStart_155080 := by decide
  rcases family_descends (prefixWord ++ tailWord_155080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155114 : List Nat := [3, 1, 3, 1, 4, 2, 1, 2, 3]
def baseStart_155114 : Nat := 118140960795 + 155114 * 2 ^ 59
def prefixEnd_155114 : Nat := 4983230072969 + 3 ^ 40 * 155114 * 2
def baseEnd_155114 : Nat := 70798256214765643965911

theorem tailTrace_155114 : CollatzResearch.WordTrace tailWord_155114 prefixEnd_155114 70798256214765643965911 := by
  unfold tailWord_155114
  simp only [CollatzResearch.WordTrace]
  refine ⟨1414368090013986051806099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3771648240037296138149597 1414368090013986051806099)
  ·
    refine ⟨2121552135020979077709149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1414368090013986051806099 2121552135020979077709149)
    ·
      refine ⟨795582050632867154140931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2121552135020979077709149 795582050632867154140931)
      ·
        refine ⟨1193373075949300731211397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 795582050632867154140931 1193373075949300731211397)
        ·
          refine ⟨223757451740493887102137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1193373075949300731211397 223757451740493887102137)
          ·
            refine ⟨167818088805370415326603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223757451740493887102137 167818088805370415326603)
            ·
              refine ⟨251727133208055622989905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167818088805370415326603 251727133208055622989905)
              ·
                refine ⟨188795349906041717242429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251727133208055622989905 188795349906041717242429)
                ·
                  refine ⟨70798256214765643965911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188795349906041717242429 70798256214765643965911)
                  ·
                    rfl

theorem cell20_155114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_155114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155114 prefixEnd_155114 := by exact prefixLift 155114
  have htrace : WordTrace (prefixWord ++ tailWord_155114) baseStart_155114 baseEnd_155114 := by
    simpa [prefixWord, tailWord_155114, baseEnd_155114] using wordTrace_append hprefix tailTrace_155114
  have hstable : (prefixWord ++ tailWord_155114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155114).length < 2 ^ (prefixWord ++ tailWord_155114).sum := by decide
  have hdescent : baseEnd_155114 < baseStart_155114 := by decide
  rcases family_descends (prefixWord ++ tailWord_155114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155118 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_155118 : Nat := 118140960795 + 155118 * 2 ^ 59
def prefixEnd_155118 : Nat := 4983230072969 + 3 ^ 40 * 155118 * 2
def baseEnd_155118 : Nat := 70800081923759407832561

theorem tailTrace_155118 : CollatzResearch.WordTrace tailWord_155118 prefixEnd_155118 70800081923759407832561 := by
  unfold tailWord_155118
  simp only [CollatzResearch.WordTrace]
  refine ⟨707202281505181611296251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3771745501360968593580005 707202281505181611296251)
  ·
    refine ⟨1060803422257772416944377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 707202281505181611296251 1060803422257772416944377)
    ·
      refine ⟨795602566693329312708283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1060803422257772416944377 795602566693329312708283)
      ·
        refine ⟨1193403850039993969062425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 795602566693329312708283 1193403850039993969062425)
        ·
          refine ⟨895052887529995476796819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1193403850039993969062425 895052887529995476796819)
          ·
            refine ⟨1342579331294993215195229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 895052887529995476796819 1342579331294993215195229)
            ·
              refine ⟨503467249235622455698211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1342579331294993215195229 503467249235622455698211)
              ·
                refine ⟨755200873853433683547317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 503467249235622455698211 755200873853433683547317)
                ·
                  refine ⟨70800081923759407832561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 755200873853433683547317 70800081923759407832561)
                  ·
                    rfl

theorem cell20_155118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_155118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155118 prefixEnd_155118 := by exact prefixLift 155118
  have htrace : WordTrace (prefixWord ++ tailWord_155118) baseStart_155118 baseEnd_155118 := by
    simpa [prefixWord, tailWord_155118, baseEnd_155118] using wordTrace_append hprefix tailTrace_155118
  have hstable : (prefixWord ++ tailWord_155118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155118).length < 2 ^ (prefixWord ++ tailWord_155118).sum := by decide
  have hdescent : baseEnd_155118 < baseStart_155118 := by decide
  rcases family_descends (prefixWord ++ tailWord_155118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155170 : List Nat := [3, 3, 1, 1, 1, 1, 10]
def baseStart_155170 : Nat := 118140960795 + 155170 * 2 ^ 59
def prefixEnd_155170 : Nat := 4983230072969 + 3 ^ 40 * 155170 * 2
def baseEnd_155170 : Nat := 7869312904519815344335

theorem tailTrace_155170 : CollatzResearch.WordTrace tailWord_155170 prefixEnd_155170 7869312904519815344335 := by
  unfold tailWord_155170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1414878711963266442815741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3773009898568710514175309 1414878711963266442815741)
  ·
    refine ⟨530579516986224916055903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1414878711963266442815741 530579516986224916055903)
    ·
      refine ⟨795869275479337374083855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 530579516986224916055903 795869275479337374083855)
      ·
        refine ⟨1193803913219006061125783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 795869275479337374083855 1193803913219006061125783)
        ·
          refine ⟨1790705869828509091688675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1193803913219006061125783 1790705869828509091688675)
          ·
            refine ⟨2686058804742763637533013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1790705869828509091688675 2686058804742763637533013)
            ·
              refine ⟨7869312904519815344335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2686058804742763637533013 7869312904519815344335)
              ·
                rfl

theorem cell20_155170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 10].length) (baseStart_155170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155170 prefixEnd_155170 := by exact prefixLift 155170
  have htrace : WordTrace (prefixWord ++ tailWord_155170) baseStart_155170 baseEnd_155170 := by
    simpa [prefixWord, tailWord_155170, baseEnd_155170] using wordTrace_append hprefix tailTrace_155170
  have hstable : (prefixWord ++ tailWord_155170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155170).length < 2 ^ (prefixWord ++ tailWord_155170).sum := by decide
  have hdescent : baseEnd_155170 < baseStart_155170 := by decide
  rcases family_descends (prefixWord ++ tailWord_155170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155176 : List Nat := [2, 1, 5, 2, 3, 1, 1, 1, 4]
def baseStart_155176 : Nat := 118140960795 + 155176 * 2 ^ 59
def prefixEnd_155176 : Nat := 4983230072969 + 3 ^ 40 * 155176 * 2
def baseEnd_155176 : Nat := 70826554704168983898991

theorem tailTrace_155176 : CollatzResearch.WordTrace tailWord_155176 prefixEnd_155176 70826554704168983898991 := by
  unfold tailWord_155176
  simp only [CollatzResearch.WordTrace]
  refine ⟨2829866842915664397990691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3773155790554219197320921 2829866842915664397990691)
  ·
    refine ⟨4244800264373496596986037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2829866842915664397990691 4244800264373496596986037)
    ·
      refine ⟨397950024785015305967441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4244800264373496596986037 397950024785015305967441)
      ·
        refine ⟨298462518588761479475581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 397950024785015305967441 298462518588761479475581)
        ·
          refine ⟨111923444470785554803343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 298462518588761479475581 111923444470785554803343)
          ·
            refine ⟨167885166706178332205015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111923444470785554803343 167885166706178332205015)
            ·
              refine ⟨251827750059267498307523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167885166706178332205015 251827750059267498307523)
              ·
                refine ⟨377741625088901247461285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251827750059267498307523 377741625088901247461285)
                ·
                  refine ⟨70826554704168983898991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 377741625088901247461285 70826554704168983898991)
                  ·
                    rfl

theorem cell20_155176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 4].length) (baseStart_155176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155176 prefixEnd_155176 := by exact prefixLift 155176
  have htrace : WordTrace (prefixWord ++ tailWord_155176) baseStart_155176 baseEnd_155176 := by
    simpa [prefixWord, tailWord_155176, baseEnd_155176] using wordTrace_append hprefix tailTrace_155176
  have hstable : (prefixWord ++ tailWord_155176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155176).length < 2 ^ (prefixWord ++ tailWord_155176).sum := by decide
  have hdescent : baseEnd_155176 < baseStart_155176 := by decide
  rcases family_descends (prefixWord ++ tailWord_155176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155190 : List Nat := [5, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_155190 : Nat := 118140960795 + 155190 * 2 ^ 59
def prefixEnd_155190 : Nat := 4983230072969 + 3 ^ 40 * 155190 * 2
def baseEnd_155190 : Nat := 70832944685647157432267

theorem tailTrace_155190 : CollatzResearch.WordTrace tailWord_155190 prefixEnd_155190 70832944685647157432267 := by
  unfold tailWord_155190
  simp only [CollatzResearch.WordTrace]
  refine ⟨353765269236288074186939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3773496205187072791327349 353765269236288074186939)
  ·
    refine ⟨530647903854432111280409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 353765269236288074186939 530647903854432111280409)
    ·
      refine ⟨397985927890824083460307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 530647903854432111280409 397985927890824083460307)
      ·
        refine ⟨596978891836236125190461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397985927890824083460307 596978891836236125190461)
        ·
          refine ⟨223867084438588546946423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 596978891836236125190461 223867084438588546946423)
          ·
            refine ⟨335800626657882820419635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223867084438588546946423 335800626657882820419635)
            ·
              refine ⟨503700939986824230629453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335800626657882820419635 503700939986824230629453)
              ·
                refine ⟨188887852495059086486045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 503700939986824230629453 188887852495059086486045)
                ·
                  refine ⟨70832944685647157432267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188887852495059086486045 70832944685647157432267)
                  ·
                    rfl

theorem cell20_155190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_155190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155190 prefixEnd_155190 := by exact prefixLift 155190
  have htrace : WordTrace (prefixWord ++ tailWord_155190) baseStart_155190 baseEnd_155190 := by
    simpa [prefixWord, tailWord_155190, baseEnd_155190] using wordTrace_append hprefix tailTrace_155190
  have hstable : (prefixWord ++ tailWord_155190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155190).length < 2 ^ (prefixWord ++ tailWord_155190).sum := by decide
  have hdescent : baseEnd_155190 < baseStart_155190 := by decide
  rcases family_descends (prefixWord ++ tailWord_155190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155194 : List Nat := [3, 1, 1, 1, 3, 2, 3, 3, 3]
def baseStart_155194 : Nat := 118140960795 + 155194 * 2 ^ 59
def prefixEnd_155194 : Nat := 4983230072969 + 3 ^ 40 * 155194 * 2
def baseEnd_155194 : Nat := 70834770394640921298917

theorem tailTrace_155194 : CollatzResearch.WordTrace tailWord_155194 prefixEnd_155194 70834770394640921298917 := by
  unfold tailWord_155194
  simp only [CollatzResearch.WordTrace]
  refine ⟨1415097549941529467534159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3773593466510745246757757 1415097549941529467534159)
  ·
    refine ⟨2122646324912294201301239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1415097549941529467534159 2122646324912294201301239)
    ·
      refine ⟨3183969487368441301951859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2122646324912294201301239 3183969487368441301951859)
      ·
        refine ⟨4775954231052661952927789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3183969487368441301951859 4775954231052661952927789)
        ·
          refine ⟨1790982836644748232347921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4775954231052661952927789 1790982836644748232347921)
          ·
            refine ⟨1343237127483561174260941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1790982836644748232347921 1343237127483561174260941)
            ·
              refine ⟨503713922806335440347853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1343237127483561174260941 503713922806335440347853)
              ·
                refine ⟨188892721052375790130445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 503713922806335440347853 188892721052375790130445)
                ·
                  refine ⟨70834770394640921298917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188892721052375790130445 70834770394640921298917)
                  ·
                    rfl

theorem cell20_155194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_155194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155194 prefixEnd_155194 := by exact prefixLift 155194
  have htrace : WordTrace (prefixWord ++ tailWord_155194) baseStart_155194 baseEnd_155194 := by
    simpa [prefixWord, tailWord_155194, baseEnd_155194] using wordTrace_append hprefix tailTrace_155194
  have hstable : (prefixWord ++ tailWord_155194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155194).length < 2 ^ (prefixWord ++ tailWord_155194).sum := by decide
  have hdescent : baseEnd_155194 < baseStart_155194 := by decide
  rcases family_descends (prefixWord ++ tailWord_155194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155201 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 6]
def baseStart_155201 : Nat := 118140960795 + 155201 * 2 ^ 59
def prefixEnd_155201 : Nat := 4983230072969 + 3 ^ 40 * 155201 * 2
def baseEnd_155201 : Nat := 70837965385380008065555

theorem tailTrace_155201 : CollatzResearch.WordTrace tailWord_155201 prefixEnd_155201 70837965385380008065555 := by
  unfold tailWord_155201
  simp only [CollatzResearch.WordTrace]
  refine ⟨5660645510740758065641457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3773763673827172043760971 5660645510740758065641457)
  ·
    refine ⟨4245484133055568549231093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5660645510740758065641457 4245484133055568549231093)
    ·
      refine ⟨398014137473959551490415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4245484133055568549231093 398014137473959551490415)
      ·
        refine ⟨597021206210939327235623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398014137473959551490415 597021206210939327235623)
        ·
          refine ⟨895531809316408990853435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597021206210939327235623 895531809316408990853435)
          ·
            refine ⟨1343297713974613486280153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 895531809316408990853435 1343297713974613486280153)
            ·
              refine ⟨1007473285480960114710115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1343297713974613486280153 1007473285480960114710115)
              ·
                refine ⟨1511209928221440172065173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1007473285480960114710115 1511209928221440172065173)
                ·
                  refine ⟨70837965385380008065555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1511209928221440172065173 70837965385380008065555)
                  ·
                    rfl

theorem cell20_155201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_155201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155201 prefixEnd_155201 := by exact prefixLift 155201
  have htrace : WordTrace (prefixWord ++ tailWord_155201) baseStart_155201 baseEnd_155201 := by
    simpa [prefixWord, tailWord_155201, baseEnd_155201] using wordTrace_append hprefix tailTrace_155201
  have hstable : (prefixWord ++ tailWord_155201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155201).length < 2 ^ (prefixWord ++ tailWord_155201).sum := by decide
  have hdescent : baseEnd_155201 < baseStart_155201 := by decide
  rcases family_descends (prefixWord ++ tailWord_155201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155235 : List Nat := [1, 1, 1, 5, 1, 3, 4, 2, 2]
def baseStart_155235 : Nat := 118140960795 + 155235 * 2 ^ 59
def prefixEnd_155235 : Nat := 4983230072969 + 3 ^ 40 * 155235 * 2
def baseEnd_155235 : Nat := 70853483911827000932083

theorem tailTrace_155235 : CollatzResearch.WordTrace tailWord_155235 prefixEnd_155235 70853483911827000932083 := by
  unfold tailWord_155235
  simp only [CollatzResearch.WordTrace]
  refine ⟨5661885592617581872379159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3774590395078387914919439 5661885592617581872379159)
  ·
    refine ⟨8492828388926372808568739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5661885592617581872379159 8492828388926372808568739)
    ·
      refine ⟨12739242583389559212853109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8492828388926372808568739 12739242583389559212853109)
      ·
        refine ⟨1194303992192771176204979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12739242583389559212853109 1194303992192771176204979)
        ·
          refine ⟨1791455988289156764307469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1194303992192771176204979 1791455988289156764307469)
          ·
            refine ⟨671795995608433786615301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1791455988289156764307469 671795995608433786615301)
            ·
              refine ⟨125961749176581334990369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 671795995608433786615301 125961749176581334990369)
              ·
                refine ⟨94471311882436001242777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125961749176581334990369 94471311882436001242777)
                ·
                  refine ⟨70853483911827000932083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94471311882436001242777 70853483911827000932083)
                  ·
                    rfl

theorem cell20_155235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 2].length) (baseStart_155235 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155235 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155235 prefixEnd_155235 := by exact prefixLift 155235
  have htrace : WordTrace (prefixWord ++ tailWord_155235) baseStart_155235 baseEnd_155235 := by
    simpa [prefixWord, tailWord_155235, baseEnd_155235] using wordTrace_append hprefix tailTrace_155235
  have hstable : (prefixWord ++ tailWord_155235).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155235).length < 2 ^ (prefixWord ++ tailWord_155235).sum := by decide
  have hdescent : baseEnd_155235 < baseStart_155235 := by decide
  rcases family_descends (prefixWord ++ tailWord_155235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155287 : List Nat := [1, 1, 3, 3, 2, 4, 1, 2, 3]
def baseStart_155287 : Nat := 118140960795 + 155287 * 2 ^ 59
def prefixEnd_155287 : Nat := 4983230072969 + 3 ^ 40 * 155287 * 2
def baseEnd_155287 : Nat := 70877218128745931198537

theorem tailTrace_155287 : CollatzResearch.WordTrace tailWord_155287 prefixEnd_155287 70877218128745931198537 := by
  unfold tailWord_155287
  simp only [CollatzResearch.WordTrace]
  refine ⟨5663782188429194753272115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3775854792286129835514743 5663782188429194753272115)
  ·
    refine ⟨8495673282643792129908173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5663782188429194753272115 8495673282643792129908173)
    ·
      refine ⟨3185877480991422048715565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8495673282643792129908173 3185877480991422048715565)
      ·
        refine ⟨1194704055371783268268337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3185877480991422048715565 1194704055371783268268337)
        ·
          refine ⟨896028041528837451201253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1194704055371783268268337 896028041528837451201253)
          ·
            refine ⟨168005257786657022100235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 896028041528837451201253 168005257786657022100235)
            ·
              refine ⟨252007886679985533150353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168005257786657022100235 252007886679985533150353)
              ·
                refine ⟨189005915009989149862765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252007886679985533150353 189005915009989149862765)
                ·
                  refine ⟨70877218128745931198537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189005915009989149862765 70877218128745931198537)
                  ·
                    rfl

theorem cell20_155287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 3].length) (baseStart_155287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155287 prefixEnd_155287 := by exact prefixLift 155287
  have htrace : WordTrace (prefixWord ++ tailWord_155287) baseStart_155287 baseEnd_155287 := by
    simpa [prefixWord, tailWord_155287, baseEnd_155287] using wordTrace_append hprefix tailTrace_155287
  have hstable : (prefixWord ++ tailWord_155287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155287).length < 2 ^ (prefixWord ++ tailWord_155287).sum := by decide
  have hdescent : baseEnd_155287 < baseStart_155287 := by decide
  rcases family_descends (prefixWord ++ tailWord_155287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155294 : List Nat := [4, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_155294 : Nat := 118140960795 + 155294 * 2 ^ 59
def prefixEnd_155294 : Nat := 4983230072969 + 3 ^ 40 * 155294 * 2
def baseEnd_155294 : Nat := 70880413119485017965175

theorem tailTrace_155294 : CollatzResearch.WordTrace tailWord_155294 prefixEnd_155294 70880413119485017965175 := by
  unfold tailWord_155294
  simp only [CollatzResearch.WordTrace]
  refine ⟨708004687425479368597117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3776024999602556632517957 708004687425479368597117)
  ·
    refine ⟨265501757784554763223919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 708004687425479368597117 265501757784554763223919)
    ·
      refine ⟨398252636676832144835879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265501757784554763223919 398252636676832144835879)
      ·
        refine ⟨597378955015248217253819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398252636676832144835879 597378955015248217253819)
        ·
          refine ⟨896068432522872325880729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597378955015248217253819 896068432522872325880729)
          ·
            refine ⟨672051324392154244410547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 896068432522872325880729 672051324392154244410547)
            ·
              refine ⟨1008076986588231366615821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672051324392154244410547 1008076986588231366615821)
              ·
                refine ⟨378028869970586762480933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1008076986588231366615821 378028869970586762480933)
                ·
                  refine ⟨70880413119485017965175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 378028869970586762480933 70880413119485017965175)
                  ·
                    rfl

theorem cell20_155294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_155294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155294 prefixEnd_155294 := by exact prefixLift 155294
  have htrace : WordTrace (prefixWord ++ tailWord_155294) baseStart_155294 baseEnd_155294 := by
    simpa [prefixWord, tailWord_155294, baseEnd_155294] using wordTrace_append hprefix tailTrace_155294
  have hstable : (prefixWord ++ tailWord_155294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155294).length < 2 ^ (prefixWord ++ tailWord_155294).sum := by decide
  have hdescent : baseEnd_155294 < baseStart_155294 := by decide
  rcases family_descends (prefixWord ++ tailWord_155294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155318 : List Nat := [5, 1, 3, 1, 1, 2, 1, 6]
def baseStart_155318 : Nat := 118140960795 + 155318 * 2 ^ 59
def prefixEnd_155318 : Nat := 4983230072969 + 3 ^ 40 * 155318 * 2
def baseEnd_155318 : Nat := 23630455791149200388359

theorem tailTrace_155318 : CollatzResearch.WordTrace tailWord_155318 prefixEnd_155318 23630455791149200388359 := by
  unfold tailWord_155318
  simp only [CollatzResearch.WordTrace]
  refine ⟨354057053207305440478163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3776608567544591365100405 354057053207305440478163)
  ·
    refine ⟨531085579810958160717245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 354057053207305440478163 531085579810958160717245)
    ·
      refine ⟨199157092429109310268967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 531085579810958160717245 199157092429109310268967)
      ·
        refine ⟨298735638643663965403451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199157092429109310268967 298735638643663965403451)
        ·
          refine ⟨448103457965495948105177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298735638643663965403451 448103457965495948105177)
          ·
            refine ⟨336077593474121961078883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 448103457965495948105177 336077593474121961078883)
            ·
              refine ⟨504116390211182941618325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336077593474121961078883 504116390211182941618325)
              ·
                refine ⟨23630455791149200388359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 504116390211182941618325 23630455791149200388359)
                ·
                  rfl

theorem cell20_155318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_155318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155318 prefixEnd_155318 := by exact prefixLift 155318
  have htrace : WordTrace (prefixWord ++ tailWord_155318) baseStart_155318 baseEnd_155318 := by
    simpa [prefixWord, tailWord_155318, baseEnd_155318] using wordTrace_append hprefix tailTrace_155318
  have hstable : (prefixWord ++ tailWord_155318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155318).length < 2 ^ (prefixWord ++ tailWord_155318).sum := by decide
  have hdescent : baseEnd_155318 < baseStart_155318 := by decide
  rcases family_descends (prefixWord ++ tailWord_155318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155322 : List Nat := [3, 1, 1, 1, 2, 5, 1, 6]
def baseStart_155322 : Nat := 118140960795 + 155322 * 2 ^ 59
def prefixEnd_155322 : Nat := 4983230072969 + 3 ^ 40 * 155322 * 2
def baseEnd_155322 : Nat := 23631064360813788343909

theorem tailTrace_155322 : CollatzResearch.WordTrace tailWord_155322 prefixEnd_155322 23631064360813788343909 := by
  unfold tailWord_155322
  simp only [CollatzResearch.WordTrace]
  refine ⟨1416264685825598932699055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3776705828868263820530813 1416264685825598932699055)
  ·
    refine ⟨2124397028738398399048583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1416264685825598932699055 2124397028738398399048583)
    ·
      refine ⟨3186595543107597598572875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2124397028738398399048583 3186595543107597598572875)
      ·
        refine ⟨4779893314661396397859313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3186595543107597598572875 4779893314661396397859313)
        ·
          refine ⟨3584919985996047298394485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4779893314661396397859313 3584919985996047298394485)
          ·
            refine ⟨336086248687129434224483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3584919985996047298394485 336086248687129434224483)
            ·
              refine ⟨504129373030694151336725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336086248687129434224483 504129373030694151336725)
              ·
                refine ⟨23631064360813788343909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 504129373030694151336725 23631064360813788343909)
                ·
                  rfl

theorem cell20_155322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_155322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155322 prefixEnd_155322 := by exact prefixLift 155322
  have htrace : WordTrace (prefixWord ++ tailWord_155322) baseStart_155322 baseEnd_155322 := by
    simpa [prefixWord, tailWord_155322, baseEnd_155322] using wordTrace_append hprefix tailTrace_155322
  have hstable : (prefixWord ++ tailWord_155322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155322).length < 2 ^ (prefixWord ++ tailWord_155322).sum := by decide
  have hdescent : baseEnd_155322 < baseStart_155322 := by decide
  rcases family_descends (prefixWord ++ tailWord_155322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155346 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 5]
def baseStart_155346 : Nat := 118140960795 + 155346 * 2 ^ 59
def prefixEnd_155346 : Nat := 4983230072969 + 3 ^ 40 * 155346 * 2
def baseEnd_155346 : Nat := 70904147336403948231629

theorem tailTrace_155346 : CollatzResearch.WordTrace tailWord_155346 prefixEnd_155346 70904147336403948231629 := by
  unfold tailWord_155346
  simp only [CollatzResearch.WordTrace]
  refine ⟨1416483523803861957417473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3777289396810298553113261 1416483523803861957417473)
  ·
    refine ⟨1062362642852896468063105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1416483523803861957417473 1062362642852896468063105)
    ·
      refine ⟨796771982139672351047329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1062362642852896468063105 796771982139672351047329)
      ·
        refine ⟨597578986604754263285497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 796771982139672351047329 597578986604754263285497)
        ·
          refine ⟨448184239953565697464123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 597578986604754263285497 448184239953565697464123)
          ·
            refine ⟨672276359930348546196185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448184239953565697464123 672276359930348546196185)
            ·
              refine ⟨504207269947761409647139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 672276359930348546196185 504207269947761409647139)
              ·
                refine ⟨756310904921642114470709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 504207269947761409647139 756310904921642114470709)
                ·
                  refine ⟨70904147336403948231629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 756310904921642114470709 70904147336403948231629)
                  ·
                    rfl

theorem cell20_155346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_155346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155346 prefixEnd_155346 := by exact prefixLift 155346
  have htrace : WordTrace (prefixWord ++ tailWord_155346) baseStart_155346 baseEnd_155346 := by
    simpa [prefixWord, tailWord_155346, baseEnd_155346] using wordTrace_append hprefix tailTrace_155346
  have hstable : (prefixWord ++ tailWord_155346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155346).length < 2 ^ (prefixWord ++ tailWord_155346).sum := by decide
  have hdescent : baseEnd_155346 < baseStart_155346 := by decide
  rcases family_descends (prefixWord ++ tailWord_155346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155353 : List Nat := [1, 2, 1, 2, 3, 3, 3, 1, 4]
def baseStart_155353 : Nat := 118140960795 + 155353 * 2 ^ 59
def prefixEnd_155353 : Nat := 4983230072969 + 3 ^ 40 * 155353 * 2
def baseEnd_155353 : Nat := 70907342327143034998267

theorem tailTrace_155353 : CollatzResearch.WordTrace tailWord_155353 prefixEnd_155353 70907342327143034998267 := by
  unfold tailWord_155353
  simp only [CollatzResearch.WordTrace]
  refine ⟨5666189406190088025174713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3777459604126725350116475 5666189406190088025174713)
  ·
    refine ⟨4249642054642566018881035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5666189406190088025174713 4249642054642566018881035)
    ·
      refine ⟨6374463081963849028321553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4249642054642566018881035 6374463081963849028321553)
      ·
        refine ⟨4780847311472886771241165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6374463081963849028321553 4780847311472886771241165)
        ·
          refine ⟨1792817741802332539215437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4780847311472886771241165 1792817741802332539215437)
          ·
            refine ⟨672306653175874702205789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1792817741802332539215437 672306653175874702205789)
            ·
              refine ⟨252114994940953013327171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 672306653175874702205789 252114994940953013327171)
              ·
                refine ⟨378172492411429519990757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252114994940953013327171 378172492411429519990757)
                ·
                  refine ⟨70907342327143034998267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 378172492411429519990757 70907342327143034998267)
                  ·
                    rfl

theorem cell20_155353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_155353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155353 prefixEnd_155353 := by exact prefixLift 155353
  have htrace : WordTrace (prefixWord ++ tailWord_155353) baseStart_155353 baseEnd_155353 := by
    simpa [prefixWord, tailWord_155353, baseEnd_155353] using wordTrace_append hprefix tailTrace_155353
  have hstable : (prefixWord ++ tailWord_155353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155353).length < 2 ^ (prefixWord ++ tailWord_155353).sum := by decide
  have hdescent : baseEnd_155353 < baseStart_155353 := by decide
  rcases family_descends (prefixWord ++ tailWord_155353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155356 : List Nat := [2, 2, 5, 1, 2, 1, 2, 5]
def baseStart_155356 : Nat := 118140960795 + 155356 * 2 ^ 59
def prefixEnd_155356 : Nat := 4983230072969 + 3 ^ 40 * 155356 * 2
def baseEnd_155356 : Nat := 23636237202962785966085

theorem tailTrace_155356 : CollatzResearch.WordTrace tailWord_155356 prefixEnd_155356 23636237202962785966085 := by
  unfold tailWord_155356
  simp only [CollatzResearch.WordTrace]
  refine ⟨2833149412589609768766961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3777532550119479691689281 2833149412589609768766961)
  ·
    refine ⟨2124862059442207326575221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2833149412589609768766961 2124862059442207326575221)
    ·
      refine ⟨199205818072706936866427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2124862059442207326575221 199205818072706936866427)
      ·
        refine ⟨298808727109060405299641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199205818072706936866427 298808727109060405299641)
        ·
          refine ⟨224106545331795303974731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298808727109060405299641 224106545331795303974731)
          ·
            refine ⟨336159817997692955962097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224106545331795303974731 336159817997692955962097)
            ·
              refine ⟨252119863498269716971573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 336159817997692955962097 252119863498269716971573)
              ·
                refine ⟨23636237202962785966085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 252119863498269716971573 23636237202962785966085)
                ·
                  rfl

theorem cell20_155356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 5].length) (baseStart_155356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155356 prefixEnd_155356 := by exact prefixLift 155356
  have htrace : WordTrace (prefixWord ++ tailWord_155356) baseStart_155356 baseEnd_155356 := by
    simpa [prefixWord, tailWord_155356, baseEnd_155356] using wordTrace_append hprefix tailTrace_155356
  have hstable : (prefixWord ++ tailWord_155356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155356).length < 2 ^ (prefixWord ++ tailWord_155356).sum := by decide
  have hdescent : baseEnd_155356 < baseStart_155356 := by decide
  rcases family_descends (prefixWord ++ tailWord_155356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155363 : List Nat := [1, 1, 1, 7, 2, 1, 1, 3, 3]
def baseStart_155363 : Nat := 118140960795 + 155363 * 2 ^ 59
def prefixEnd_155363 : Nat := 4983230072969 + 3 ^ 40 * 155363 * 2
def baseEnd_155363 : Nat := 70911906599627444664893

theorem tailTrace_155363 : CollatzResearch.WordTrace tailWord_155363 prefixEnd_155363 70911906599627444664893 := by
  unfold tailWord_155363
  simp only [CollatzResearch.WordTrace]
  refine ⟨5666554136153859733038743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3777702757435906488692495 5666554136153859733038743)
  ·
    refine ⟨8499831204230789599558115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5666554136153859733038743 8499831204230789599558115)
    ·
      refine ⟨12749746806346184399337173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8499831204230789599558115 12749746806346184399337173)
      ·
        refine ⟨298822190773738696859465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 12749746806346184399337173 298822190773738696859465)
        ·
          refine ⟨224116643080304022644599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298822190773738696859465 224116643080304022644599)
          ·
            refine ⟨336174964620456033966899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224116643080304022644599 336174964620456033966899)
            ·
              refine ⟨504262446930684050950349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336174964620456033966899 504262446930684050950349)
              ·
                refine ⟨189098417599006519106381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 504262446930684050950349 189098417599006519106381)
                ·
                  refine ⟨70911906599627444664893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189098417599006519106381 70911906599627444664893)
                  ·
                    rfl

theorem cell20_155363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 3].length) (baseStart_155363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155363 prefixEnd_155363 := by exact prefixLift 155363
  have htrace : WordTrace (prefixWord ++ tailWord_155363) baseStart_155363 baseEnd_155363 := by
    simpa [prefixWord, tailWord_155363, baseEnd_155363] using wordTrace_append hprefix tailTrace_155363
  have hstable : (prefixWord ++ tailWord_155363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155363).length < 2 ^ (prefixWord ++ tailWord_155363).sum := by decide
  have hdescent : baseEnd_155363 < baseStart_155363 := by decide
  rcases family_descends (prefixWord ++ tailWord_155363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155415 : List Nat := [1, 1, 3, 4, 2, 3, 1, 5]
def baseStart_155415 : Nat := 118140960795 + 155415 * 2 ^ 59
def prefixEnd_155415 : Nat := 4983230072969 + 3 ^ 40 * 155415 * 2
def baseEnd_155415 : Nat := 23645213605515458310449

theorem tailTrace_155415 : CollatzResearch.WordTrace tailWord_155415 prefixEnd_155415 23645213605515458310449 := by
  unfold tailWord_155415
  simp only [CollatzResearch.WordTrace]
  refine ⟨5668450731965472613931699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3778967154643648409287799 5668450731965472613931699)
  ·
    refine ⟨8502676097948208920897549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5668450731965472613931699 8502676097948208920897549)
    ·
      refine ⟨3188503536730578345336581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8502676097948208920897549 3188503536730578345336581)
      ·
        refine ⟨597844413136983439750609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3188503536730578345336581 597844413136983439750609)
        ·
          refine ⟨448383309852737579812957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 597844413136983439750609 448383309852737579812957)
          ·
            refine ⟨168143741194776592429859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 448383309852737579812957 168143741194776592429859)
            ·
              refine ⟨252215611792164888644789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168143741194776592429859 252215611792164888644789)
              ·
                refine ⟨23645213605515458310449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 252215611792164888644789 23645213605515458310449)
                ·
                  rfl

theorem cell20_155415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 5].length) (baseStart_155415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155415 prefixEnd_155415 := by exact prefixLift 155415
  have htrace : WordTrace (prefixWord ++ tailWord_155415) baseStart_155415 baseEnd_155415 := by
    simpa [prefixWord, tailWord_155415, baseEnd_155415] using wordTrace_append hprefix tailTrace_155415
  have hstable : (prefixWord ++ tailWord_155415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155415).length < 2 ^ (prefixWord ++ tailWord_155415).sum := by decide
  have hdescent : baseEnd_155415 < baseStart_155415 := by decide
  rcases family_descends (prefixWord ++ tailWord_155415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155429 : List Nat := [1, 3, 1, 2, 3, 3, 1, 2, 4]
def baseStart_155429 : Nat := 118140960795 + 155429 * 2 ^ 59
def prefixEnd_155429 : Nat := 4983230072969 + 3 ^ 40 * 155429 * 2
def baseEnd_155429 : Nat := 70942030798024548464623

theorem tailTrace_155429 : CollatzResearch.WordTrace tailWord_155429 prefixEnd_155429 70942030798024548464623 := by
  unfold tailWord_155429
  simp only [CollatzResearch.WordTrace]
  refine ⟨5668961353914753004941341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3779307569276502003294227 5668961353914753004941341)
  ·
    refine ⟨2125860507718032376853003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5668961353914753004941341 2125860507718032376853003)
    ·
      refine ⟨3188790761577048565279505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2125860507718032376853003 3188790761577048565279505)
      ·
        refine ⟨2391593071182786423959629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3188790761577048565279505 2391593071182786423959629)
        ·
          refine ⟨896847401693544908984861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2391593071182786423959629 896847401693544908984861)
          ·
            refine ⟨336317775635079340869323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 896847401693544908984861 336317775635079340869323)
            ·
              refine ⟨504476663452619011303985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336317775635079340869323 504476663452619011303985)
              ·
                refine ⟨378357497589464258477989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 504476663452619011303985 378357497589464258477989)
                ·
                  refine ⟨70942030798024548464623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 378357497589464258477989 70942030798024548464623)
                  ·
                    rfl

theorem cell20_155429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_155429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155429 prefixEnd_155429 := by exact prefixLift 155429
  have htrace : WordTrace (prefixWord ++ tailWord_155429) baseStart_155429 baseEnd_155429 := by
    simpa [prefixWord, tailWord_155429, baseEnd_155429] using wordTrace_append hprefix tailTrace_155429
  have hstable : (prefixWord ++ tailWord_155429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155429).length < 2 ^ (prefixWord ++ tailWord_155429).sum := by decide
  have hdescent : baseEnd_155429 < baseStart_155429 := by decide
  rcases family_descends (prefixWord ++ tailWord_155429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155477 : List Nat := [1, 3, 2, 2, 2, 3, 3, 1, 3]
def baseStart_155477 : Nat := 118140960795 + 155477 * 2 ^ 59
def prefixEnd_155477 : Nat := 4983230072969 + 3 ^ 40 * 155477 * 2
def baseEnd_155477 : Nat := 70963939305949714864427

theorem tailTrace_155477 : CollatzResearch.WordTrace tailWord_155477 prefixEnd_155477 70963939305949714864427 := by
  unfold tailWord_155477
  simp only [CollatzResearch.WordTrace]
  refine ⟨5670712057740857202688685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3780474705160571468459123 5670712057740857202688685)
  ·
    refine ⟨2126517021652821451008257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5670712057740857202688685 2126517021652821451008257)
    ·
      refine ⟨1594887766239616088256193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2126517021652821451008257 1594887766239616088256193)
      ·
        refine ⟨1196165824679712066192145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1594887766239616088256193 1196165824679712066192145)
        ·
          refine ⟨897124368509784049644109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1196165824679712066192145 897124368509784049644109)
          ·
            refine ⟨336421638191169018616541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 897124368509784049644109 336421638191169018616541)
            ·
              refine ⟨126158114321688381981203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 336421638191169018616541 126158114321688381981203)
              ·
                refine ⟨189237171482532572971805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126158114321688381981203 189237171482532572971805)
                ·
                  refine ⟨70963939305949714864427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189237171482532572971805 70963939305949714864427)
                  ·
                    rfl

theorem cell20_155477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_155477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155477 prefixEnd_155477 := by exact prefixLift 155477
  have htrace : WordTrace (prefixWord ++ tailWord_155477) baseStart_155477 baseEnd_155477 := by
    simpa [prefixWord, tailWord_155477, baseEnd_155477] using wordTrace_append hprefix tailTrace_155477
  have hstable : (prefixWord ++ tailWord_155477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155477).length < 2 ^ (prefixWord ++ tailWord_155477).sum := by decide
  have hdescent : baseEnd_155477 < baseStart_155477 := by decide
  rcases family_descends (prefixWord ++ tailWord_155477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155519 : List Nat := [1, 1, 2, 2, 1, 1, 3, 6, 3]
def baseStart_155519 : Nat := 118140960795 + 155519 * 2 ^ 59
def prefixEnd_155519 : Nat := 4983230072969 + 3 ^ 40 * 155519 * 2
def baseEnd_155519 : Nat := 70983109250384235464255

theorem tailTrace_155519 : CollatzResearch.WordTrace tailWord_155519 prefixEnd_155519 70983109250384235464255 := by
  unfold tailWord_155519
  simp only [CollatzResearch.WordTrace]
  refine ⟨5672243923588698375717611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3781495949059132250478407 5672243923588698375717611)
  ·
    refine ⟨8508365885383047563576417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5672243923588698375717611 8508365885383047563576417)
    ·
      refine ⟨6381274414037285672682313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8508365885383047563576417 6381274414037285672682313)
      ·
        refine ⟨4785955810527964254511735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6381274414037285672682313 4785955810527964254511735)
        ·
          refine ⟨7178933715791946381767603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4785955810527964254511735 7178933715791946381767603)
          ·
            refine ⟨10768400573687919572651405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7178933715791946381767603 10768400573687919572651405)
            ·
              refine ⟨4038150215132969839744277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10768400573687919572651405 4038150215132969839744277)
              ·
                refine ⟨189288291334357961238013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4038150215132969839744277 189288291334357961238013)
                ·
                  refine ⟨70983109250384235464255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189288291334357961238013 70983109250384235464255)
                  ·
                    rfl

theorem cell20_155519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 3].length) (baseStart_155519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155519 prefixEnd_155519 := by exact prefixLift 155519
  have htrace : WordTrace (prefixWord ++ tailWord_155519) baseStart_155519 baseEnd_155519 := by
    simpa [prefixWord, tailWord_155519, baseEnd_155519] using wordTrace_append hprefix tailTrace_155519
  have hstable : (prefixWord ++ tailWord_155519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155519).length < 2 ^ (prefixWord ++ tailWord_155519).sum := by decide
  have hdescent : baseEnd_155519 < baseStart_155519 := by decide
  rcases family_descends (prefixWord ++ tailWord_155519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155595 : List Nat := [1, 1, 1, 1, 3, 4, 1, 5, 3]
def baseStart_155595 : Nat := 118140960795 + 155595 * 2 ^ 59
def prefixEnd_155595 : Nat := 4983230072969 + 3 ^ 40 * 155595 * 2
def baseEnd_155595 : Nat := 71017797721265748930611

theorem tailTrace_155595 : CollatzResearch.WordTrace tailWord_155595 prefixEnd_155595 71017797721265748930611 := by
  unfold tailWord_155595
  simp only [CollatzResearch.WordTrace]
  refine ⟨5675015871313363355484239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3783343914208908903656159 5675015871313363355484239)
  ·
    refine ⟨8512523806970045033226359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5675015871313363355484239 8512523806970045033226359)
    ·
      refine ⟨12768785710455067549839539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8512523806970045033226359 12768785710455067549839539)
      ·
        refine ⟨19153178565682601324759309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12768785710455067549839539 19153178565682601324759309)
        ·
          refine ⟨7182441962130975496784741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19153178565682601324759309 7182441962130975496784741)
          ·
            refine ⟨1346707867899557905647139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7182441962130975496784741 1346707867899557905647139)
            ·
              refine ⟨2020061801849336858470709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1346707867899557905647139 2020061801849336858470709)
              ·
                refine ⟨189380793923375330481629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2020061801849336858470709 189380793923375330481629)
                ·
                  refine ⟨71017797721265748930611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189380793923375330481629 71017797721265748930611)
                  ·
                    rfl

theorem cell20_155595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 3].length) (baseStart_155595 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155595 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155595 prefixEnd_155595 := by exact prefixLift 155595
  have htrace : WordTrace (prefixWord ++ tailWord_155595) baseStart_155595 baseEnd_155595 := by
    simpa [prefixWord, tailWord_155595, baseEnd_155595] using wordTrace_append hprefix tailTrace_155595
  have hstable : (prefixWord ++ tailWord_155595).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155595).length < 2 ^ (prefixWord ++ tailWord_155595).sum := by decide
  have hdescent : baseEnd_155595 < baseStart_155595 := by decide
  rcases family_descends (prefixWord ++ tailWord_155595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155605 : List Nat := [1, 3, 2, 3, 2, 2, 3, 4]
def baseStart_155605 : Nat := 118140960795 + 155605 * 2 ^ 59
def prefixEnd_155605 : Nat := 4983230072969 + 3 ^ 40 * 155605 * 2
def baseEnd_155605 : Nat := 23674120664583386199079

theorem tailTrace_155605 : CollatzResearch.WordTrace tailWord_155605 prefixEnd_155605 23674120664583386199079 := by
  unfold tailWord_155605
  simp only [CollatzResearch.WordTrace]
  refine ⟨5675380601277135063348269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3783587067518090042232179 5675380601277135063348269)
  ·
    refine ⟨2128267725478925648755601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5675380601277135063348269 2128267725478925648755601)
    ·
      refine ⟨1596200794109194236566701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2128267725478925648755601 1596200794109194236566701)
      ·
        refine ⟨598575297790947838712513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1596200794109194236566701 598575297790947838712513)
        ·
          refine ⟨448931473343210879034385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 598575297790947838712513 448931473343210879034385)
          ·
            refine ⟨336698605007408159275789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 448931473343210879034385 336698605007408159275789)
            ·
              refine ⟨126261976877778059728421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 336698605007408159275789 126261976877778059728421)
              ·
                refine ⟨23674120664583386199079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126261976877778059728421 23674120664583386199079)
                ·
                  rfl

theorem cell20_155605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 4].length) (baseStart_155605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155605 prefixEnd_155605 := by exact prefixLift 155605
  have htrace : WordTrace (prefixWord ++ tailWord_155605) baseStart_155605 baseEnd_155605 := by
    simpa [prefixWord, tailWord_155605, baseEnd_155605] using wordTrace_append hprefix tailTrace_155605
  have hstable : (prefixWord ++ tailWord_155605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155605).length < 2 ^ (prefixWord ++ tailWord_155605).sum := by decide
  have hdescent : baseEnd_155605 < baseStart_155605 := by decide
  rcases family_descends (prefixWord ++ tailWord_155605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155629 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 5]
def baseStart_155629 : Nat := 118140960795 + 155629 * 2 ^ 59
def prefixEnd_155629 : Nat := 4983230072969 + 3 ^ 40 * 155629 * 2
def baseEnd_155629 : Nat := 71033316247712741797139

theorem tailTrace_155629 : CollatzResearch.WordTrace tailWord_155629 prefixEnd_155629 71033316247712741797139 := by
  unfold tailWord_155629
  simp only [CollatzResearch.WordTrace]
  refine ⟨5676255953190187162221941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3784170635460124774814627 5676255953190187162221941)
  ·
    refine ⟨532148995611580046458307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5676255953190187162221941 532148995611580046458307)
    ·
      refine ⟨798223493417370069687461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 532148995611580046458307 798223493417370069687461)
      ·
        refine ⟨149666905015756888066399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 798223493417370069687461 149666905015756888066399)
        ·
          refine ⟨224500357523635332099599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149666905015756888066399 224500357523635332099599)
          ·
            refine ⟨336750536285452998149399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224500357523635332099599 336750536285452998149399)
            ·
              refine ⟨505125804428179497224099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336750536285452998149399 505125804428179497224099)
              ·
                refine ⟨757688706642269245836149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505125804428179497224099 757688706642269245836149)
                ·
                  refine ⟨71033316247712741797139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 757688706642269245836149 71033316247712741797139)
                  ·
                    rfl

theorem cell20_155629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_155629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155629 prefixEnd_155629 := by exact prefixLift 155629
  have htrace : WordTrace (prefixWord ++ tailWord_155629) baseStart_155629 baseEnd_155629 := by
    simpa [prefixWord, tailWord_155629, baseEnd_155629] using wordTrace_append hprefix tailTrace_155629
  have hstable : (prefixWord ++ tailWord_155629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155629).length < 2 ^ (prefixWord ++ tailWord_155629).sum := by decide
  have hdescent : baseEnd_155629 < baseStart_155629 := by decide
  rcases family_descends (prefixWord ++ tailWord_155629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155640 : List Nat := [2, 1, 2, 1, 1, 3, 3, 3, 4]
def baseStart_155640 : Nat := 118140960795 + 155640 * 2 ^ 59
def prefixEnd_155640 : Nat := 4983230072969 + 3 ^ 40 * 155640 * 2
def baseEnd_155640 : Nat := 71038336947445592430427

theorem tailTrace_155640 : CollatzResearch.WordTrace tailWord_155640 prefixEnd_155640 71038336947445592430427 := by
  unfold tailWord_155640
  simp only [CollatzResearch.WordTrace]
  refine ⟨2838328578075168020436187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3784438104100224027248249 2838328578075168020436187)
  ·
    refine ⟨4257492867112752030654281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2838328578075168020436187 4257492867112752030654281)
    ·
      refine ⟨3193119650334564022990711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4257492867112752030654281 3193119650334564022990711)
      ·
        refine ⟨4789679475501846034486067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3193119650334564022990711 4789679475501846034486067)
        ·
          refine ⟨7184519213252769051729101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4789679475501846034486067 7184519213252769051729101)
          ·
            refine ⟨2694194704969788394398413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7184519213252769051729101 2694194704969788394398413)
            ·
              refine ⟨1010323014363670647899405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2694194704969788394398413 1010323014363670647899405)
              ·
                refine ⟨378871130386376492962277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1010323014363670647899405 378871130386376492962277)
                ·
                  refine ⟨71038336947445592430427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 378871130386376492962277 71038336947445592430427)
                  ·
                    rfl

theorem cell20_155640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_155640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155640 prefixEnd_155640 := by exact prefixLift 155640
  have htrace : WordTrace (prefixWord ++ tailWord_155640) baseStart_155640 baseEnd_155640 := by
    simpa [prefixWord, tailWord_155640, baseEnd_155640] using wordTrace_append hprefix tailTrace_155640
  have hstable : (prefixWord ++ tailWord_155640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155640).length < 2 ^ (prefixWord ++ tailWord_155640).sum := by decide
  have hdescent : baseEnd_155640 < baseStart_155640 := by decide
  rcases family_descends (prefixWord ++ tailWord_155640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155646 : List Nat := [4, 2, 2, 2, 1, 2, 3, 1, 3]
def baseStart_155646 : Nat := 118140960795 + 155646 * 2 ^ 59
def prefixEnd_155646 : Nat := 4983230072969 + 3 ^ 40 * 155646 * 2
def baseEnd_155646 : Nat := 71041075510936238230403

theorem tailTrace_155646 : CollatzResearch.WordTrace tailWord_155646 prefixEnd_155646 71041075510936238230403 := by
  unfold tailWord_155646
  simp only [CollatzResearch.WordTrace]
  refine ⟨709609499266074883198849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3784583996085732710393861 709609499266074883198849)
  ·
    refine ⟨532207124449556162399137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 709609499266074883198849 532207124449556162399137)
    ·
      refine ⟨399155343337167121799353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 532207124449556162399137 399155343337167121799353)
      ·
        refine ⟨299366507502875341349515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 399155343337167121799353 299366507502875341349515)
        ·
          refine ⟨449049761254313012024273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299366507502875341349515 449049761254313012024273)
          ·
            refine ⟨336787320940734759018205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 449049761254313012024273 336787320940734759018205)
            ·
              refine ⟨126295245352775534631827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 336787320940734759018205 126295245352775534631827)
              ·
                refine ⟨189442868029163301947741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126295245352775534631827 189442868029163301947741)
                ·
                  refine ⟨71041075510936238230403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189442868029163301947741 71041075510936238230403)
                  ·
                    rfl

theorem cell20_155646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_155646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155646 prefixEnd_155646 := by exact prefixLift 155646
  have htrace : WordTrace (prefixWord ++ tailWord_155646) baseStart_155646 baseEnd_155646 := by
    simpa [prefixWord, tailWord_155646, baseEnd_155646] using wordTrace_append hprefix tailTrace_155646
  have hstable : (prefixWord ++ tailWord_155646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155646).length < 2 ^ (prefixWord ++ tailWord_155646).sum := by decide
  have hdescent : baseEnd_155646 < baseStart_155646 := by decide
  rcases family_descends (prefixWord ++ tailWord_155646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155674 : List Nat := [3, 1, 1, 3, 1, 3, 3, 3, 2]
def baseStart_155674 : Nat := 118140960795 + 155674 * 2 ^ 59
def prefixEnd_155674 : Nat := 4983230072969 + 3 ^ 40 * 155674 * 2
def baseEnd_155674 : Nat := 71053855473892585296955

theorem tailTrace_155674 : CollatzResearch.WordTrace tailWord_155674 prefixEnd_155674 71053855473892585296955 := by
  unfold tailWord_155674
  simp only [CollatzResearch.WordTrace]
  refine ⟨1419474309506789961902519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3785264825351439898406717 1419474309506789961902519)
  ·
    refine ⟨2129211464260184942853779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1419474309506789961902519 2129211464260184942853779)
    ·
      refine ⟨3193817196390277414280669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2129211464260184942853779 3193817196390277414280669)
      ·
        refine ⟨1197681448646354030355251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3193817196390277414280669 1197681448646354030355251)
        ·
          refine ⟨1796522172969531045532877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1197681448646354030355251 1796522172969531045532877)
          ·
            refine ⟨673695814863574142074829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1796522172969531045532877 673695814863574142074829)
            ·
              refine ⟨252635930573840303278061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 673695814863574142074829 252635930573840303278061)
              ·
                refine ⟨94738473965190113729273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 252635930573840303278061 94738473965190113729273)
                ·
                  refine ⟨71053855473892585296955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94738473965190113729273 71053855473892585296955)
                  ·
                    rfl

theorem cell20_155674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 2].length) (baseStart_155674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155674 prefixEnd_155674 := by exact prefixLift 155674
  have htrace : WordTrace (prefixWord ++ tailWord_155674) baseStart_155674 baseEnd_155674 := by
    simpa [prefixWord, tailWord_155674, baseEnd_155674] using wordTrace_append hprefix tailTrace_155674
  have hstable : (prefixWord ++ tailWord_155674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155674).length < 2 ^ (prefixWord ++ tailWord_155674).sum := by decide
  have hdescent : baseEnd_155674 < baseStart_155674 := by decide
  rcases family_descends (prefixWord ++ tailWord_155674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155681 : List Nat := [1, 2, 3, 2, 5, 1, 6]
def baseStart_155681 : Nat := 118140960795 + 155681 * 2 ^ 59
def prefixEnd_155681 : Nat := 4983230072969 + 3 ^ 40 * 155681 * 2
def baseEnd_155681 : Nat := 7895227829403519118177

theorem tailTrace_155681 : CollatzResearch.WordTrace tailWord_155681 prefixEnd_155681 7895227829403519118177 := by
  unfold tailWord_155681
  simp only [CollatzResearch.WordTrace]
  refine ⟨5678152549001800043114897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3785435032667866695409931 5678152549001800043114897)
  ·
    refine ⟨4258614411751350032336173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5678152549001800043114897 4258614411751350032336173)
    ·
      refine ⟨1596980404406756262126065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4258614411751350032336173 1596980404406756262126065)
      ·
        refine ⟨1197735303305067196594549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1596980404406756262126065 1197735303305067196594549)
        ·
          refine ⟨112287684684850049680739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1197735303305067196594549 112287684684850049680739)
          ·
            refine ⟨168431527027275074521109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112287684684850049680739 168431527027275074521109)
            ·
              refine ⟨7895227829403519118177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 168431527027275074521109 7895227829403519118177)
              ·
                rfl

theorem cell20_155681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 6].length) (baseStart_155681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155681 prefixEnd_155681 := by exact prefixLift 155681
  have htrace : WordTrace (prefixWord ++ tailWord_155681) baseStart_155681 baseEnd_155681 := by
    simpa [prefixWord, tailWord_155681, baseEnd_155681] using wordTrace_append hprefix tailTrace_155681
  have hstable : (prefixWord ++ tailWord_155681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155681).length < 2 ^ (prefixWord ++ tailWord_155681).sum := by decide
  have hdescent : baseEnd_155681 < baseStart_155681 := by decide
  rcases family_descends (prefixWord ++ tailWord_155681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155685 : List Nat := [1, 3, 1, 2, 2, 3, 8]
def baseStart_155685 : Nat := 118140960795 + 155685 * 2 ^ 59
def prefixEnd_155685 : Nat := 4983230072969 + 3 ^ 40 * 155685 * 2
def baseEnd_155685 : Nat := 7895430685958381770027

theorem tailTrace_155685 : CollatzResearch.WordTrace tailWord_155685 prefixEnd_155685 7895430685958381770027 := by
  unfold tailWord_155685
  simp only [CollatzResearch.WordTrace]
  refine ⟨5678298440987308726260509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3785532293991539150840339 5678298440987308726260509)
  ·
    refine ⟨2129361915370240772347691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5678298440987308726260509 2129361915370240772347691)
    ·
      refine ⟨3194042873055361158521537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2129361915370240772347691 3194042873055361158521537)
      ·
        refine ⟨2395532154791520868891153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3194042873055361158521537 2395532154791520868891153)
        ·
          refine ⟨1796649116093640651668365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2395532154791520868891153 1796649116093640651668365)
          ·
            refine ⟨673743418535115244375637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1796649116093640651668365 673743418535115244375637)
            ·
              refine ⟨7895430685958381770027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 673743418535115244375637 7895430685958381770027)
              ·
                rfl

theorem cell20_155685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 8].length) (baseStart_155685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155685 prefixEnd_155685 := by exact prefixLift 155685
  have htrace : WordTrace (prefixWord ++ tailWord_155685) baseStart_155685 baseEnd_155685 := by
    simpa [prefixWord, tailWord_155685, baseEnd_155685] using wordTrace_append hprefix tailTrace_155685
  have hstable : (prefixWord ++ tailWord_155685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155685).length < 2 ^ (prefixWord ++ tailWord_155685).sum := by decide
  have hdescent : baseEnd_155685 < baseStart_155685 := by decide
  rcases family_descends (prefixWord ++ tailWord_155685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155742 : List Nat := [4, 4, 1, 1, 2, 2, 2, 2, 2]
def baseStart_155742 : Nat := 118140960795 + 155742 * 2 ^ 59
def prefixEnd_155742 : Nat := 4983230072969 + 3 ^ 40 * 155742 * 2
def baseEnd_155742 : Nat := 71084892526786571030011

theorem tailTrace_155742 : CollatzResearch.WordTrace tailWord_155742 prefixEnd_155742 71084892526786571030011 := by
  unfold tailWord_155742
  simp only [CollatzResearch.WordTrace]
  refine ⟨710047175222600932635685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3786918267853871640723653 710047175222600932635685)
  ·
    refine ⟨133133845354237674869191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 710047175222600932635685 133133845354237674869191)
    ·
      refine ⟨199700768031356512303787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133133845354237674869191 199700768031356512303787)
      ·
        refine ⟨299551152047034768455681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199700768031356512303787 299551152047034768455681)
        ·
          refine ⟨224663364035276076341761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299551152047034768455681 224663364035276076341761)
          ·
            refine ⟨168497523026457057256321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224663364035276076341761 168497523026457057256321)
            ·
              refine ⟨126373142269842792942241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168497523026457057256321 126373142269842792942241)
              ·
                refine ⟨94779856702382094706681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126373142269842792942241 94779856702382094706681)
                ·
                  refine ⟨71084892526786571030011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94779856702382094706681 71084892526786571030011)
                  ·
                    rfl

theorem cell20_155742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_155742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155742 prefixEnd_155742 := by exact prefixLift 155742
  have htrace : WordTrace (prefixWord ++ tailWord_155742) baseStart_155742 baseEnd_155742 := by
    simpa [prefixWord, tailWord_155742, baseEnd_155742] using wordTrace_append hprefix tailTrace_155742
  have hstable : (prefixWord ++ tailWord_155742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155742).length < 2 ^ (prefixWord ++ tailWord_155742).sum := by decide
  have hdescent : baseEnd_155742 < baseStart_155742 := by decide
  rcases family_descends (prefixWord ++ tailWord_155742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155747 : List Nat := [1, 1, 1, 5, 1, 1, 3, 4, 3]
def baseStart_155747 : Nat := 118140960795 + 155747 * 2 ^ 59
def prefixEnd_155747 : Nat := 4983230072969 + 3 ^ 40 * 155747 * 2
def baseEnd_155747 : Nat := 71087174663028775863323

theorem tailTrace_155747 : CollatzResearch.WordTrace tailWord_155747 prefixEnd_155747 71087174663028775863323 := by
  unfold tailWord_155747
  simp only [CollatzResearch.WordTrace]
  refine ⟨5680559766762693315017495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3787039844508462210011663 5680559766762693315017495)
  ·
    refine ⟨8520839650144039972526243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5680559766762693315017495 8520839650144039972526243)
    ·
      refine ⟨12781259475216059958789365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8520839650144039972526243 12781259475216059958789365)
      ·
        refine ⟨1198243075801505621136503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12781259475216059958789365 1198243075801505621136503)
        ·
          refine ⟨1797364613702258431704755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1198243075801505621136503 1797364613702258431704755)
          ·
            refine ⟨2696046920553387647557133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1797364613702258431704755 2696046920553387647557133)
            ·
              refine ⟨1011017595207520367833925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2696046920553387647557133 1011017595207520367833925)
              ·
                refine ⟨189565799101410068968861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1011017595207520367833925 189565799101410068968861)
                ·
                  refine ⟨71087174663028775863323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189565799101410068968861 71087174663028775863323)
                  ·
                    rfl

theorem cell20_155747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 3].length) (baseStart_155747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155747 prefixEnd_155747 := by exact prefixLift 155747
  have htrace : WordTrace (prefixWord ++ tailWord_155747) baseStart_155747 baseEnd_155747 := by
    simpa [prefixWord, tailWord_155747, baseEnd_155747] using wordTrace_append hprefix tailTrace_155747
  have hstable : (prefixWord ++ tailWord_155747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155747).length < 2 ^ (prefixWord ++ tailWord_155747).sum := by decide
  have hdescent : baseEnd_155747 < baseStart_155747 := by decide
  rcases family_descends (prefixWord ++ tailWord_155747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155768 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 7]
def baseStart_155768 : Nat := 118140960795 + 155768 * 2 ^ 59
def prefixEnd_155768 : Nat := 4983230072969 + 3 ^ 40 * 155768 * 2
def baseEnd_155768 : Nat := 71096759635246036163237

theorem tailTrace_155768 : CollatzResearch.WordTrace tailWord_155768 prefixEnd_155768 71096759635246036163237 := by
  unfold tailWord_155768
  simp only [CollatzResearch.WordTrace]
  refine ⟨2840662849843306950765979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3787550466457742601021305 2840662849843306950765979)
  ·
    refine ⟨4260994274764960426148969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2840662849843306950765979 4260994274764960426148969)
    ·
      refine ⟨3195745706073720319611727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4260994274764960426148969 3195745706073720319611727)
      ·
        refine ⟨4793618559110580479417591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3195745706073720319611727 4793618559110580479417591)
        ·
          refine ⟨7190427838665870719126387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4793618559110580479417591 7190427838665870719126387)
          ·
            refine ⟨10785641757998806078689581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7190427838665870719126387 10785641757998806078689581)
            ·
              refine ⟨4044615659249552279508593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10785641757998806078689581 4044615659249552279508593)
              ·
                refine ⟨3033461744437164209631445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4044615659249552279508593 3033461744437164209631445)
                ·
                  refine ⟨71096759635246036163237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3033461744437164209631445 71096759635246036163237)
                  ·
                    rfl

theorem cell20_155768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_155768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155768 prefixEnd_155768 := by exact prefixLift 155768
  have htrace : WordTrace (prefixWord ++ tailWord_155768) baseStart_155768 baseEnd_155768 := by
    simpa [prefixWord, tailWord_155768, baseEnd_155768] using wordTrace_append hprefix tailTrace_155768
  have hstable : (prefixWord ++ tailWord_155768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155768).length < 2 ^ (prefixWord ++ tailWord_155768).sum := by decide
  have hdescent : baseEnd_155768 < baseStart_155768 := by decide
  rcases family_descends (prefixWord ++ tailWord_155768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155802 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 5]
def baseStart_155802 : Nat := 118140960795 + 155802 * 2 ^ 59
def prefixEnd_155802 : Nat := 4983230072969 + 3 ^ 40 * 155802 * 2
def baseEnd_155802 : Nat := 71112278161693029029765

theorem tailTrace_155802 : CollatzResearch.WordTrace tailWord_155802 prefixEnd_155802 71112278161693029029765 := by
  unfold tailWord_155802
  simp only [CollatzResearch.WordTrace]
  refine ⟨1420641445390859427067415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3788377187708958472179773 1420641445390859427067415)
  ·
    refine ⟨2130962168086289140601123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1420641445390859427067415 2130962168086289140601123)
    ·
      refine ⟨3196443252129433710901685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2130962168086289140601123 3196443252129433710901685)
      ·
        refine ⟨299666554887134410397033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3196443252129433710901685 299666554887134410397033)
        ·
          refine ⟨224749916165350807797775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299666554887134410397033 224749916165350807797775)
          ·
            refine ⟨337124874248026211696663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224749916165350807797775 337124874248026211696663)
            ·
              refine ⟨505687311372039317544995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337124874248026211696663 505687311372039317544995)
              ·
                refine ⟨758530967058058976317493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505687311372039317544995 758530967058058976317493)
                ·
                  refine ⟨71112278161693029029765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 758530967058058976317493 71112278161693029029765)
                  ·
                    rfl

theorem cell20_155802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_155802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155802 prefixEnd_155802 := by exact prefixLift 155802
  have htrace : WordTrace (prefixWord ++ tailWord_155802) baseStart_155802 baseEnd_155802 := by
    simpa [prefixWord, tailWord_155802, baseEnd_155802] using wordTrace_append hprefix tailTrace_155802
  have hstable : (prefixWord ++ tailWord_155802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155802).length < 2 ^ (prefixWord ++ tailWord_155802).sum := by decide
  have hdescent : baseEnd_155802 < baseStart_155802 := by decide
  rcases family_descends (prefixWord ++ tailWord_155802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155809 : List Nat := [1, 2, 3, 3, 1, 3, 2, 1, 4]
def baseStart_155809 : Nat := 118140960795 + 155809 * 2 ^ 59
def prefixEnd_155809 : Nat := 4983230072969 + 3 ^ 40 * 155809 * 2
def baseEnd_155809 : Nat := 71115473152432115796403

theorem tailTrace_155809 : CollatzResearch.WordTrace tailWord_155809 prefixEnd_155809 71115473152432115796403 := by
  unfold tailWord_155809
  simp only [CollatzResearch.WordTrace]
  refine ⟨5682821092538077903774481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3788547395025385269182987 5682821092538077903774481)
  ·
    refine ⟨4262115819403558427830861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5682821092538077903774481 4262115819403558427830861)
    ·
      refine ⟨1598293432276334410436573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4262115819403558427830861 1598293432276334410436573)
      ·
        refine ⟨599360037103625403913715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1598293432276334410436573 599360037103625403913715)
        ·
          refine ⟨899040055655438105870573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 599360037103625403913715 899040055655438105870573)
          ·
            refine ⟨337140020870789289701465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 899040055655438105870573 337140020870789289701465)
            ·
              refine ⟨252855015653091967276099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337140020870789289701465 252855015653091967276099)
              ·
                refine ⟨379282523479637950914149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252855015653091967276099 379282523479637950914149)
                ·
                  refine ⟨71115473152432115796403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 379282523479637950914149 71115473152432115796403)
                  ·
                    rfl

theorem cell20_155809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_155809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155809 prefixEnd_155809 := by exact prefixLift 155809
  have htrace : WordTrace (prefixWord ++ tailWord_155809) baseStart_155809 baseEnd_155809 := by
    simpa [prefixWord, tailWord_155809, baseEnd_155809] using wordTrace_append hprefix tailTrace_155809
  have hstable : (prefixWord ++ tailWord_155809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155809).length < 2 ^ (prefixWord ++ tailWord_155809).sum := by decide
  have hdescent : baseEnd_155809 < baseStart_155809 := by decide
  rcases family_descends (prefixWord ++ tailWord_155809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155829 : List Nat := [1, 3, 3, 4, 2, 1, 2, 4]
def baseStart_155829 : Nat := 118140960795 + 155829 * 2 ^ 59
def prefixEnd_155829 : Nat := 4983230072969 + 3 ^ 40 * 155829 * 2
def baseEnd_155829 : Nat := 23708200565800311709885

theorem tailTrace_155829 : CollatzResearch.WordTrace tailWord_155829 prefixEnd_155829 23708200565800311709885 := by
  unfold tailWord_155829
  simp only [CollatzResearch.WordTrace]
  refine ⟨5683550552465621319502541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3789033701643747546335027 5683550552465621319502541)
  ·
    refine ⟨2131331457174607994813453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5683550552465621319502541 2131331457174607994813453)
    ·
      refine ⟨799249296440477998055045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2131331457174607994813453 799249296440477998055045)
      ·
        refine ⟨149859243082589624635321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 799249296440477998055045 149859243082589624635321)
        ·
          refine ⟨112394432311942218476491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149859243082589624635321 112394432311942218476491)
          ·
            refine ⟨168591648467913327714737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112394432311942218476491 168591648467913327714737)
            ·
              refine ⟨126443736350934995786053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168591648467913327714737 126443736350934995786053)
              ·
                refine ⟨23708200565800311709885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126443736350934995786053 23708200565800311709885)
                ·
                  rfl

theorem cell20_155829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 4].length) (baseStart_155829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155829 prefixEnd_155829 := by exact prefixLift 155829
  have htrace : WordTrace (prefixWord ++ tailWord_155829) baseStart_155829 baseEnd_155829 := by
    simpa [prefixWord, tailWord_155829, baseEnd_155829] using wordTrace_append hprefix tailTrace_155829
  have hstable : (prefixWord ++ tailWord_155829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155829).length < 2 ^ (prefixWord ++ tailWord_155829).sum := by decide
  have hdescent : baseEnd_155829 < baseStart_155829 := by decide
  rcases family_descends (prefixWord ++ tailWord_155829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155854 : List Nat := [4, 1, 1, 1, 4, 3, 6]
def baseStart_155854 : Nat := 118140960795 + 155854 * 2 ^ 59
def prefixEnd_155854 : Nat := 4983230072969 + 3 ^ 40 * 155854 * 2
def baseEnd_155854 : Nat := 7904001375401328810691

theorem tailTrace_155854 : CollatzResearch.WordTrace tailWord_155854 prefixEnd_155854 7904001375401328810691 := by
  unfold tailWord_155854
  simp only [CollatzResearch.WordTrace]
  refine ⟨710557797171881323645327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3789641584916700392775077 710557797171881323645327)
  ·
    refine ⟨1065836695757821985467991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 710557797171881323645327 1065836695757821985467991)
    ·
      refine ⟨1598755043636732978201987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1065836695757821985467991 1598755043636732978201987)
      ·
        refine ⟨2398132565455099467302981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1598755043636732978201987 2398132565455099467302981)
        ·
          refine ⟨449649856022831150119309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2398132565455099467302981 449649856022831150119309)
          ·
            refine ⟨168618696008561681294741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 449649856022831150119309 168618696008561681294741)
            ·
              refine ⟨7904001375401328810691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 168618696008561681294741 7904001375401328810691)
              ·
                rfl

theorem cell20_155854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 6].length) (baseStart_155854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155854 prefixEnd_155854 := by exact prefixLift 155854
  have htrace : WordTrace (prefixWord ++ tailWord_155854) baseStart_155854 baseEnd_155854 := by
    simpa [prefixWord, tailWord_155854, baseEnd_155854] using wordTrace_append hprefix tailTrace_155854
  have hstable : (prefixWord ++ tailWord_155854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155854).length < 2 ^ (prefixWord ++ tailWord_155854).sum := by decide
  have hdescent : baseEnd_155854 < baseStart_155854 := by decide
  rcases family_descends (prefixWord ++ tailWord_155854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155902 : List Nat := [4, 2, 2, 1, 1, 1, 2, 5, 2]
def baseStart_155902 : Nat := 118140960795 + 155902 * 2 ^ 59
def prefixEnd_155902 : Nat := 4983230072969 + 3 ^ 40 * 155902 * 2
def baseEnd_155902 : Nat := 71157920886537125696023

theorem tailTrace_155902 : CollatzResearch.WordTrace tailWord_155902 prefixEnd_155902 71157920886537125696023 := by
  unfold tailWord_155902
  simp only [CollatzResearch.WordTrace]
  refine ⟨710776635150144348363745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3790808720800769857939973 710776635150144348363745)
  ·
    refine ⟨533082476362608261272809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 710776635150144348363745 533082476362608261272809)
    ·
      refine ⟨399811857271956195954607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 533082476362608261272809 399811857271956195954607)
      ·
        refine ⟨599717785907934293931911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399811857271956195954607 599717785907934293931911)
        ·
          refine ⟨899576678861901440897867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 599717785907934293931911 899576678861901440897867)
          ·
            refine ⟨1349365018292852161346801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 899576678861901440897867 1349365018292852161346801)
            ·
              refine ⟨1012023763719639121010101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1349365018292852161346801 1012023763719639121010101)
              ·
                refine ⟨94877227848716167594697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1012023763719639121010101 94877227848716167594697)
                ·
                  refine ⟨71157920886537125696023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94877227848716167594697 71157920886537125696023)
                  ·
                    rfl

theorem cell20_155902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_155902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155902 prefixEnd_155902 := by exact prefixLift 155902
  have htrace : WordTrace (prefixWord ++ tailWord_155902) baseStart_155902 baseEnd_155902 := by
    simpa [prefixWord, tailWord_155902, baseEnd_155902] using wordTrace_append hprefix tailTrace_155902
  have hstable : (prefixWord ++ tailWord_155902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155902).length < 2 ^ (prefixWord ++ tailWord_155902).sum := by decide
  have hdescent : baseEnd_155902 < baseStart_155902 := by decide
  rcases family_descends (prefixWord ++ tailWord_155902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155937 : List Nat := [1, 2, 3, 2, 1, 1, 4, 3, 3]
def baseStart_155937 : Nat := 118140960795 + 155937 * 2 ^ 59
def prefixEnd_155937 : Nat := 4983230072969 + 3 ^ 40 * 155937 * 2
def baseEnd_155937 : Nat := 71173895840232559529213

theorem tailTrace_155937 : CollatzResearch.WordTrace tailWord_155937 prefixEnd_155937 71173895840232559529213 := by
  unfold tailWord_155937
  simp only [CollatzResearch.WordTrace]
  refine ⟨5687489636074355764434065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3791659757382903842956043 5687489636074355764434065)
  ·
    refine ⟨4265617227055766823325549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5687489636074355764434065 4265617227055766823325549)
    ·
      refine ⟨1599606460145912558747081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4265617227055766823325549 1599606460145912558747081)
      ·
        refine ⟨1199704845109434419060311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1599606460145912558747081 1199704845109434419060311)
        ·
          refine ⟨1799557267664151628590467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1199704845109434419060311 1799557267664151628590467)
          ·
            refine ⟨2699335901496227442885701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1799557267664151628590467 2699335901496227442885701)
            ·
              refine ⟨506125481530542645541069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2699335901496227442885701 506125481530542645541069)
              ·
                refine ⟨189797055573953492077901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 506125481530542645541069 189797055573953492077901)
                ·
                  refine ⟨71173895840232559529213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189797055573953492077901 71173895840232559529213)
                  ·
                    rfl

theorem cell20_155937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 3].length) (baseStart_155937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155937 prefixEnd_155937 := by exact prefixLift 155937
  have htrace : WordTrace (prefixWord ++ tailWord_155937) baseStart_155937 baseEnd_155937 := by
    simpa [prefixWord, tailWord_155937, baseEnd_155937] using wordTrace_append hprefix tailTrace_155937
  have hstable : (prefixWord ++ tailWord_155937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155937).length < 2 ^ (prefixWord ++ tailWord_155937).sum := by decide
  have hdescent : baseEnd_155937 < baseStart_155937 := by decide
  rcases family_descends (prefixWord ++ tailWord_155937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155943 : List Nat := [1, 1, 8, 1, 1, 1, 3, 4]
def baseStart_155943 : Nat := 118140960795 + 155943 * 2 ^ 59
def prefixEnd_155943 : Nat := 4983230072969 + 3 ^ 40 * 155943 * 2
def baseEnd_155943 : Nat := 23725544801241068443063

theorem tailTrace_155943 : CollatzResearch.WordTrace tailWord_155943 prefixEnd_155943 23725544801241068443063 := by
  unfold tailWord_155943
  simp only [CollatzResearch.WordTrace]
  refine ⟨5687708474052618789152483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3791805649368412526101655 5687708474052618789152483)
  ·
    refine ⟨8531562711078928183728725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5687708474052618789152483 8531562711078928183728725)
    ·
      refine ⟨99979250520456189653071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 8531562711078928183728725 99979250520456189653071)
      ·
        refine ⟨149968875780684284479607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99979250520456189653071 149968875780684284479607)
        ·
          refine ⟨224953313671026426719411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149968875780684284479607 224953313671026426719411)
          ·
            refine ⟨337429970506539640079117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224953313671026426719411 337429970506539640079117)
            ·
              refine ⟨126536238939952365029669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 337429970506539640079117 126536238939952365029669)
              ·
                refine ⟨23725544801241068443063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126536238939952365029669 23725544801241068443063)
                ·
                  rfl

theorem cell20_155943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 4].length) (baseStart_155943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_155943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_155943 prefixEnd_155943 := by exact prefixLift 155943
  have htrace : WordTrace (prefixWord ++ tailWord_155943) baseStart_155943 baseEnd_155943 := by
    simpa [prefixWord, tailWord_155943, baseEnd_155943] using wordTrace_append hprefix tailTrace_155943
  have hstable : (prefixWord ++ tailWord_155943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155943).length < 2 ^ (prefixWord ++ tailWord_155943).sum := by decide
  have hdescent : baseEnd_155943 < baseStart_155943 := by decide
  rcases family_descends (prefixWord ++ tailWord_155943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156016 : List Nat := [2, 1, 1, 1, 4, 5, 1, 3, 2]
def baseStart_156016 : Nat := 118140960795 + 156016 * 2 ^ 59
def prefixEnd_156016 : Nat := 4983230072969 + 3 ^ 40 * 156016 * 2
def baseEnd_156016 : Nat := 71209953592859395895557

theorem tailTrace_156016 : CollatzResearch.WordTrace tailWord_156016 prefixEnd_156016 71209953592859395895557 := by
  unfold tailWord_156016
  simp only [CollatzResearch.WordTrace]
  refine ⟨2845185501394076128279951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3793580668525434837706601 2845185501394076128279951)
  ·
    refine ⟨4267778252091114192419927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2845185501394076128279951 4267778252091114192419927)
    ·
      refine ⟨6401667378136671288629891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4267778252091114192419927 6401667378136671288629891)
      ·
        refine ⟨9602501067205006932944837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6401667378136671288629891 9602501067205006932944837)
        ·
          refine ⟨1800468950100938799927157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9602501067205006932944837 1800468950100938799927157)
          ·
            refine ⟨168793964071963012493171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1800468950100938799927157 168793964071963012493171)
            ·
              refine ⟨253190946107944518739757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168793964071963012493171 253190946107944518739757)
              ·
                refine ⟨94946604790479194527409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253190946107944518739757 94946604790479194527409)
                ·
                  refine ⟨71209953592859395895557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94946604790479194527409 71209953592859395895557)
                  ·
                    rfl

theorem cell20_156016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 2].length) (baseStart_156016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156016 prefixEnd_156016 := by exact prefixLift 156016
  have htrace : WordTrace (prefixWord ++ tailWord_156016) baseStart_156016 baseEnd_156016 := by
    simpa [prefixWord, tailWord_156016, baseEnd_156016] using wordTrace_append hprefix tailTrace_156016
  have hstable : (prefixWord ++ tailWord_156016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156016).length < 2 ^ (prefixWord ++ tailWord_156016).sum := by decide
  have hdescent : baseEnd_156016 < baseStart_156016 := by decide
  rcases family_descends (prefixWord ++ tailWord_156016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156027 : List Nat := [1, 1, 1, 1, 1, 9, 6]
def baseStart_156027 : Nat := 118140960795 + 156027 * 2 ^ 59
def prefixEnd_156027 : Nat := 4983230072969 + 3 ^ 40 * 156027 * 2
def baseEnd_156027 : Nat := 7912774921399138503205

theorem tailTrace_156027 : CollatzResearch.WordTrace tailWord_156027 prefixEnd_156027 7912774921399138503205 := by
  unfold tailWord_156027
  simp only [CollatzResearch.WordTrace]
  refine ⟨5690772205748301135210335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3793848137165534090140223 5690772205748301135210335)
  ·
    refine ⟨8536158308622451702815503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5690772205748301135210335 8536158308622451702815503)
    ·
      refine ⟨12804237462933677554223255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8536158308622451702815503 12804237462933677554223255)
      ·
        refine ⟨19206356194400516331334883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12804237462933677554223255 19206356194400516331334883)
        ·
          refine ⟨28809534291600774497002325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19206356194400516331334883 28809534291600774497002325)
          ·
            refine ⟨168805864989848288068373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 28809534291600774497002325 168805864989848288068373)
            ·
              refine ⟨7912774921399138503205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 168805864989848288068373 7912774921399138503205)
              ·
                rfl

theorem cell20_156027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 6].length) (baseStart_156027 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156027 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156027 prefixEnd_156027 := by exact prefixLift 156027
  have htrace : WordTrace (prefixWord ++ tailWord_156027) baseStart_156027 baseEnd_156027 := by
    simpa [prefixWord, tailWord_156027, baseEnd_156027] using wordTrace_append hprefix tailTrace_156027
  have hstable : (prefixWord ++ tailWord_156027).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156027).length < 2 ^ (prefixWord ++ tailWord_156027).sum := by decide
  have hdescent : baseEnd_156027 < baseStart_156027 := by decide
  rcases family_descends (prefixWord ++ tailWord_156027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156033 : List Nat := [1, 2, 4, 3, 1, 2, 3, 2, 2]
def baseStart_156033 : Nat := 118140960795 + 156033 * 2 ^ 59
def prefixEnd_156033 : Nat := 4983230072969 + 3 ^ 40 * 156033 * 2
def baseEnd_156033 : Nat := 71217712856082892328821

theorem tailTrace_156033 : CollatzResearch.WordTrace tailWord_156033 prefixEnd_156033 71217712856082892328821 := by
  unfold tailWord_156033
  simp only [CollatzResearch.WordTrace]
  refine ⟨5690991043726564159928753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3793994029151042773285835 5690991043726564159928753)
  ·
    refine ⟨4268243282794923119946565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5690991043726564159928753 4268243282794923119946565)
    ·
      refine ⟨800295615524048084989981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4268243282794923119946565 800295615524048084989981)
      ·
        refine ⟨300110855821518031871243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 800295615524048084989981 300110855821518031871243)
        ·
          refine ⟨450166283732277047806865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300110855821518031871243 450166283732277047806865)
          ·
            refine ⟨337624712799207785855149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 450166283732277047806865 337624712799207785855149)
            ·
              refine ⟨126609267299702919695681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 337624712799207785855149 126609267299702919695681)
              ·
                refine ⟨94956950474777189771761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126609267299702919695681 94956950474777189771761)
                ·
                  refine ⟨71217712856082892328821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94956950474777189771761 71217712856082892328821)
                  ·
                    rfl

theorem cell20_156033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 2].length) (baseStart_156033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156033 prefixEnd_156033 := by exact prefixLift 156033
  have htrace : WordTrace (prefixWord ++ tailWord_156033) baseStart_156033 baseEnd_156033 := by
    simpa [prefixWord, tailWord_156033, baseEnd_156033] using wordTrace_append hprefix tailTrace_156033
  have hstable : (prefixWord ++ tailWord_156033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156033).length < 2 ^ (prefixWord ++ tailWord_156033).sum := by decide
  have hdescent : baseEnd_156033 < baseStart_156033 := by decide
  rcases family_descends (prefixWord ++ tailWord_156033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156084 : List Nat := [2, 5, 2, 2, 2, 1, 2, 2, 2]
def baseStart_156084 : Nat := 118140960795 + 156084 * 2 ^ 59
def prefixEnd_156084 : Nat := 4983230072969 + 3 ^ 40 * 156084 * 2
def baseEnd_156084 : Nat := 71240990645753381628613

theorem tailTrace_156084 : CollatzResearch.WordTrace tailWord_156084 prefixEnd_156084 71240990645753381628613 := by
  unfold tailWord_156084
  simp only [CollatzResearch.WordTrace]
  refine ⟨2846425583270899935017653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3795234111027866580023537 2846425583270899935017653)
  ·
    refine ⟨266852398431646868907905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2846425583270899935017653 266852398431646868907905)
    ·
      refine ⟨200139298823735151680929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266852398431646868907905 200139298823735151680929)
      ·
        refine ⟨150104474117801363760697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200139298823735151680929 150104474117801363760697)
        ·
          refine ⟨112578355588351022820523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150104474117801363760697 112578355588351022820523)
          ·
            refine ⟨168867533382526534230785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112578355588351022820523 168867533382526534230785)
            ·
              refine ⟨126650650036894900673089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168867533382526534230785 126650650036894900673089)
              ·
                refine ⟨94987987527671175504817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126650650036894900673089 94987987527671175504817)
                ·
                  refine ⟨71240990645753381628613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94987987527671175504817 71240990645753381628613)
                  ·
                    rfl

theorem cell20_156084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_156084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156084 prefixEnd_156084 := by exact prefixLift 156084
  have htrace : WordTrace (prefixWord ++ tailWord_156084) baseStart_156084 baseEnd_156084 := by
    simpa [prefixWord, tailWord_156084, baseEnd_156084] using wordTrace_append hprefix tailTrace_156084
  have hstable : (prefixWord ++ tailWord_156084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156084).length < 2 ^ (prefixWord ++ tailWord_156084).sum := by decide
  have hdescent : baseEnd_156084 < baseStart_156084 := by decide
  rcases family_descends (prefixWord ++ tailWord_156084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156089 : List Nat := [1, 2, 1, 4, 3, 1, 1, 4, 3]
def baseStart_156089 : Nat := 118140960795 + 156089 * 2 ^ 59
def prefixEnd_156089 : Nat := 4983230072969 + 3 ^ 40 * 156089 * 2
def baseEnd_156089 : Nat := 71243272781995586461925

theorem tailTrace_156089 : CollatzResearch.WordTrace tailWord_156089 prefixEnd_156089 71243272781995586461925 := by
  unfold tailWord_156089
  simp only [CollatzResearch.WordTrace]
  refine ⟨5693033531523685723967321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3795355687682457149311547 5693033531523685723967321)
  ·
    refine ⟨4269775148642764292975491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5693033531523685723967321 4269775148642764292975491)
    ·
      refine ⟨6404662722964146439463237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4269775148642764292975491 6404662722964146439463237)
      ·
        refine ⟨1200874260555777457399357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6404662722964146439463237 1200874260555777457399357)
        ·
          refine ⟨450327847708416546524759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1200874260555777457399357 450327847708416546524759)
          ·
            refine ⟨675491771562624819787139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450327847708416546524759 675491771562624819787139)
            ·
              refine ⟨1013237657343937229680709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675491771562624819787139 1013237657343937229680709)
              ·
                refine ⟨189982060751988230565133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1013237657343937229680709 189982060751988230565133)
                ·
                  refine ⟨71243272781995586461925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189982060751988230565133 71243272781995586461925)
                  ·
                    rfl

theorem cell20_156089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 3].length) (baseStart_156089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156089 prefixEnd_156089 := by exact prefixLift 156089
  have htrace : WordTrace (prefixWord ++ tailWord_156089) baseStart_156089 baseEnd_156089 := by
    simpa [prefixWord, tailWord_156089, baseEnd_156089] using wordTrace_append hprefix tailTrace_156089
  have hstable : (prefixWord ++ tailWord_156089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156089).length < 2 ^ (prefixWord ++ tailWord_156089).sum := by decide
  have hdescent : baseEnd_156089 < baseStart_156089 := by decide
  rcases family_descends (prefixWord ++ tailWord_156089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156092 : List Nat := [2, 2, 2, 4, 1, 2, 1, 4, 2]
def baseStart_156092 : Nat := 118140960795 + 156092 * 2 ^ 59
def prefixEnd_156092 : Nat := 4983230072969 + 3 ^ 40 * 156092 * 2
def baseEnd_156092 : Nat := 71244642063740909361913

theorem tailTrace_156092 : CollatzResearch.WordTrace tailWord_156092 prefixEnd_156092 71244642063740909361913 := by
  unfold tailWord_156092
  simp only [CollatzResearch.WordTrace]
  refine ⟨2846571475256408618163265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3795428633675211490884353 2846571475256408618163265)
  ·
    refine ⟨2134928606442306463622449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2846571475256408618163265 2134928606442306463622449)
    ·
      refine ⟨1601196454831729847716837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2134928606442306463622449 1601196454831729847716837)
      ·
        refine ⟨300224335280949346446907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1601196454831729847716837 300224335280949346446907)
        ·
          refine ⟨450336502921424019670361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300224335280949346446907 450336502921424019670361)
          ·
            refine ⟨337752377191068014752771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 450336502921424019670361 337752377191068014752771)
            ·
              refine ⟨506628565786602022129157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337752377191068014752771 506628565786602022129157)
              ·
                refine ⟨94992856084987879149217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 506628565786602022129157 94992856084987879149217)
                ·
                  refine ⟨71244642063740909361913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94992856084987879149217 71244642063740909361913)
                  ·
                    rfl

theorem cell20_156092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 2].length) (baseStart_156092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156092 prefixEnd_156092 := by exact prefixLift 156092
  have htrace : WordTrace (prefixWord ++ tailWord_156092) baseStart_156092 baseEnd_156092 := by
    simpa [prefixWord, tailWord_156092, baseEnd_156092] using wordTrace_append hprefix tailTrace_156092
  have hstable : (prefixWord ++ tailWord_156092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156092).length < 2 ^ (prefixWord ++ tailWord_156092).sum := by decide
  have hdescent : baseEnd_156092 < baseStart_156092 := by decide
  rcases family_descends (prefixWord ++ tailWord_156092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156103 : List Nat := [1, 1, 4, 1, 1, 4, 3, 5]
def baseStart_156103 : Nat := 118140960795 + 156103 * 2 ^ 59
def prefixEnd_156103 : Nat := 4983230072969 + 3 ^ 40 * 156103 * 2
def baseEnd_156103 : Nat := 23749887587824586665067

theorem tailTrace_156103 : CollatzResearch.WordTrace tailWord_156103 prefixEnd_156103 23749887587824586665067 := by
  unfold tailWord_156103
  simp only [CollatzResearch.WordTrace]
  refine ⟨5693544153472966114976963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3795696102315310743317975 5693544153472966114976963)
  ·
    refine ⟨8540316230209449172465445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5693544153472966114976963 8540316230209449172465445)
    ·
      refine ⟨1601309293164271719837271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8540316230209449172465445 1601309293164271719837271)
      ·
        refine ⟨2401963939746407579755907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1601309293164271719837271 2401963939746407579755907)
        ·
          refine ⟨3602945909619611369633861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2401963939746407579755907 3602945909619611369633861)
          ·
            refine ⟨675552358053677131806349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3602945909619611369633861 675552358053677131806349)
            ·
              refine ⟨253332134270128924427381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 675552358053677131806349 253332134270128924427381)
              ·
                refine ⟨23749887587824586665067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 253332134270128924427381 23749887587824586665067)
                ·
                  rfl

theorem cell20_156103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 5].length) (baseStart_156103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156103 prefixEnd_156103 := by exact prefixLift 156103
  have htrace : WordTrace (prefixWord ++ tailWord_156103) baseStart_156103 baseEnd_156103 := by
    simpa [prefixWord, tailWord_156103, baseEnd_156103] using wordTrace_append hprefix tailTrace_156103
  have hstable : (prefixWord ++ tailWord_156103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156103).length < 2 ^ (prefixWord ++ tailWord_156103).sum := by decide
  have hdescent : baseEnd_156103 < baseStart_156103 := by decide
  rcases family_descends (prefixWord ++ tailWord_156103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156110 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_156110 : Nat := 118140960795 + 156110 * 2 ^ 59
def prefixEnd_156110 : Nat := 4983230072969 + 3 ^ 40 * 156110 * 2
def baseEnd_156110 : Nat := 71252857754212846761839

theorem tailTrace_156110 : CollatzResearch.WordTrace tailWord_156110 prefixEnd_156110 71252857754212846761839 := by
  unfold tailWord_156110
  simp only [CollatzResearch.WordTrace]
  refine ⟨711724933055950788810223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3795866309631737540321189 711724933055950788810223)
  ·
    refine ⟨1067587399583926183215335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 711724933055950788810223 1067587399583926183215335)
    ·
      refine ⟨1601381099375889274823003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1067587399583926183215335 1601381099375889274823003)
      ·
        refine ⟨2402071649063833912234505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1601381099375889274823003 2402071649063833912234505)
        ·
          refine ⟨1801553736797875434175879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2402071649063833912234505 1801553736797875434175879)
          ·
            refine ⟨2702330605196813151263819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1801553736797875434175879 2702330605196813151263819)
            ·
              refine ⟨4053495907795219726895729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2702330605196813151263819 4053495907795219726895729)
              ·
                refine ⟨3040121930846414795171797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4053495907795219726895729 3040121930846414795171797)
                ·
                  refine ⟨71252857754212846761839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3040121930846414795171797 71252857754212846761839)
                  ·
                    rfl

theorem cell20_156110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_156110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156110 prefixEnd_156110 := by exact prefixLift 156110
  have htrace : WordTrace (prefixWord ++ tailWord_156110) baseStart_156110 baseEnd_156110 := by
    simpa [prefixWord, tailWord_156110, baseEnd_156110] using wordTrace_append hprefix tailTrace_156110
  have hstable : (prefixWord ++ tailWord_156110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156110).length < 2 ^ (prefixWord ++ tailWord_156110).sum := by decide
  have hdescent : baseEnd_156110 < baseStart_156110 := by decide
  rcases family_descends (prefixWord ++ tailWord_156110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156172 : List Nat := [2, 2, 1, 2, 4, 1, 2, 2, 4]
def baseStart_156172 : Nat := 118140960795 + 156172 * 2 ^ 59
def prefixEnd_156172 : Nat := 4983230072969 + 3 ^ 40 * 156172 * 2
def baseEnd_156172 : Nat := 71281156243616186694919

theorem tailTrace_156172 : CollatzResearch.WordTrace tailWord_156172 prefixEnd_156172 71281156243616186694919 := by
  unfold tailWord_156172
  simp only [CollatzResearch.WordTrace]
  refine ⟨2848030395111495449619385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3797373860148660599492513 2848030395111495449619385)
  ·
    refine ⟨2136022796333621587214539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2848030395111495449619385 2136022796333621587214539)
    ·
      refine ⟨3204034194500432380821809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2136022796333621587214539 3204034194500432380821809)
      ·
        refine ⟨2403025645875324285616357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3204034194500432380821809 2403025645875324285616357)
        ·
          refine ⟨450567308601623303553067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2403025645875324285616357 450567308601623303553067)
          ·
            refine ⟨675850962902434955329601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450567308601623303553067 675850962902434955329601)
            ·
              refine ⟨506888222176826216497201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 675850962902434955329601 506888222176826216497201)
              ·
                refine ⟨380166166632619662372901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 506888222176826216497201 380166166632619662372901)
                ·
                  refine ⟨71281156243616186694919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 380166166632619662372901 71281156243616186694919)
                  ·
                    rfl

theorem cell20_156172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_156172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156172 prefixEnd_156172 := by exact prefixLift 156172
  have htrace : WordTrace (prefixWord ++ tailWord_156172) baseStart_156172 baseEnd_156172 := by
    simpa [prefixWord, tailWord_156172, baseEnd_156172] using wordTrace_append hprefix tailTrace_156172
  have hstable : (prefixWord ++ tailWord_156172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156172).length < 2 ^ (prefixWord ++ tailWord_156172).sum := by decide
  have hdescent : baseEnd_156172 < baseStart_156172 := by decide
  rcases family_descends (prefixWord ++ tailWord_156172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156186 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 5]
def baseStart_156186 : Nat := 118140960795 + 156186 * 2 ^ 59
def prefixEnd_156186 : Nat := 4983230072969 + 3 ^ 40 * 156186 * 2
def baseEnd_156186 : Nat := 71287546225094360228195

theorem tailTrace_156186 : CollatzResearch.WordTrace tailWord_156186 prefixEnd_156186 71287546225094360228195 := by
  unfold tailWord_156186
  simp only [CollatzResearch.WordTrace]
  refine ⟨1424142853043067822562103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3797714274781514193498941 1424142853043067822562103)
  ·
    refine ⟨2136214279564601733843155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1424142853043067822562103 2136214279564601733843155)
    ·
      refine ⟨3204321419346902600764733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2136214279564601733843155 3204321419346902600764733)
      ·
        refine ⟨1201620532255088475286775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3204321419346902600764733 1201620532255088475286775)
        ·
          refine ⟨1802430798382632712930163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1201620532255088475286775 1802430798382632712930163)
          ·
            refine ⟨2703646197573949069395245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1802430798382632712930163 2703646197573949069395245)
            ·
              refine ⟨1013867324090230901023217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2703646197573949069395245 1013867324090230901023217)
              ·
                refine ⟨760400493067673175767413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1013867324090230901023217 760400493067673175767413)
                ·
                  refine ⟨71287546225094360228195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 760400493067673175767413 71287546225094360228195)
                  ·
                    rfl

theorem cell20_156186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_156186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156186 prefixEnd_156186 := by exact prefixLift 156186
  have htrace : WordTrace (prefixWord ++ tailWord_156186) baseStart_156186 baseEnd_156186 := by
    simpa [prefixWord, tailWord_156186, baseEnd_156186] using wordTrace_append hprefix tailTrace_156186
  have hstable : (prefixWord ++ tailWord_156186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156186).length < 2 ^ (prefixWord ++ tailWord_156186).sum := by decide
  have hdescent : baseEnd_156186 < baseStart_156186 := by decide
  rcases family_descends (prefixWord ++ tailWord_156186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156206 : List Nat := [4, 1, 3, 1, 3, 2, 1, 1, 4]
def baseStart_156206 : Nat := 118140960795 + 156206 * 2 ^ 59
def prefixEnd_156206 : Nat := 4983230072969 + 3 ^ 40 * 156206 * 2
def baseEnd_156206 : Nat := 71296674770063179561447

theorem tailTrace_156206 : CollatzResearch.WordTrace tailWord_156206 prefixEnd_156206 71296674770063179561447 := by
  unfold tailWord_156206
  simp only [CollatzResearch.WordTrace]
  refine ⟨712162609012476838247059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3798200581399876470650981 712162609012476838247059)
  ·
    refine ⟨1068243913518715257370589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 712162609012476838247059 1068243913518715257370589)
    ·
      refine ⟨400591467569518221513971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1068243913518715257370589 400591467569518221513971)
      ·
        refine ⟨600887201354277332270957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400591467569518221513971 600887201354277332270957)
        ·
          refine ⟨225332700507853999601609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 600887201354277332270957 225332700507853999601609)
          ·
            refine ⟨168999525380890499701207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225332700507853999601609 168999525380890499701207)
            ·
              refine ⟨253499288071335749551811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168999525380890499701207 253499288071335749551811)
              ·
                refine ⟨380248932107003624327717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253499288071335749551811 380248932107003624327717)
                ·
                  refine ⟨71296674770063179561447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 380248932107003624327717 71296674770063179561447)
                  ·
                    rfl

theorem cell20_156206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_156206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156206 prefixEnd_156206 := by exact prefixLift 156206
  have htrace : WordTrace (prefixWord ++ tailWord_156206) baseStart_156206 baseEnd_156206 := by
    simpa [prefixWord, tailWord_156206, baseEnd_156206] using wordTrace_append hprefix tailTrace_156206
  have hstable : (prefixWord ++ tailWord_156206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156206).length < 2 ^ (prefixWord ++ tailWord_156206).sum := by decide
  have hdescent : baseEnd_156206 < baseStart_156206 := by decide
  rcases family_descends (prefixWord ++ tailWord_156206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156210 : List Nat := [3, 2, 1, 1, 2, 1, 5, 1, 4]
def baseStart_156210 : Nat := 118140960795 + 156210 * 2 ^ 59
def prefixEnd_156210 : Nat := 4983230072969 + 3 ^ 40 * 156210 * 2
def baseEnd_156210 : Nat := 71298500479056943428097

theorem tailTrace_156210 : CollatzResearch.WordTrace tailWord_156210 prefixEnd_156210 71298500479056943428097 := by
  unfold tailWord_156210
  simp only [CollatzResearch.WordTrace]
  refine ⟨1424361691021330847280521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3798297842723548926081389 1424361691021330847280521)
  ·
    refine ⟨1068271268265998135460391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1424361691021330847280521 1068271268265998135460391)
    ·
      refine ⟨1602406902398997203190587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1068271268265998135460391 1602406902398997203190587)
      ·
        refine ⟨2403610353598495804785881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1602406902398997203190587 2403610353598495804785881)
        ·
          refine ⟨1802707765198871853589411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2403610353598495804785881 1802707765198871853589411)
          ·
            refine ⟨2704061647798307780384117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1802707765198871853589411 2704061647798307780384117)
            ·
              refine ⟨253505779481091354411011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2704061647798307780384117 253505779481091354411011)
              ·
                refine ⟨380258669221637031616517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253505779481091354411011 380258669221637031616517)
                ·
                  refine ⟨71298500479056943428097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 380258669221637031616517 71298500479056943428097)
                  ·
                    rfl

theorem cell20_156210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_156210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156210 prefixEnd_156210 := by exact prefixLift 156210
  have htrace : WordTrace (prefixWord ++ tailWord_156210) baseStart_156210 baseEnd_156210 := by
    simpa [prefixWord, tailWord_156210, baseEnd_156210] using wordTrace_append hprefix tailTrace_156210
  have hstable : (prefixWord ++ tailWord_156210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156210).length < 2 ^ (prefixWord ++ tailWord_156210).sum := by decide
  have hdescent : baseEnd_156210 < baseStart_156210 := by decide
  rcases family_descends (prefixWord ++ tailWord_156210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156217 : List Nat := [1, 2, 1, 5, 1, 1, 4, 5]
def baseStart_156217 : Nat := 118140960795 + 156217 * 2 ^ 59
def prefixEnd_156217 : Nat := 4983230072969 + 3 ^ 40 * 156217 * 2
def baseEnd_156217 : Nat := 23767231823265343398245

theorem tailTrace_156217 : CollatzResearch.WordTrace tailWord_156217 prefixEnd_156217 23767231823265343398245 := by
  unfold tailWord_156217
  simp only [CollatzResearch.WordTrace]
  refine ⟨5697702075059963584626905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3798468050039975723084603 5697702075059963584626905)
  ·
    refine ⟨4273276556294972688470179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5697702075059963584626905 4273276556294972688470179)
    ·
      refine ⟨6409914834442459032705269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4273276556294972688470179 6409914834442459032705269)
      ·
        refine ⟨600929515728980534316119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6409914834442459032705269 600929515728980534316119)
        ·
          refine ⟨901394273593470801474179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 600929515728980534316119 901394273593470801474179)
          ·
            refine ⟨1352091410390206202211269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901394273593470801474179 1352091410390206202211269)
            ·
              refine ⟨253517139448163662914613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1352091410390206202211269 253517139448163662914613)
              ·
                refine ⟨23767231823265343398245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 253517139448163662914613 23767231823265343398245)
                ·
                  rfl

theorem cell20_156217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 5].length) (baseStart_156217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156217 prefixEnd_156217 := by exact prefixLift 156217
  have htrace : WordTrace (prefixWord ++ tailWord_156217) baseStart_156217 baseEnd_156217 := by
    simpa [prefixWord, tailWord_156217, baseEnd_156217] using wordTrace_append hprefix tailTrace_156217
  have hstable : (prefixWord ++ tailWord_156217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156217).length < 2 ^ (prefixWord ++ tailWord_156217).sum := by decide
  have hdescent : baseEnd_156217 < baseStart_156217 := by decide
  rcases family_descends (prefixWord ++ tailWord_156217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156220 : List Nat := [2, 2, 2, 2, 3, 1, 4, 1, 3]
def baseStart_156220 : Nat := 118140960795 + 156220 * 2 ^ 59
def prefixEnd_156220 : Nat := 4983230072969 + 3 ^ 40 * 156220 * 2
def baseEnd_156220 : Nat := 71303064751541353094723

theorem tailTrace_156220 : CollatzResearch.WordTrace tailWord_156220 prefixEnd_156220 71303064751541353094723 := by
  unfold tailWord_156220
  simp only [CollatzResearch.WordTrace]
  refine ⟨2848905747024547548493057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3798540996032730064657409 2848905747024547548493057)
  ·
    refine ⟨2136679310268410661369793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2848905747024547548493057 2136679310268410661369793)
    ·
      refine ⟨1602509482701307996027345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2136679310268410661369793 1602509482701307996027345)
      ·
        refine ⟨1201882112025980997020509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1602509482701307996027345 1201882112025980997020509)
        ·
          refine ⟨450705792009742873882691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1201882112025980997020509 450705792009742873882691)
          ·
            refine ⟨676058688014614310824037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450705792009742873882691 676058688014614310824037)
            ·
              refine ⟨126761004002740183279507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 676058688014614310824037 126761004002740183279507)
              ·
                refine ⟨190141506004110274919261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126761004002740183279507 190141506004110274919261)
                ·
                  refine ⟨71303064751541353094723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190141506004110274919261 71303064751541353094723)
                  ·
                    rfl

theorem cell20_156220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_156220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156220 prefixEnd_156220 := by exact prefixLift 156220
  have htrace : WordTrace (prefixWord ++ tailWord_156220) baseStart_156220 baseEnd_156220 := by
    simpa [prefixWord, tailWord_156220, baseEnd_156220] using wordTrace_append hprefix tailTrace_156220
  have hstable : (prefixWord ++ tailWord_156220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156220).length < 2 ^ (prefixWord ++ tailWord_156220).sum := by decide
  have hdescent : baseEnd_156220 < baseStart_156220 := by decide
  rcases family_descends (prefixWord ++ tailWord_156220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156261 : List Nat := [1, 3, 1, 3, 4, 2, 2, 2, 2]
def baseStart_156261 : Nat := 118140960795 + 156261 * 2 ^ 59
def prefixEnd_156261 : Nat := 4983230072969 + 3 ^ 40 * 156261 * 2
def baseEnd_156261 : Nat := 71321778268727432727889

theorem tailTrace_156261 : CollatzResearch.WordTrace tailWord_156261 prefixEnd_156261 71321778268727432727889 := by
  unfold tailWord_156261
  simp only [CollatzResearch.WordTrace]
  refine ⟨5699306886900559099228637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3799537924600372732819091 5699306886900559099228637)
  ·
    refine ⟨2137240082587709662210739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5699306886900559099228637 2137240082587709662210739)
    ·
      refine ⟨3205860123881564493316109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2137240082587709662210739 3205860123881564493316109)
      ·
        refine ⟨1202197546455586684993541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3205860123881564493316109 1202197546455586684993541)
        ·
          refine ⟨225412039960422503436289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1202197546455586684993541 225412039960422503436289)
          ·
            refine ⟨169059029970316877577217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225412039960422503436289 169059029970316877577217)
            ·
              refine ⟨126794272477737658182913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169059029970316877577217 126794272477737658182913)
              ·
                refine ⟨95095704358303243637185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126794272477737658182913 95095704358303243637185)
                ·
                  refine ⟨71321778268727432727889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95095704358303243637185 71321778268727432727889)
                  ·
                    rfl

theorem cell20_156261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 2].length) (baseStart_156261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156261 prefixEnd_156261 := by exact prefixLift 156261
  have htrace : WordTrace (prefixWord ++ tailWord_156261) baseStart_156261 baseEnd_156261 := by
    simpa [prefixWord, tailWord_156261, baseEnd_156261] using wordTrace_append hprefix tailTrace_156261
  have hstable : (prefixWord ++ tailWord_156261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156261).length < 2 ^ (prefixWord ++ tailWord_156261).sum := by decide
  have hdescent : baseEnd_156261 < baseStart_156261 := by decide
  rcases family_descends (prefixWord ++ tailWord_156261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156272 : List Nat := [2, 1, 1, 1, 7, 2, 1, 5]
def baseStart_156272 : Nat := 118140960795 + 156272 * 2 ^ 59
def prefixEnd_156272 : Nat := 4983230072969 + 3 ^ 40 * 156272 * 2
def baseEnd_156272 : Nat := 23775599656153427787059

theorem tailTrace_156272 : CollatzResearch.WordTrace tailWord_156272 prefixEnd_156272 23775599656153427787059 := by
  unfold tailWord_156272
  simp only [CollatzResearch.WordTrace]
  refine ⟨2849854044930353988939535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3799805393240471985252713 2849854044930353988939535)
  ·
    refine ⟨4274781067395530983409303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2849854044930353988939535 4274781067395530983409303)
    ·
      refine ⟨6412171601093296475113955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4274781067395530983409303 6412171601093296475113955)
      ·
        refine ⟨9618257401639944712670933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6412171601093296475113955 9618257401639944712670933)
        ·
          refine ⟨225427907850936204203225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 9618257401639944712670933 225427907850936204203225)
          ·
            refine ⟨169070930888202153152419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225427907850936204203225 169070930888202153152419)
            ·
              refine ⟨253606396332303229728629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169070930888202153152419 253606396332303229728629)
              ·
                refine ⟨23775599656153427787059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 253606396332303229728629 23775599656153427787059)
                ·
                  rfl

theorem cell20_156272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 5].length) (baseStart_156272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156272 prefixEnd_156272 := by exact prefixLift 156272
  have htrace : WordTrace (prefixWord ++ tailWord_156272) baseStart_156272 baseEnd_156272 := by
    simpa [prefixWord, tailWord_156272, baseEnd_156272] using wordTrace_append hprefix tailTrace_156272
  have hstable : (prefixWord ++ tailWord_156272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156272).length < 2 ^ (prefixWord ++ tailWord_156272).sum := by decide
  have hdescent : baseEnd_156272 < baseStart_156272 := by decide
  rcases family_descends (prefixWord ++ tailWord_156272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156317 : List Nat := [1, 4, 2, 1, 1, 1, 5, 2, 3]
def baseStart_156317 : Nat := 118140960795 + 156317 * 2 ^ 59
def prefixEnd_156317 : Nat := 4983230072969 + 3 ^ 40 * 156317 * 2
def baseEnd_156317 : Nat := 71347338194640126860993

theorem tailTrace_156317 : CollatzResearch.WordTrace tailWord_156317 prefixEnd_156317 71347338194640126860993 := by
  unfold tailWord_156317
  simp only [CollatzResearch.WordTrace]
  refine ⟨5701349374697680663267205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3800899583131787108844803 5701349374697680663267205)
  ·
    refine ⟨1069003007755815124362601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5701349374697680663267205 1069003007755815124362601)
    ·
      refine ⟨801752255816861343271951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1069003007755815124362601 801752255816861343271951)
      ·
        refine ⟨1202628383725292014907927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 801752255816861343271951 1202628383725292014907927)
        ·
          refine ⟨1803942575587938022361891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1202628383725292014907927 1803942575587938022361891)
          ·
            refine ⟨2705913863381907033542837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1803942575587938022361891 2705913863381907033542837)
            ·
              refine ⟨253679424692053784394641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2705913863381907033542837 253679424692053784394641)
              ·
                refine ⟨190259568519040338295981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 253679424692053784394641 190259568519040338295981)
                ·
                  refine ⟨71347338194640126860993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190259568519040338295981 71347338194640126860993)
                  ·
                    rfl

theorem cell20_156317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_156317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156317 prefixEnd_156317 := by exact prefixLift 156317
  have htrace : WordTrace (prefixWord ++ tailWord_156317) baseStart_156317 baseEnd_156317 := by
    simpa [prefixWord, tailWord_156317, baseEnd_156317] using wordTrace_append hprefix tailTrace_156317
  have hstable : (prefixWord ++ tailWord_156317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156317).length < 2 ^ (prefixWord ++ tailWord_156317).sum := by decide
  have hdescent : baseEnd_156317 < baseStart_156317 := by decide
  rcases family_descends (prefixWord ++ tailWord_156317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156324 : List Nat := [2, 3, 1, 2, 2, 1, 4, 1, 4]
def baseStart_156324 : Nat := 118140960795 + 156324 * 2 ^ 59
def prefixEnd_156324 : Nat := 4983230072969 + 3 ^ 40 * 156324 * 2
def baseEnd_156324 : Nat := 71350533185379213627631

theorem tailTrace_156324 : CollatzResearch.WordTrace tailWord_156324 prefixEnd_156324 71350533185379213627631 := by
  unfold tailWord_156324
  simp only [CollatzResearch.WordTrace]
  refine ⟨2850802342836160429386013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3801069790448213905848017 2850802342836160429386013)
  ·
    refine ⟨1069050878563560161019755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2850802342836160429386013 1069050878563560161019755)
    ·
      refine ⟨1603576317845340241529633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1069050878563560161019755 1603576317845340241529633)
      ·
        refine ⟨1202682238384005181147225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1603576317845340241529633 1202682238384005181147225)
        ·
          refine ⟨902011678788003885860419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1202682238384005181147225 902011678788003885860419)
          ·
            refine ⟨1353017518182005828790629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902011678788003885860419 1353017518182005828790629)
            ·
              refine ⟨253690784659126092898243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1353017518182005828790629 253690784659126092898243)
              ·
                refine ⟨380536176988689139347365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253690784659126092898243 380536176988689139347365)
                ·
                  refine ⟨71350533185379213627631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 380536176988689139347365 71350533185379213627631)
                  ·
                    rfl

theorem cell20_156324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_156324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156324 prefixEnd_156324 := by exact prefixLift 156324
  have htrace : WordTrace (prefixWord ++ tailWord_156324) baseStart_156324 baseEnd_156324 := by
    simpa [prefixWord, tailWord_156324, baseEnd_156324] using wordTrace_append hprefix tailTrace_156324
  have hstable : (prefixWord ++ tailWord_156324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156324).length < 2 ^ (prefixWord ++ tailWord_156324).sum := by decide
  have hdescent : baseEnd_156324 < baseStart_156324 := by decide
  rcases family_descends (prefixWord ++ tailWord_156324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156330 : List Nat := [3, 1, 5, 2, 1, 1, 3, 1, 3]
def baseStart_156330 : Nat := 118140960795 + 156330 * 2 ^ 59
def prefixEnd_156330 : Nat := 4983230072969 + 3 ^ 40 * 156330 * 2
def baseEnd_156330 : Nat := 71353271748869859427607

theorem tailTrace_156330 : CollatzResearch.WordTrace tailWord_156330 prefixEnd_156330 71353271748869859427607 := by
  unfold tailWord_156330
  simp only [CollatzResearch.WordTrace]
  refine ⟨1425455880912645970872611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3801215682433722588993629 1425455880912645970872611)
  ·
    refine ⟨2138183821368968956308917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1425455880912645970872611 2138183821368968956308917)
    ·
      refine ⟨200454733253340839653961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2138183821368968956308917 200454733253340839653961)
      ·
        refine ⟨150341049940005629740471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200454733253340839653961 150341049940005629740471)
        ·
          refine ⟨225511574910008444610707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150341049940005629740471 225511574910008444610707)
          ·
            refine ⟨338267362365012666916061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225511574910008444610707 338267362365012666916061)
            ·
              refine ⟨126850260886879750093523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 338267362365012666916061 126850260886879750093523)
              ·
                refine ⟨190275391330319625140285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126850260886879750093523 190275391330319625140285)
                ·
                  refine ⟨71353271748869859427607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190275391330319625140285 71353271748869859427607)
                  ·
                    rfl

theorem cell20_156330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_156330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156330 prefixEnd_156330 := by exact prefixLift 156330
  have htrace : WordTrace (prefixWord ++ tailWord_156330) baseStart_156330 baseEnd_156330 := by
    simpa [prefixWord, tailWord_156330, baseEnd_156330] using wordTrace_append hprefix tailTrace_156330
  have hstable : (prefixWord ++ tailWord_156330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156330).length < 2 ^ (prefixWord ++ tailWord_156330).sum := by decide
  have hdescent : baseEnd_156330 < baseStart_156330 := by decide
  rcases family_descends (prefixWord ++ tailWord_156330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156365 : List Nat := [1, 6, 2, 1, 2, 2, 6]
def baseStart_156365 : Nat := 118140960795 + 156365 * 2 ^ 59
def prefixEnd_156365 : Nat := 4983230072969 + 3 ^ 40 * 156365 * 2
def baseEnd_156365 : Nat := 7929916300285032584533

theorem tailTrace_156365 : CollatzResearch.WordTrace tailWord_156365 prefixEnd_156365 7929916300285032584533 := by
  unfold tailWord_156365
  simp only [CollatzResearch.WordTrace]
  refine ⟨5703100078523784861014549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3802066719015856574009699 5703100078523784861014549)
  ·
    refine ⟨267332816180802415360057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5703100078523784861014549 267332816180802415360057)
    ·
      refine ⟨200499612135601811520043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267332816180802415360057 200499612135601811520043)
      ·
        refine ⟨300749418203402717280065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200499612135601811520043 300749418203402717280065)
        ·
          refine ⟨225562063652552037960049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300749418203402717280065 225562063652552037960049)
          ·
            refine ⟨169171547739414028470037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225562063652552037960049 169171547739414028470037)
            ·
              refine ⟨7929916300285032584533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 169171547739414028470037 7929916300285032584533)
              ·
                rfl

theorem cell20_156365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 6].length) (baseStart_156365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156365 prefixEnd_156365 := by exact prefixLift 156365
  have htrace : WordTrace (prefixWord ++ tailWord_156365) baseStart_156365 baseEnd_156365 := by
    simpa [prefixWord, tailWord_156365, baseEnd_156365] using wordTrace_append hprefix tailTrace_156365
  have hstable : (prefixWord ++ tailWord_156365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156365).length < 2 ^ (prefixWord ++ tailWord_156365).sum := by decide
  have hdescent : baseEnd_156365 < baseStart_156365 := by decide
  rcases family_descends (prefixWord ++ tailWord_156365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156376 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 5]
def baseStart_156376 : Nat := 118140960795 + 156376 * 2 ^ 59
def prefixEnd_156376 : Nat := 4983230072969 + 3 ^ 40 * 156376 * 2
def baseEnd_156376 : Nat := 71374267402298143894085

theorem tailTrace_156376 : CollatzResearch.WordTrace tailWord_156376 prefixEnd_156376 71374267402298143894085 := by
  unfold tailWord_156376
  simp only [CollatzResearch.WordTrace]
  refine ⟨2851750640741966869832491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3802334187655955826443321 2851750640741966869832491)
  ·
    refine ⟨4277625961112950304748737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2851750640741966869832491 4277625961112950304748737)
    ·
      refine ⟨3208219470834712728561553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4277625961112950304748737 3208219470834712728561553)
      ·
        refine ⟨2406164603126034546421165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3208219470834712728561553 2406164603126034546421165)
        ·
          refine ⟨902311726172262954907937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2406164603126034546421165 902311726172262954907937)
          ·
            refine ⟨676733794629197216180953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 902311726172262954907937 676733794629197216180953)
            ·
              refine ⟨507550345971897912135715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 676733794629197216180953 507550345971897912135715)
              ·
                refine ⟨761325518957846868203573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 507550345971897912135715 761325518957846868203573)
                ·
                  refine ⟨71374267402298143894085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 761325518957846868203573 71374267402298143894085)
                  ·
                    rfl

theorem cell20_156376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_156376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156376 prefixEnd_156376 := by exact prefixLift 156376
  have htrace : WordTrace (prefixWord ++ tailWord_156376) baseStart_156376 baseEnd_156376 := by
    simpa [prefixWord, tailWord_156376, baseEnd_156376] using wordTrace_append hprefix tailTrace_156376
  have hstable : (prefixWord ++ tailWord_156376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156376).length < 2 ^ (prefixWord ++ tailWord_156376).sum := by decide
  have hdescent : baseEnd_156376 < baseStart_156376 := by decide
  rcases family_descends (prefixWord ++ tailWord_156376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156393 : List Nat := [1, 2, 1, 1, 1, 2, 8, 1, 3]
def baseStart_156393 : Nat := 118140960795 + 156393 * 2 ^ 59
def prefixEnd_156393 : Nat := 4983230072969 + 3 ^ 40 * 156393 * 2
def baseEnd_156393 : Nat := 71382026665521640327349

theorem tailTrace_156393 : CollatzResearch.WordTrace tailWord_156393 prefixEnd_156393 71382026665521640327349 := by
  unfold tailWord_156393
  simp only [CollatzResearch.WordTrace]
  refine ⟨5704121322422345643033833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3802747548281563762022555 5704121322422345643033833)
  ·
    refine ⟨4278090991816759232275375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5704121322422345643033833 4278090991816759232275375)
    ·
      refine ⟨6417136487725138848413063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4278090991816759232275375 6417136487725138848413063)
      ·
        refine ⟨9625704731587708272619595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6417136487725138848413063 9625704731587708272619595)
        ·
          refine ⟨14438557097381562408929393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9625704731587708272619595 14438557097381562408929393)
          ·
            refine ⟨10828917823036171806697045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14438557097381562408929393 10828917823036171806697045)
            ·
              refine ⟨126901380738705138359731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 10828917823036171806697045 126901380738705138359731)
              ·
                refine ⟨190352071108057707539597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126901380738705138359731 190352071108057707539597)
                ·
                  refine ⟨71382026665521640327349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190352071108057707539597 71382026665521640327349)
                  ·
                    rfl

theorem cell20_156393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 3].length) (baseStart_156393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156393 prefixEnd_156393 := by exact prefixLift 156393
  have htrace : WordTrace (prefixWord ++ tailWord_156393) baseStart_156393 baseEnd_156393 := by
    simpa [prefixWord, tailWord_156393, baseEnd_156393] using wordTrace_append hprefix tailTrace_156393
  have hstable : (prefixWord ++ tailWord_156393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156393).length < 2 ^ (prefixWord ++ tailWord_156393).sum := by decide
  have hdescent : baseEnd_156393 < baseStart_156393 := by decide
  rcases family_descends (prefixWord ++ tailWord_156393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156490 : List Nat := [3, 1, 2, 1, 1, 1, 2, 6, 3]
def baseStart_156490 : Nat := 118140960795 + 156490 * 2 ^ 59
def prefixEnd_156490 : Nat := 4983230072969 + 3 ^ 40 * 156490 * 2
def baseEnd_156490 : Nat := 71426300108620414093619

theorem tailTrace_156490 : CollatzResearch.WordTrace tailWord_156490 prefixEnd_156490 71426300108620414093619 := by
  unfold tailWord_156490
  simp only [CollatzResearch.WordTrace]
  refine ⟨1426914800767732802328731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3805106135380620806209949 1426914800767732802328731)
  ·
    refine ⟨2140372201151599203493097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1426914800767732802328731 2140372201151599203493097)
    ·
      refine ⟨1605279150863699402619823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2140372201151599203493097 1605279150863699402619823)
      ·
        refine ⟨2407918726295549103929735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1605279150863699402619823 2407918726295549103929735)
        ·
          refine ⟨3611878089443323655894603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2407918726295549103929735 3611878089443323655894603)
          ·
            refine ⟨5417817134164985483841905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3611878089443323655894603 5417817134164985483841905)
            ·
              refine ⟨4063362850623739112881429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5417817134164985483841905 4063362850623739112881429)
              ·
                refine ⟨190470133622987770916317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4063362850623739112881429 190470133622987770916317)
                ·
                  refine ⟨71426300108620414093619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190470133622987770916317 71426300108620414093619)
                  ·
                    rfl

theorem cell20_156490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_156490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156490 prefixEnd_156490 := by exact prefixLift 156490
  have htrace : WordTrace (prefixWord ++ tailWord_156490) baseStart_156490 baseEnd_156490 := by
    simpa [prefixWord, tailWord_156490, baseEnd_156490] using wordTrace_append hprefix tailTrace_156490
  have hstable : (prefixWord ++ tailWord_156490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156490).length < 2 ^ (prefixWord ++ tailWord_156490).sum := by decide
  have hdescent : baseEnd_156490 < baseStart_156490 := by decide
  rcases family_descends (prefixWord ++ tailWord_156490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156552 : List Nat := [2, 1, 3, 3, 2, 1, 3, 1, 4]
def baseStart_156552 : Nat := 118140960795 + 156552 * 2 ^ 59
def prefixEnd_156552 : Nat := 4983230072969 + 3 ^ 40 * 156552 * 2
def baseEnd_156552 : Nat := 71454598598023754026699

theorem tailTrace_156552 : CollatzResearch.WordTrace tailWord_156552 prefixEnd_156552 71454598598023754026699 := by
  unfold tailWord_156552
  simp only [CollatzResearch.WordTrace]
  refine ⟨2854960264423157899035955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3806613685897543865381273 2854960264423157899035955)
  ·
    refine ⟨4282440396634736848553933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2854960264423157899035955 4282440396634736848553933)
    ·
      refine ⟨1605915148738026318207725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4282440396634736848553933 1605915148738026318207725)
      ·
        refine ⟨602218180776759869327897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1605915148738026318207725 602218180776759869327897)
        ·
          refine ⟨451663635582569901995923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 602218180776759869327897 451663635582569901995923)
          ·
            refine ⟨677495453373854852993885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451663635582569901995923 677495453373854852993885)
            ·
              refine ⟨254060795015195569872707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 677495453373854852993885 254060795015195569872707)
              ·
                refine ⟨381091192522793354809061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254060795015195569872707 381091192522793354809061)
                ·
                  refine ⟨71454598598023754026699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 381091192522793354809061 71454598598023754026699)
                  ·
                    rfl

theorem cell20_156552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_156552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156552 prefixEnd_156552 := by exact prefixLift 156552
  have htrace : WordTrace (prefixWord ++ tailWord_156552) baseStart_156552 baseEnd_156552 := by
    simpa [prefixWord, tailWord_156552, baseEnd_156552] using wordTrace_append hprefix tailTrace_156552
  have hstable : (prefixWord ++ tailWord_156552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156552).length < 2 ^ (prefixWord ++ tailWord_156552).sum := by decide
  have hdescent : baseEnd_156552 < baseStart_156552 := by decide
  rcases family_descends (prefixWord ++ tailWord_156552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156562 : List Nat := [3, 2, 3, 2, 2, 1, 1, 3, 3]
def baseStart_156562 : Nat := 118140960795 + 156562 * 2 ^ 59
def prefixEnd_156562 : Nat := 4983230072969 + 3 ^ 40 * 156562 * 2
def baseEnd_156562 : Nat := 71459162870508163693325

theorem tailTrace_156562 : CollatzResearch.WordTrace tailWord_156562 prefixEnd_156562 71459162870508163693325 := by
  unfold tailWord_156562
  simp only [CollatzResearch.WordTrace]
  refine ⟨1427571314702521876483985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3806856839206725003957293 1427571314702521876483985)
  ·
    refine ⟨1070678486026891407362989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1427571314702521876483985 1070678486026891407362989)
    ·
      refine ⟨401504432260084277761121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1070678486026891407362989 401504432260084277761121)
      ·
        refine ⟨301128324195063208320841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 401504432260084277761121 301128324195063208320841)
        ·
          refine ⟨225846243146297406240631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301128324195063208320841 225846243146297406240631)
          ·
            refine ⟨338769364719446109360947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225846243146297406240631 338769364719446109360947)
            ·
              refine ⟨508154047079169164041421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338769364719446109360947 508154047079169164041421)
              ·
                refine ⟨190557767654688436515533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 508154047079169164041421 190557767654688436515533)
                ·
                  refine ⟨71459162870508163693325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190557767654688436515533 71459162870508163693325)
                  ·
                    rfl

theorem cell20_156562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_156562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156562 prefixEnd_156562 := by exact prefixLift 156562
  have htrace : WordTrace (prefixWord ++ tailWord_156562) baseStart_156562 baseEnd_156562 := by
    simpa [prefixWord, tailWord_156562, baseEnd_156562] using wordTrace_append hprefix tailTrace_156562
  have hstable : (prefixWord ++ tailWord_156562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156562).length < 2 ^ (prefixWord ++ tailWord_156562).sum := by decide
  have hdescent : baseEnd_156562 < baseStart_156562 := by decide
  rcases family_descends (prefixWord ++ tailWord_156562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156573 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 6]
def baseStart_156573 : Nat := 118140960795 + 156573 * 2 ^ 59
def prefixEnd_156573 : Nat := 4983230072969 + 3 ^ 40 * 156573 * 2
def baseEnd_156573 : Nat := 71464183570241014326613

theorem tailTrace_156573 : CollatzResearch.WordTrace tailWord_156573 prefixEnd_156573 71464183570241014326613 := by
  unfold tailWord_156573
  simp only [CollatzResearch.WordTrace]
  refine ⟨5710686461770236384586373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3807124307846824256390915 5710686461770236384586373)
  ·
    refine ⟨1070753711581919322109945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5710686461770236384586373 1070753711581919322109945)
    ·
      refine ⟨803065283686439491582459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1070753711581919322109945 803065283686439491582459)
      ·
        refine ⟨1204597925529659237373689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 803065283686439491582459 1204597925529659237373689)
        ·
          refine ⟨903448444147244428030267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1204597925529659237373689 903448444147244428030267)
          ·
            refine ⟨1355172666220866642045401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903448444147244428030267 1355172666220866642045401)
            ·
              refine ⟨1016379499665649981534051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1355172666220866642045401 1016379499665649981534051)
              ·
                refine ⟨1524569249498474972301077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1016379499665649981534051 1524569249498474972301077)
                ·
                  refine ⟨71464183570241014326613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1524569249498474972301077 71464183570241014326613)
                  ·
                    rfl

theorem cell20_156573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_156573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156573 prefixEnd_156573 := by exact prefixLift 156573
  have htrace : WordTrace (prefixWord ++ tailWord_156573) baseStart_156573 baseEnd_156573 := by
    simpa [prefixWord, tailWord_156573, baseEnd_156573] using wordTrace_append hprefix tailTrace_156573
  have hstable : (prefixWord ++ tailWord_156573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156573).length < 2 ^ (prefixWord ++ tailWord_156573).sum := by decide
  have hdescent : baseEnd_156573 < baseStart_156573 := by decide
  rcases family_descends (prefixWord ++ tailWord_156573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156580 : List Nat := [2, 3, 1, 2, 1, 2, 1, 8]
def baseStart_156580 : Nat := 118140960795 + 156580 * 2 ^ 59
def prefixEnd_156580 : Nat := 4983230072969 + 3 ^ 40 * 156580 * 2
def baseEnd_156580 : Nat := 23822459520326700364417

theorem tailTrace_156580 : CollatzResearch.WordTrace tailWord_156580 prefixEnd_156580 23822459520326700364417 := by
  unfold tailWord_156580
  simp only [CollatzResearch.WordTrace]
  refine ⟨2855470886372438290045597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3807294515163251053394129 2855470886372438290045597)
  ·
    refine ⟨1070801582389664358767099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2855470886372438290045597 1070801582389664358767099)
    ·
      refine ⟨1606202373584496538150649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1070801582389664358767099 1606202373584496538150649)
      ·
        refine ⟨1204651780188372403612987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1606202373584496538150649 1204651780188372403612987)
        ·
          refine ⟨1806977670282558605419481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1204651780188372403612987 1806977670282558605419481)
          ·
            refine ⟨1355233252711918954064611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1806977670282558605419481 1355233252711918954064611)
            ·
              refine ⟨2032849879067878431096917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1355233252711918954064611 2032849879067878431096917)
              ·
                refine ⟨23822459520326700364417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2032849879067878431096917 23822459520326700364417)
                ·
                  rfl

theorem cell20_156580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_156580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156580 prefixEnd_156580 := by exact prefixLift 156580
  have htrace : WordTrace (prefixWord ++ tailWord_156580) baseStart_156580 baseEnd_156580 := by
    simpa [prefixWord, tailWord_156580, baseEnd_156580] using wordTrace_append hprefix tailTrace_156580
  have hstable : (prefixWord ++ tailWord_156580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156580).length < 2 ^ (prefixWord ++ tailWord_156580).sum := by decide
  have hdescent : baseEnd_156580 < baseStart_156580 := by decide
  rcases family_descends (prefixWord ++ tailWord_156580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156628 : List Nat := [2, 4, 1, 2, 1, 3, 1, 2, 4]
def baseStart_156628 : Nat := 118140960795 + 156628 * 2 ^ 59
def prefixEnd_156628 : Nat := 4983230072969 + 3 ^ 40 * 156628 * 2
def baseEnd_156628 : Nat := 71489287068905267493055

theorem tailTrace_156628 : CollatzResearch.WordTrace tailWord_156628 prefixEnd_156628 71489287068905267493055 := by
  unfold tailWord_156628
  simp only [CollatzResearch.WordTrace]
  refine ⟨2856346238285490388919269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3808461651047320518559025 2856346238285490388919269)
  ·
    refine ⟨535564919678529447922363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2856346238285490388919269 535564919678529447922363)
    ·
      refine ⟨803347379517794171883545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 535564919678529447922363 803347379517794171883545)
      ·
        refine ⟨602510534638345628912659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 803347379517794171883545 602510534638345628912659)
        ·
          refine ⟨903765801957518443368989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602510534638345628912659 903765801957518443368989)
          ·
            refine ⟨338912175734069416263371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 903765801957518443368989 338912175734069416263371)
            ·
              refine ⟨508368263601104124395057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338912175734069416263371 508368263601104124395057)
              ·
                refine ⟨381276197700828093296293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 508368263601104124395057 381276197700828093296293)
                ·
                  refine ⟨71489287068905267493055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 381276197700828093296293 71489287068905267493055)
                  ·
                    rfl

theorem cell20_156628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_156628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156628 prefixEnd_156628 := by exact prefixLift 156628
  have htrace : WordTrace (prefixWord ++ tailWord_156628) baseStart_156628 baseEnd_156628 := by
    simpa [prefixWord, tailWord_156628, baseEnd_156628] using wordTrace_append hprefix tailTrace_156628
  have hstable : (prefixWord ++ tailWord_156628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156628).length < 2 ^ (prefixWord ++ tailWord_156628).sum := by decide
  have hdescent : baseEnd_156628 < baseStart_156628 := by decide
  rcases family_descends (prefixWord ++ tailWord_156628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156700 : List Nat := [2, 2, 3, 1, 4, 2, 1, 3, 2]
def baseStart_156700 : Nat := 118140960795 + 156700 * 2 ^ 59
def prefixEnd_156700 : Nat := 4983230072969 + 3 ^ 40 * 156700 * 2
def baseEnd_156700 : Nat := 71522149830793017092761

theorem tailTrace_156700 : CollatzResearch.WordTrace tailWord_156700 prefixEnd_156700 71522149830793017092761 := by
  unfold tailWord_156700
  simp only [CollatzResearch.WordTrace]
  refine ⟨2857659266155068537229777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3810212354873424716306369 2857659266155068537229777)
  ·
    refine ⟨2143244449616301402922333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2857659266155068537229777 2143244449616301402922333)
    ·
      refine ⟨803716668606113026095875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2143244449616301402922333 803716668606113026095875)
      ·
        refine ⟨1205575002909169539143813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 803716668606113026095875 1205575002909169539143813)
        ·
          refine ⟨226045313045469288589465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1205575002909169539143813 226045313045469288589465)
          ·
            refine ⟨169533984784101966442099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226045313045469288589465 169533984784101966442099)
            ·
              refine ⟨254300977176152949663149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169533984784101966442099 254300977176152949663149)
              ·
                refine ⟨95362866441057356123681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 254300977176152949663149 95362866441057356123681)
                ·
                  refine ⟨71522149830793017092761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95362866441057356123681 71522149830793017092761)
                  ·
                    rfl

theorem cell20_156700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 2].length) (baseStart_156700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156700 prefixEnd_156700 := by exact prefixLift 156700
  have htrace : WordTrace (prefixWord ++ tailWord_156700) baseStart_156700 baseEnd_156700 := by
    simpa [prefixWord, tailWord_156700, baseEnd_156700] using wordTrace_append hprefix tailTrace_156700
  have hstable : (prefixWord ++ tailWord_156700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156700).length < 2 ^ (prefixWord ++ tailWord_156700).sum := by decide
  have hdescent : baseEnd_156700 < baseStart_156700 := by decide
  rcases family_descends (prefixWord ++ tailWord_156700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156711 : List Nat := [1, 1, 7, 1, 1, 1, 8]
def baseStart_156711 : Nat := 118140960795 + 156711 * 2 ^ 59
def prefixEnd_156711 : Nat := 4983230072969 + 3 ^ 40 * 156711 * 2
def baseEnd_156711 : Nat := 7947463392280651969561

theorem tailTrace_156711 : CollatzResearch.WordTrace tailWord_156711 prefixEnd_156711 7947463392280651969561 := by
  unfold tailWord_156711
  simp only [CollatzResearch.WordTrace]
  refine ⟨5715719735270285953109987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3810479823513523968739991 5715719735270285953109987)
  ·
    refine ⟨8573579602905428929664981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5715719735270285953109987 8573579602905428929664981)
    ·
      refine ⟨200943271943095990539023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 8573579602905428929664981 200943271943095990539023)
      ·
        refine ⟨301414907914643985808535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200943271943095990539023 301414907914643985808535)
        ·
          refine ⟨452122361871965978712803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301414907914643985808535 452122361871965978712803)
          ·
            refine ⟨678183542807948968069205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452122361871965978712803 678183542807948968069205)
            ·
              refine ⟨7947463392280651969561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 678183542807948968069205 7947463392280651969561)
              ·
                rfl

theorem cell20_156711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 8].length) (baseStart_156711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156711 prefixEnd_156711 := by exact prefixLift 156711
  have htrace : WordTrace (prefixWord ++ tailWord_156711) baseStart_156711 baseEnd_156711 := by
    simpa [prefixWord, tailWord_156711, baseEnd_156711] using wordTrace_append hprefix tailTrace_156711
  have hstable : (prefixWord ++ tailWord_156711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156711).length < 2 ^ (prefixWord ++ tailWord_156711).sum := by decide
  have hdescent : baseEnd_156711 < baseStart_156711 := by decide
  rcases family_descends (prefixWord ++ tailWord_156711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156718 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_156718 : Nat := 118140960795 + 156718 * 2 ^ 59
def prefixEnd_156718 : Nat := 4983230072969 + 3 ^ 40 * 156718 * 2
def baseEnd_156718 : Nat := 71530365521264954492687

theorem tailTrace_156718 : CollatzResearch.WordTrace tailWord_156718 prefixEnd_156718 71530365521264954492687 := by
  unfold tailWord_156718
  simp only [CollatzResearch.WordTrace]
  refine ⟨714496880780615768576851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3810650030829950765743205 714496880780615768576851)
  ·
    refine ⟨1071745321170923652865277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 714496880780615768576851 1071745321170923652865277)
    ·
      refine ⟨401904495439096369824479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1071745321170923652865277 401904495439096369824479)
      ·
        refine ⟨602856743158644554736719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401904495439096369824479 602856743158644554736719)
        ·
          refine ⟨904285114737966832105079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602856743158644554736719 904285114737966832105079)
          ·
            refine ⟨1356427672106950248157619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 904285114737966832105079 1356427672106950248157619)
            ·
              refine ⟨2034641508160425372236429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1356427672106950248157619 2034641508160425372236429)
              ·
                refine ⟨762990565560159514588661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2034641508160425372236429 762990565560159514588661)
                ·
                  refine ⟨71530365521264954492687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 762990565560159514588661 71530365521264954492687)
                  ·
                    rfl

theorem cell20_156718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_156718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156718 prefixEnd_156718 := by exact prefixLift 156718
  have htrace : WordTrace (prefixWord ++ tailWord_156718) baseStart_156718 baseEnd_156718 := by
    simpa [prefixWord, tailWord_156718, baseEnd_156718] using wordTrace_append hprefix tailTrace_156718
  have hstable : (prefixWord ++ tailWord_156718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156718).length < 2 ^ (prefixWord ++ tailWord_156718).sum := by decide
  have hdescent : baseEnd_156718 < baseStart_156718 := by decide
  rcases family_descends (prefixWord ++ tailWord_156718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156721 : List Nat := [1, 2, 2, 3, 1, 2, 5, 2, 2]
def baseStart_156721 : Nat := 118140960795 + 156721 * 2 ^ 59
def prefixEnd_156721 : Nat := 4983230072969 + 3 ^ 40 * 156721 * 2
def baseEnd_156721 : Nat := 71531734803010277392675

theorem tailTrace_156721 : CollatzResearch.WordTrace tailWord_156721 prefixEnd_156721 71531734803010277392675 := by
  unfold tailWord_156721
  simp only [CollatzResearch.WordTrace]
  refine ⟨5716084465234057660974017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3810722976822705107316011 5716084465234057660974017)
  ·
    refine ⟨4287063348925543245730513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5716084465234057660974017 4287063348925543245730513)
    ·
      refine ⟨3215297511694157434297885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4287063348925543245730513 3215297511694157434297885)
      ·
        refine ⟨1205736566885309037861707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3215297511694157434297885 1205736566885309037861707)
        ·
          refine ⟨1808604850327963556792561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1205736566885309037861707 1808604850327963556792561)
          ·
            refine ⟨1356453637745972667594421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1808604850327963556792561 1356453637745972667594421)
            ·
              refine ⟨127167528538684937586977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1356453637745972667594421 127167528538684937586977)
              ·
                refine ⟨95375646404013703190233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127167528538684937586977 95375646404013703190233)
                ·
                  refine ⟨71531734803010277392675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95375646404013703190233 71531734803010277392675)
                  ·
                    rfl

theorem cell20_156721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 2].length) (baseStart_156721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156721 prefixEnd_156721 := by exact prefixLift 156721
  have htrace : WordTrace (prefixWord ++ tailWord_156721) baseStart_156721 baseEnd_156721 := by
    simpa [prefixWord, tailWord_156721, baseEnd_156721] using wordTrace_append hprefix tailTrace_156721
  have hstable : (prefixWord ++ tailWord_156721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156721).length < 2 ^ (prefixWord ++ tailWord_156721).sum := by decide
  have hdescent : baseEnd_156721 < baseStart_156721 := by decide
  rcases family_descends (prefixWord ++ tailWord_156721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156732 : List Nat := [2, 2, 2, 2, 2, 2, 1, 7]
def baseStart_156732 : Nat := 118140960795 + 156732 * 2 ^ 59
def prefixEnd_156732 : Nat := 4983230072969 + 3 ^ 40 * 156732 * 2
def baseEnd_156732 : Nat := 23845585167581042675321

theorem tailTrace_156732 : CollatzResearch.WordTrace tailWord_156732 prefixEnd_156732 23845585167581042675321 := by
  unfold tailWord_156732
  simp only [CollatzResearch.WordTrace]
  refine ⟨2858242834097103269812225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3810990445462804359749633 2858242834097103269812225)
  ·
    refine ⟨2143682125572827452359169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2858242834097103269812225 2143682125572827452359169)
    ·
      refine ⟨1607761594179620589269377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2143682125572827452359169 1607761594179620589269377)
      ·
        refine ⟨1205821195634715441952033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1607761594179620589269377 1205821195634715441952033)
        ·
          refine ⟨904365896726036581464025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1205821195634715441952033 904365896726036581464025)
          ·
            refine ⟨678274422544527436098019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 904365896726036581464025 678274422544527436098019)
            ·
              refine ⟨1017411633816791154147029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678274422544527436098019 1017411633816791154147029)
              ·
                refine ⟨23845585167581042675321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1017411633816791154147029 23845585167581042675321)
                ·
                  rfl

theorem cell20_156732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_156732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156732 prefixEnd_156732 := by exact prefixLift 156732
  have htrace : WordTrace (prefixWord ++ tailWord_156732) baseStart_156732 baseEnd_156732 := by
    simpa [prefixWord, tailWord_156732, baseEnd_156732] using wordTrace_append hprefix tailTrace_156732
  have hstable : (prefixWord ++ tailWord_156732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156732).length < 2 ^ (prefixWord ++ tailWord_156732).sum := by decide
  have hdescent : baseEnd_156732 < baseStart_156732 := by decide
  rcases family_descends (prefixWord ++ tailWord_156732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156749 : List Nat := [1, 6, 1, 1, 1, 2, 2, 6]
def baseStart_156749 : Nat := 118140960795 + 156749 * 2 ^ 59
def prefixEnd_156749 : Nat := 4983230072969 + 3 ^ 40 * 156749 * 2
def baseEnd_156749 : Nat := 23848171588655541486409

theorem tailTrace_156749 : CollatzResearch.WordTrace tailWord_156749 prefixEnd_156749 23848171588655541486409 := by
  unfold tailWord_156749
  simp only [CollatzResearch.WordTrace]
  refine ⟨5717105709132618442993301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3811403806088412295328867 5717105709132618442993301)
  ·
    refine ⟨267989330115591489515311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5717105709132618442993301 267989330115591489515311)
    ·
      refine ⟨401983995173387234272967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267989330115591489515311 401983995173387234272967)
      ·
        refine ⟨602975992760080851409451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401983995173387234272967 602975992760080851409451)
        ·
          refine ⟨904463989140121277114177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602975992760080851409451 904463989140121277114177)
          ·
            refine ⟨678347991855090957835633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 904463989140121277114177 678347991855090957835633)
            ·
              refine ⟨508760993891318218376725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 678347991855090957835633 508760993891318218376725)
              ·
                refine ⟨23848171588655541486409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 508760993891318218376725 23848171588655541486409)
                ·
                  rfl

theorem cell20_156749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 6].length) (baseStart_156749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156749 prefixEnd_156749 := by exact prefixLift 156749
  have htrace : WordTrace (prefixWord ++ tailWord_156749) baseStart_156749 baseEnd_156749 := by
    simpa [prefixWord, tailWord_156749, baseEnd_156749] using wordTrace_append hprefix tailTrace_156749
  have hstable : (prefixWord ++ tailWord_156749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156749).length < 2 ^ (prefixWord ++ tailWord_156749).sum := by decide
  have hdescent : baseEnd_156749 < baseStart_156749 := by decide
  rcases family_descends (prefixWord ++ tailWord_156749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156766 : List Nat := [4, 4, 1, 1, 1, 9]
def baseStart_156766 : Nat := 118140960795 + 156766 * 2 ^ 59
def prefixEnd_156766 : Nat := 4983230072969 + 3 ^ 40 * 156766 * 2
def baseEnd_156766 : Nat := 2650084223303337810833

theorem tailTrace_156766 : CollatzResearch.WordTrace tailWord_156766 prefixEnd_156766 2650084223303337810833 := by
  unfold tailWord_156766
  simp only [CollatzResearch.WordTrace]
  refine ⟨714715718758878793295269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3811817166714020230908101 714715718758878793295269)
  ·
    refine ⟨134009197267289773742863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 714715718758878793295269 134009197267289773742863)
    ·
      refine ⟨201013795900934660614295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134009197267289773742863 201013795900934660614295)
      ·
        refine ⟨301520693851401990921443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201013795900934660614295 301520693851401990921443)
        ·
          refine ⟨452281040777102986382165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301520693851401990921443 452281040777102986382165)
          ·
            refine ⟨2650084223303337810833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 452281040777102986382165 2650084223303337810833)
            ·
              rfl

theorem cell20_156766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 9].length) (baseStart_156766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156766 prefixEnd_156766 := by exact prefixLift 156766
  have htrace : WordTrace (prefixWord ++ tailWord_156766) baseStart_156766 baseEnd_156766 := by
    simpa [prefixWord, tailWord_156766, baseEnd_156766] using wordTrace_append hprefix tailTrace_156766
  have hstable : (prefixWord ++ tailWord_156766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156766).length < 2 ^ (prefixWord ++ tailWord_156766).sum := by decide
  have hdescent : baseEnd_156766 < baseStart_156766 := by decide
  rcases family_descends (prefixWord ++ tailWord_156766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156776 : List Nat := [2, 1, 4, 4, 1, 1, 1, 4, 2]
def baseStart_156776 : Nat := 118140960795 + 156776 * 2 ^ 59
def prefixEnd_156776 : Nat := 4983230072969 + 3 ^ 40 * 156776 * 2
def baseEnd_156776 : Nat := 71556838301674530559117

theorem tailTrace_156776 : CollatzResearch.WordTrace tailWord_156776 prefixEnd_156776 71556838301674530559117 := by
  unfold tailWord_156776
  simp only [CollatzResearch.WordTrace]
  refine ⟨2859045240017401027113091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3812060320023201369484121 2859045240017401027113091)
  ·
    refine ⟨4288567860026101540669637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2859045240017401027113091 4288567860026101540669637)
    ·
      refine ⟨804106473754894038875557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4288567860026101540669637 804106473754894038875557)
      ·
        refine ⟨150769963829042632289167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 804106473754894038875557 150769963829042632289167)
        ·
          refine ⟨226154945743563948433751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150769963829042632289167 226154945743563948433751)
          ·
            refine ⟨339232418615345922650627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226154945743563948433751 339232418615345922650627)
            ·
              refine ⟨508848627923018883975941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339232418615345922650627 508848627923018883975941)
              ·
                refine ⟨95409117735566040745489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 508848627923018883975941 95409117735566040745489)
                ·
                  refine ⟨71556838301674530559117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95409117735566040745489 71556838301674530559117)
                  ·
                    rfl

theorem cell20_156776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 2].length) (baseStart_156776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156776 prefixEnd_156776 := by exact prefixLift 156776
  have htrace : WordTrace (prefixWord ++ tailWord_156776) baseStart_156776 baseEnd_156776 := by
    simpa [prefixWord, tailWord_156776, baseEnd_156776] using wordTrace_append hprefix tailTrace_156776
  have hstable : (prefixWord ++ tailWord_156776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156776).length < 2 ^ (prefixWord ++ tailWord_156776).sum := by decide
  have hdescent : baseEnd_156776 < baseStart_156776 := by decide
  rcases family_descends (prefixWord ++ tailWord_156776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156780 : List Nat := [2, 2, 1, 1, 3, 2, 3, 4, 2]
def baseStart_156780 : Nat := 118140960795 + 156780 * 2 ^ 59
def prefixEnd_156780 : Nat := 4983230072969 + 3 ^ 40 * 156780 * 2
def baseEnd_156780 : Nat := 71558664010668294425767

theorem tailTrace_156780 : CollatzResearch.WordTrace tailWord_156780 prefixEnd_156780 71558664010668294425767 := by
  unfold tailWord_156780
  simp only [CollatzResearch.WordTrace]
  refine ⟨2859118186010155368685897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3812157581346873824914529 2859118186010155368685897)
  ·
    refine ⟨2144338639507616526514423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2859118186010155368685897 2144338639507616526514423)
    ·
      refine ⟨3216507959261424789771635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2144338639507616526514423 3216507959261424789771635)
      ·
        refine ⟨4824761938892137184657453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3216507959261424789771635 4824761938892137184657453)
        ·
          refine ⟨1809285727084551444246545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4824761938892137184657453 1809285727084551444246545)
          ·
            refine ⟨1356964295313413583184909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1809285727084551444246545 1356964295313413583184909)
            ·
              refine ⟨508861610742530093694341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1356964295313413583184909 508861610742530093694341)
              ·
                refine ⟨95411552014224392567689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 508861610742530093694341 95411552014224392567689)
                ·
                  refine ⟨71558664010668294425767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95411552014224392567689 71558664010668294425767)
                  ·
                    rfl

theorem cell20_156780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 2].length) (baseStart_156780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156780 prefixEnd_156780 := by exact prefixLift 156780
  have htrace : WordTrace (prefixWord ++ tailWord_156780) baseStart_156780 baseEnd_156780 := by
    simpa [prefixWord, tailWord_156780, baseEnd_156780] using wordTrace_append hprefix tailTrace_156780
  have hstable : (prefixWord ++ tailWord_156780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156780).length < 2 ^ (prefixWord ++ tailWord_156780).sum := by decide
  have hdescent : baseEnd_156780 < baseStart_156780 := by decide
  rcases family_descends (prefixWord ++ tailWord_156780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156801 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 6]
def baseStart_156801 : Nat := 118140960795 + 156801 * 2 ^ 59
def prefixEnd_156801 : Nat := 4983230072969 + 3 ^ 40 * 156801 * 2
def baseEnd_156801 : Nat := 71568248982885554725681

theorem tailTrace_156801 : CollatzResearch.WordTrace tailWord_156801 prefixEnd_156801 71568248982885554725681 := by
  unfold tailWord_156801
  simp only [CollatzResearch.WordTrace]
  refine ⟨5719002304944231323886257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3812668203296154215924171 5719002304944231323886257)
  ·
    refine ⟨4289251728708173492914693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5719002304944231323886257 4289251728708173492914693)
    ·
      refine ⟨804234699132782529921505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4289251728708173492914693 804234699132782529921505)
      ·
        refine ⟨603176024349586897441129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 804234699132782529921505 603176024349586897441129)
        ·
          refine ⟨452382018262190173080847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 603176024349586897441129 452382018262190173080847)
          ·
            refine ⟨678573027393285259621271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452382018262190173080847 678573027393285259621271)
            ·
              refine ⟨1017859541089927889431907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678573027393285259621271 1017859541089927889431907)
              ·
                refine ⟨1526789311634891834147861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1017859541089927889431907 1526789311634891834147861)
                ·
                  refine ⟨71568248982885554725681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1526789311634891834147861 71568248982885554725681)
                  ·
                    rfl

theorem cell20_156801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_156801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156801 prefixEnd_156801 := by exact prefixLift 156801
  have htrace : WordTrace (prefixWord ++ tailWord_156801) baseStart_156801 baseEnd_156801 := by
    simpa [prefixWord, tailWord_156801, baseEnd_156801] using wordTrace_append hprefix tailTrace_156801
  have hstable : (prefixWord ++ tailWord_156801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156801).length < 2 ^ (prefixWord ++ tailWord_156801).sum := by decide
  have hdescent : baseEnd_156801 < baseStart_156801 := by decide
  rcases family_descends (prefixWord ++ tailWord_156801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156901 : List Nat := [1, 3, 1, 4, 3, 1, 2, 5]
def baseStart_156901 : Nat := 118140960795 + 156901 * 2 ^ 59
def prefixEnd_156901 : Nat := 4983230072969 + 3 ^ 40 * 156901 * 2
def baseEnd_156901 : Nat := 23871297235909883797313

theorem tailTrace_156901 : CollatzResearch.WordTrace tailWord_156901 prefixEnd_156901 23871297235909883797313 := by
  unfold tailWord_156901
  simp only [CollatzResearch.WordTrace]
  refine ⟨5722649604581948402526557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3815099736387965601684371 5722649604581948402526557)
  ·
    refine ⟨2145993601718230650947459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5722649604581948402526557 2145993601718230650947459)
    ·
      refine ⟨3218990402577345976421189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2145993601718230650947459 3218990402577345976421189)
      ·
        refine ⟨603560700483252370578973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3218990402577345976421189 603560700483252370578973)
        ·
          refine ⟨226335262681219638967115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 603560700483252370578973 226335262681219638967115)
          ·
            refine ⟨339502894021829458450673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226335262681219638967115 339502894021829458450673)
            ·
              refine ⟨254627170516372093838005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339502894021829458450673 254627170516372093838005)
              ·
                refine ⟨23871297235909883797313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 254627170516372093838005 23871297235909883797313)
                ·
                  rfl

theorem cell20_156901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 5].length) (baseStart_156901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156901 prefixEnd_156901 := by exact prefixLift 156901
  have htrace : WordTrace (prefixWord ++ tailWord_156901) baseStart_156901 baseEnd_156901 := by
    simpa [prefixWord, tailWord_156901, baseEnd_156901] using wordTrace_append hprefix tailTrace_156901
  have hstable : (prefixWord ++ tailWord_156901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156901).length < 2 ^ (prefixWord ++ tailWord_156901).sum := by decide
  have hdescent : baseEnd_156901 < baseStart_156901 := by decide
  rcases family_descends (prefixWord ++ tailWord_156901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156908 : List Nat := [2, 2, 1, 1, 2, 5, 1, 3, 3]
def baseStart_156908 : Nat := 118140960795 + 156908 * 2 ^ 59
def prefixEnd_156908 : Nat := 4983230072969 + 3 ^ 40 * 156908 * 2
def baseEnd_156908 : Nat := 71617086698468738158577

theorem tailTrace_156908 : CollatzResearch.WordTrace tailWord_156908 prefixEnd_156908 71617086698468738158577 := by
  unfold tailWord_156908
  simp only [CollatzResearch.WordTrace]
  refine ⟨2861452457778294299015689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3815269943704392398687585 2861452457778294299015689)
  ·
    refine ⟨2146089343333720724261767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2861452457778294299015689 2146089343333720724261767)
    ·
      refine ⟨3219134015000581086392651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2146089343333720724261767 3219134015000581086392651)
      ·
        refine ⟨4828701022500871629588977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3219134015000581086392651 4828701022500871629588977)
        ·
          refine ⟨3621525766875653722191733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4828701022500871629588977 3621525766875653722191733)
          ·
            refine ⟨339518040644592536455475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3621525766875653722191733 339518040644592536455475)
            ·
              refine ⟨509277060966888804683213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339518040644592536455475 509277060966888804683213)
              ·
                refine ⟨190978897862583301756205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 509277060966888804683213 190978897862583301756205)
                ·
                  refine ⟨71617086698468738158577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190978897862583301756205 71617086698468738158577)
                  ·
                    rfl

theorem cell20_156908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_156908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156908 prefixEnd_156908 := by exact prefixLift 156908
  have htrace : WordTrace (prefixWord ++ tailWord_156908) baseStart_156908 baseEnd_156908 := by
    simpa [prefixWord, tailWord_156908, baseEnd_156908] using wordTrace_append hprefix tailTrace_156908
  have hstable : (prefixWord ++ tailWord_156908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156908).length < 2 ^ (prefixWord ++ tailWord_156908).sum := by decide
  have hdescent : baseEnd_156908 < baseStart_156908 := by decide
  rcases family_descends (prefixWord ++ tailWord_156908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156970 : List Nat := [3, 1, 4, 2, 1, 2, 1, 2, 4]
def baseStart_156970 : Nat := 118140960795 + 156970 * 2 ^ 59
def prefixEnd_156970 : Nat := 4983230072969 + 3 ^ 40 * 156970 * 2
def baseEnd_156970 : Nat := 71645385187872078091657

theorem tailTrace_156970 : CollatzResearch.WordTrace tailWord_156970 prefixEnd_156970 71645385187872078091657 := by
  unfold tailWord_156970
  simp only [CollatzResearch.WordTrace]
  refine ⟨1431291560332993296697091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3816777494221315457858909 1431291560332993296697091)
  ·
    refine ⟨2146937340499489945045637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1431291560332993296697091 2146937340499489945045637)
    ·
      refine ⟨402550751343654364696057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2146937340499489945045637 402550751343654364696057)
      ·
        refine ⟨301913063507740773522043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 402550751343654364696057 301913063507740773522043)
        ·
          refine ⟨452869595261611160283065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301913063507740773522043 452869595261611160283065)
          ·
            refine ⟨339652196446208370212299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 452869595261611160283065 339652196446208370212299)
            ·
              refine ⟨509478294669312555318449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339652196446208370212299 509478294669312555318449)
              ·
                refine ⟨382108721001984416488837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 509478294669312555318449 382108721001984416488837)
                ·
                  refine ⟨71645385187872078091657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 382108721001984416488837 71645385187872078091657)
                  ·
                    rfl

theorem cell20_156970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_156970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156970 prefixEnd_156970 := by exact prefixLift 156970
  have htrace : WordTrace (prefixWord ++ tailWord_156970) baseStart_156970 baseEnd_156970 := by
    simpa [prefixWord, tailWord_156970, baseEnd_156970] using wordTrace_append hprefix tailTrace_156970
  have hstable : (prefixWord ++ tailWord_156970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156970).length < 2 ^ (prefixWord ++ tailWord_156970).sum := by decide
  have hdescent : baseEnd_156970 < baseStart_156970 := by decide
  rcases family_descends (prefixWord ++ tailWord_156970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156977 : List Nat := [1, 2, 2, 3, 3, 2, 3, 4]
def baseStart_156977 : Nat := 118140960795 + 156977 * 2 ^ 59
def prefixEnd_156977 : Nat := 4983230072969 + 3 ^ 40 * 156977 * 2
def baseEnd_156977 : Nat := 23882860059537054952765

theorem tailTrace_156977 : CollatzResearch.WordTrace tailWord_156977 prefixEnd_156977 23882860059537054952765 := by
  unfold tailWord_156977
  simp only [CollatzResearch.WordTrace]
  refine ⟨5725421552306613382293185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3816947701537742254862123 5725421552306613382293185)
  ·
    refine ⟨4294066164229960036719889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5725421552306613382293185 4294066164229960036719889)
    ·
      refine ⟨3220549623172470027539917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4294066164229960036719889 3220549623172470027539917)
      ·
        refine ⟨1207706108689676260327469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3220549623172470027539917 1207706108689676260327469)
        ·
          refine ⟨452889790758628597622801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1207706108689676260327469 452889790758628597622801)
          ·
            refine ⟨339667343068971448217101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 452889790758628597622801 339667343068971448217101)
            ·
              refine ⟨127375253650864293081413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 339667343068971448217101 127375253650864293081413)
              ·
                refine ⟨23882860059537054952765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127375253650864293081413 23882860059537054952765)
                ·
                  rfl

theorem cell20_156977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 4].length) (baseStart_156977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_156977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_156977 prefixEnd_156977 := by exact prefixLift 156977
  have htrace : WordTrace (prefixWord ++ tailWord_156977) baseStart_156977 baseEnd_156977 := by
    simpa [prefixWord, tailWord_156977, baseEnd_156977] using wordTrace_append hprefix tailTrace_156977
  have hstable : (prefixWord ++ tailWord_156977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156977).length < 2 ^ (prefixWord ++ tailWord_156977).sum := by decide
  have hdescent : baseEnd_156977 < baseStart_156977 := by decide
  rcases family_descends (prefixWord ++ tailWord_156977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157032 : List Nat := [2, 1, 4, 2, 3, 2, 2, 4]
def baseStart_157032 : Nat := 118140960795 + 157032 * 2 ^ 59
def prefixEnd_157032 : Nat := 4983230072969 + 3 ^ 40 * 157032 * 2
def baseEnd_157032 : Nat := 23891227892425139341579

theorem tailTrace_157032 : CollatzResearch.WordTrace tailWord_157032 prefixEnd_157032 23891227892425139341579 := by
  unfold tailWord_157032
  simp only [CollatzResearch.WordTrace]
  refine ⟨2863713783553678887772675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3818285044738238517030233 2863713783553678887772675)
  ·
    refine ⟨4295570675330518331659013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2863713783553678887772675 4295570675330518331659013)
    ·
      refine ⟨805419501624472187186065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4295570675330518331659013 805419501624472187186065)
      ·
        refine ⟨604064626218354140389549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 805419501624472187186065 604064626218354140389549)
        ·
          refine ⟨226524234831882802646081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 604064626218354140389549 226524234831882802646081)
          ·
            refine ⟨169893176123912101984561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226524234831882802646081 169893176123912101984561)
            ·
              refine ⟨127419882092934076488421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169893176123912101984561 127419882092934076488421)
              ·
                refine ⟨23891227892425139341579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127419882092934076488421 23891227892425139341579)
                ·
                  rfl

theorem cell20_157032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 4].length) (baseStart_157032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157032 prefixEnd_157032 := by exact prefixLift 157032
  have htrace : WordTrace (prefixWord ++ tailWord_157032) baseStart_157032 baseEnd_157032 := by
    simpa [prefixWord, tailWord_157032, baseEnd_157032] using wordTrace_append hprefix tailTrace_157032
  have hstable : (prefixWord ++ tailWord_157032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157032).length < 2 ^ (prefixWord ++ tailWord_157032).sum := by decide
  have hdescent : baseEnd_157032 < baseStart_157032 := by decide
  rcases family_descends (prefixWord ++ tailWord_157032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157036 : List Nat := [2, 2, 1, 1, 5, 2, 1, 6]
def baseStart_157036 : Nat := 118140960795 + 157036 * 2 ^ 59
def prefixEnd_157036 : Nat := 4983230072969 + 3 ^ 40 * 157036 * 2
def baseEnd_157036 : Nat := 23891836462089727297129

theorem tailTrace_157036 : CollatzResearch.WordTrace tailWord_157036 prefixEnd_157036 23891836462089727297129 := by
  unfold tailWord_157036
  simp only [CollatzResearch.WordTrace]
  refine ⟨2863786729546433229345481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3818382306061910972460641 2863786729546433229345481)
  ·
    refine ⟨2147840047159824922009111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2863786729546433229345481 2147840047159824922009111)
    ·
      refine ⟨3221760070739737383013667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2147840047159824922009111 3221760070739737383013667)
      ·
        refine ⟨4832640106109606074520501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3221760070739737383013667 4832640106109606074520501)
        ·
          refine ⟨453060009947775569486297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4832640106109606074520501 453060009947775569486297)
          ·
            refine ⟨339795007460831677114723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 453060009947775569486297 339795007460831677114723)
            ·
              refine ⟨509692511191247515672085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339795007460831677114723 509692511191247515672085)
              ·
                refine ⟨23891836462089727297129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 509692511191247515672085 23891836462089727297129)
                ·
                  rfl

theorem cell20_157036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_157036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157036 prefixEnd_157036 := by exact prefixLift 157036
  have htrace : WordTrace (prefixWord ++ tailWord_157036) baseStart_157036 baseEnd_157036 := by
    simpa [prefixWord, tailWord_157036, baseEnd_157036] using wordTrace_append hprefix tailTrace_157036
  have hstable : (prefixWord ++ tailWord_157036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157036).length < 2 ^ (prefixWord ++ tailWord_157036).sum := by decide
  have hdescent : baseEnd_157036 < baseStart_157036 := by decide
  rcases family_descends (prefixWord ++ tailWord_157036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157063 : List Nat := [1, 1, 4, 2, 2, 3, 3, 2, 2]
def baseStart_157063 : Nat := 118140960795 + 157063 * 2 ^ 59
def prefixEnd_157063 : Nat := 4983230072969 + 3 ^ 40 * 157063 * 2
def baseEnd_157063 : Nat := 71687832921977087991277

theorem tailTrace_157063 : CollatzResearch.WordTrace tailWord_157063 prefixEnd_157063 71687832921977087991277 := by
  unfold tailWord_157063
  simp only [CollatzResearch.WordTrace]
  refine ⟨5728558229995050069923843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3819038819996700046615895 5728558229995050069923843)
  ·
    refine ⟨8592837344992575104885765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5728558229995050069923843 8592837344992575104885765)
    ·
      refine ⟨1611157002186107832166081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8592837344992575104885765 1611157002186107832166081)
      ·
        refine ⟨1208367751639580874124561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1611157002186107832166081 1208367751639580874124561)
        ·
          refine ⟨906275813729685655593421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1208367751639580874124561 906275813729685655593421)
          ·
            refine ⟨339853430148632120847533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 906275813729685655593421 339853430148632120847533)
            ·
              refine ⟨127445036305737045317825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 339853430148632120847533 127445036305737045317825)
              ·
                refine ⟨95583777229302783988369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127445036305737045317825 95583777229302783988369)
                ·
                  refine ⟨71687832921977087991277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95583777229302783988369 71687832921977087991277)
                  ·
                    rfl

theorem cell20_157063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 2].length) (baseStart_157063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157063 prefixEnd_157063 := by exact prefixLift 157063
  have htrace : WordTrace (prefixWord ++ tailWord_157063) baseStart_157063 baseEnd_157063 := by
    simpa [prefixWord, tailWord_157063, baseEnd_157063] using wordTrace_append hprefix tailTrace_157063
  have hstable : (prefixWord ++ tailWord_157063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157063).length < 2 ^ (prefixWord ++ tailWord_157063).sum := by decide
  have hdescent : baseEnd_157063 < baseStart_157063 := by decide
  rcases family_descends (prefixWord ++ tailWord_157063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157088 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 6]
def baseStart_157088 : Nat := 118140960795 + 157088 * 2 ^ 59
def prefixEnd_157088 : Nat := 4983230072969 + 3 ^ 40 * 157088 * 2
def baseEnd_157088 : Nat := 71699243603188112157841

theorem tailTrace_157088 : CollatzResearch.WordTrace tailWord_157088 prefixEnd_157088 71699243603188112157841 := by
  unfold tailWord_157088
  simp only [CollatzResearch.WordTrace]
  refine ⟨2864735027452239669791959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3819646703269652893055945 2864735027452239669791959)
  ·
    refine ⟨4297102541178359504687939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2864735027452239669791959 4297102541178359504687939)
    ·
      refine ⟨6445653811767539257031909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4297102541178359504687939 6445653811767539257031909)
      ·
        refine ⟨1208560089706413610693483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6445653811767539257031909 1208560089706413610693483)
        ·
          refine ⟨1812840134559620416040225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1208560089706413610693483 1812840134559620416040225)
          ·
            refine ⟨1359630100919715312030169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1812840134559620416040225 1359630100919715312030169)
            ·
              refine ⟨1019722575689786484022627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1359630100919715312030169 1019722575689786484022627)
              ·
                refine ⟨1529583863534679726033941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1019722575689786484022627 1529583863534679726033941)
                ·
                  refine ⟨71699243603188112157841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1529583863534679726033941 71699243603188112157841)
                  ·
                    rfl

theorem cell20_157088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_157088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157088 prefixEnd_157088 := by exact prefixLift 157088
  have htrace : WordTrace (prefixWord ++ tailWord_157088) baseStart_157088 baseEnd_157088 := by
    simpa [prefixWord, tailWord_157088, baseEnd_157088] using wordTrace_append hprefix tailTrace_157088
  have hstable : (prefixWord ++ tailWord_157088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157088).length < 2 ^ (prefixWord ++ tailWord_157088).sum := by decide
  have hdescent : baseEnd_157088 < baseStart_157088 := by decide
  rcases family_descends (prefixWord ++ tailWord_157088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157160 : List Nat := [2, 1, 4, 1, 1, 2, 4, 3, 2]
def baseStart_157160 : Nat := 118140960795 + 157160 * 2 ^ 59
def prefixEnd_157160 : Nat := 4983230072969 + 3 ^ 40 * 157160 * 2
def baseEnd_157160 : Nat := 71732106365075861757547

theorem tailTrace_157160 : CollatzResearch.WordTrace tailWord_157160 prefixEnd_157160 71732106365075861757547 := by
  unfold tailWord_157160
  simp only [CollatzResearch.WordTrace]
  refine ⟨2866048055321817818102467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3821397407095757090803289 2866048055321817818102467)
  ·
    refine ⟨4299072082982726727153701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2866048055321817818102467 4299072082982726727153701)
    ·
      refine ⟨806076015559261261341319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4299072082982726727153701 806076015559261261341319)
      ·
        refine ⟨1209114023338891892011979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 806076015559261261341319 1209114023338891892011979)
        ·
          refine ⟨1813671035008337838017969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1209114023338891892011979 1813671035008337838017969)
          ·
            refine ⟨1360253276256253378513477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1813671035008337838017969 1360253276256253378513477)
            ·
              refine ⟨255047489298047508471277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1360253276256253378513477 255047489298047508471277)
              ·
                refine ⟨95642808486767815676729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 255047489298047508471277 95642808486767815676729)
                ·
                  refine ⟨71732106365075861757547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95642808486767815676729 71732106365075861757547)
                  ·
                    rfl

theorem cell20_157160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 2].length) (baseStart_157160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157160 prefixEnd_157160 := by exact prefixLift 157160
  have htrace : WordTrace (prefixWord ++ tailWord_157160) baseStart_157160 baseEnd_157160 := by
    simpa [prefixWord, tailWord_157160, baseEnd_157160] using wordTrace_append hprefix tailTrace_157160
  have hstable : (prefixWord ++ tailWord_157160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157160).length < 2 ^ (prefixWord ++ tailWord_157160).sum := by decide
  have hdescent : baseEnd_157160 < baseStart_157160 := by decide
  rcases family_descends (prefixWord ++ tailWord_157160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157174 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_157174 : Nat := 118140960795 + 157174 * 2 ^ 59
def prefixEnd_157174 : Nat := 4983230072969 + 3 ^ 40 * 157174 * 2
def baseEnd_157174 : Nat := 71738496346554035290823

theorem tailTrace_157174 : CollatzResearch.WordTrace tailWord_157174 prefixEnd_157174 71738496346554035290823 := by
  unfold tailWord_157174
  simp only [CollatzResearch.WordTrace]
  refine ⟨358287920787057251700911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3821737821728610684809717 358287920787057251700911)
  ·
    refine ⟨537431881180585877551367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 358287920787057251700911 537431881180585877551367)
    ·
      refine ⟨806147821770878816327051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 537431881180585877551367 806147821770878816327051)
      ·
        refine ⟨1209221732656318224490577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 806147821770878816327051 1209221732656318224490577)
        ·
          refine ⟨906916299492238668367933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1209221732656318224490577 906916299492238668367933)
          ·
            refine ⟨340093612309589500637975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 906916299492238668367933 340093612309589500637975)
            ·
              refine ⟨510140418464384250956963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340093612309589500637975 510140418464384250956963)
              ·
                refine ⟨765210627696576376435445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510140418464384250956963 765210627696576376435445)
                ·
                  refine ⟨71738496346554035290823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 765210627696576376435445 71738496346554035290823)
                  ·
                    rfl

theorem cell20_157174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_157174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157174 prefixEnd_157174 := by exact prefixLift 157174
  have htrace : WordTrace (prefixWord ++ tailWord_157174) baseStart_157174 baseEnd_157174 := by
    simpa [prefixWord, tailWord_157174, baseEnd_157174] using wordTrace_append hprefix tailTrace_157174
  have hstable : (prefixWord ++ tailWord_157174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157174).length < 2 ^ (prefixWord ++ tailWord_157174).sum := by decide
  have hdescent : baseEnd_157174 < baseStart_157174 := by decide
  rcases family_descends (prefixWord ++ tailWord_157174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157181 : List Nat := [1, 4, 1, 1, 1, 5, 2, 1, 4]
def baseStart_157181 : Nat := 118140960795 + 157181 * 2 ^ 59
def prefixEnd_157181 : Nat := 4983230072969 + 3 ^ 40 * 157181 * 2
def baseEnd_157181 : Nat := 71741691337293122057461

theorem tailTrace_157181 : CollatzResearch.WordTrace tailWord_157181 prefixEnd_157181 71741691337293122057461 := by
  unfold tailWord_157181
  simp only [CollatzResearch.WordTrace]
  refine ⟨5732862043567556222719397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3821908029045037481812931 5732862043567556222719397)
  ·
    refine ⟨1074911633168916791759887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5732862043567556222719397 1074911633168916791759887)
    ·
      refine ⟨1612367449753375187639831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1074911633168916791759887 1612367449753375187639831)
      ·
        refine ⟨2418551174630062781459747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1612367449753375187639831 2418551174630062781459747)
        ·
          refine ⟨3627826761945094172189621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2418551174630062781459747 3627826761945094172189621)
          ·
            refine ⟨340108758932352578642777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3627826761945094172189621 340108758932352578642777)
            ·
              refine ⟨255081569199264433982083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 340108758932352578642777 255081569199264433982083)
              ·
                refine ⟨382622353798896650973125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255081569199264433982083 382622353798896650973125)
                ·
                  refine ⟨71741691337293122057461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 382622353798896650973125 71741691337293122057461)
                  ·
                    rfl

theorem cell20_157181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_157181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157181 prefixEnd_157181 := by exact prefixLift 157181
  have htrace : WordTrace (prefixWord ++ tailWord_157181) baseStart_157181 baseEnd_157181 := by
    simpa [prefixWord, tailWord_157181, baseEnd_157181] using wordTrace_append hprefix tailTrace_157181
  have hstable : (prefixWord ++ tailWord_157181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157181).length < 2 ^ (prefixWord ++ tailWord_157181).sum := by decide
  have hdescent : baseEnd_157181 < baseStart_157181 := by decide
  rcases family_descends (prefixWord ++ tailWord_157181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157191 : List Nat := [1, 1, 4, 3, 2, 2, 3, 1, 3]
def baseStart_157191 : Nat := 118140960795 + 157191 * 2 ^ 59
def prefixEnd_157191 : Nat := 4983230072969 + 3 ^ 40 * 157191 * 2
def baseEnd_157191 : Nat := 71746255609777531724087

theorem tailTrace_157191 : CollatzResearch.WordTrace tailWord_157191 prefixEnd_157191 71746255609777531724087 := by
  unfold tailWord_157191
  simp only [CollatzResearch.WordTrace]
  refine ⟨5733226773531327930583427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3822151182354218620388951 5733226773531327930583427)
  ·
    refine ⟨8599840160296991895875141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5733226773531327930583427 8599840160296991895875141)
    ·
      refine ⟨1612470030055685980476589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8599840160296991895875141 1612470030055685980476589)
      ·
        refine ⟨604676261270882242678721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1612470030055685980476589 604676261270882242678721)
        ·
          refine ⟨453507195953161682009041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 604676261270882242678721 453507195953161682009041)
          ·
            refine ⟨340130396964871261506781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 453507195953161682009041 340130396964871261506781)
            ·
              refine ⟨127548898861826723065043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 340130396964871261506781 127548898861826723065043)
              ·
                refine ⟨191323348292740084597565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127548898861826723065043 191323348292740084597565)
                ·
                  refine ⟨71746255609777531724087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191323348292740084597565 71746255609777531724087)
                  ·
                    rfl

theorem cell20_157191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 3].length) (baseStart_157191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157191 prefixEnd_157191 := by exact prefixLift 157191
  have htrace : WordTrace (prefixWord ++ tailWord_157191) baseStart_157191 baseEnd_157191 := by
    simpa [prefixWord, tailWord_157191, baseEnd_157191] using wordTrace_append hprefix tailTrace_157191
  have hstable : (prefixWord ++ tailWord_157191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157191).length < 2 ^ (prefixWord ++ tailWord_157191).sum := by decide
  have hdescent : baseEnd_157191 < baseStart_157191 := by decide
  rcases family_descends (prefixWord ++ tailWord_157191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157205 : List Nat := [1, 3, 2, 1, 3, 4, 2, 4]
def baseStart_157205 : Nat := 118140960795 + 157205 * 2 ^ 59
def prefixEnd_157205 : Nat := 4983230072969 + 3 ^ 40 * 157205 * 2
def baseEnd_157205 : Nat := 23917548530418568419121

theorem tailTrace_157205 : CollatzResearch.WordTrace tailWord_157205 prefixEnd_157205 23917548530418568419121 := by
  unfold tailWord_157205
  simp only [CollatzResearch.WordTrace]
  refine ⟨5733737395480608321593069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3822491596987072214395379 5733737395480608321593069)
  ·
    refine ⟨2150151523305228120597401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5733737395480608321593069 2150151523305228120597401)
    ·
      refine ⟨1612613642478921090448051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2150151523305228120597401 1612613642478921090448051)
      ·
        refine ⟨2418920463718381635672077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1612613642478921090448051 2418920463718381635672077)
        ·
          refine ⟨907095173894393113377029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2418920463718381635672077 907095173894393113377029)
          ·
            refine ⟨170080345105198708758193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 907095173894393113377029 170080345105198708758193)
            ·
              refine ⟨127560258828899031568645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170080345105198708758193 127560258828899031568645)
              ·
                refine ⟨23917548530418568419121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127560258828899031568645 23917548530418568419121)
                ·
                  rfl

theorem cell20_157205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 4].length) (baseStart_157205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157205 prefixEnd_157205 := by exact prefixLift 157205
  have htrace : WordTrace (prefixWord ++ tailWord_157205) baseStart_157205 baseEnd_157205 := by
    simpa [prefixWord, tailWord_157205, baseEnd_157205] using wordTrace_append hprefix tailTrace_157205
  have hstable : (prefixWord ++ tailWord_157205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157205).length < 2 ^ (prefixWord ++ tailWord_157205).sum := by decide
  have hdescent : baseEnd_157205 < baseStart_157205 := by decide
  rcases family_descends (prefixWord ++ tailWord_157205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157233 : List Nat := [1, 2, 2, 3, 1, 1, 1, 6, 3]
def baseStart_157233 : Nat := 118140960795 + 157233 * 2 ^ 59
def prefixEnd_157233 : Nat := 4983230072969 + 3 ^ 40 * 157233 * 2
def baseEnd_157233 : Nat := 71765425554212052323915

theorem tailTrace_157233 : CollatzResearch.WordTrace tailWord_157233 prefixEnd_157233 71765425554212052323915 := by
  unfold tailWord_157233
  simp only [CollatzResearch.WordTrace]
  refine ⟨5734758639379169103612353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3823172426252779402408235 5734758639379169103612353)
  ·
    refine ⟨4301068979534376827709265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5734758639379169103612353 4301068979534376827709265)
    ·
      refine ⟨3225801734650782620781949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4301068979534376827709265 3225801734650782620781949)
      ·
        refine ⟨1209675650494043482793231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3225801734650782620781949 1209675650494043482793231)
        ·
          refine ⟨1814513475741065224189847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1209675650494043482793231 1814513475741065224189847)
          ·
            refine ⟨2721770213611597836284771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1814513475741065224189847 2721770213611597836284771)
            ·
              refine ⟨4082655320417396754427157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2721770213611597836284771 4082655320417396754427157)
              ·
                refine ⟨191374468144565472863773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4082655320417396754427157 191374468144565472863773)
                ·
                  refine ⟨71765425554212052323915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191374468144565472863773 71765425554212052323915)
                  ·
                    rfl

theorem cell20_157233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 3].length) (baseStart_157233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157233 prefixEnd_157233 := by exact prefixLift 157233
  have htrace : WordTrace (prefixWord ++ tailWord_157233) baseStart_157233 baseEnd_157233 := by
    simpa [prefixWord, tailWord_157233, baseEnd_157233] using wordTrace_append hprefix tailTrace_157233
  have hstable : (prefixWord ++ tailWord_157233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157233).length < 2 ^ (prefixWord ++ tailWord_157233).sum := by decide
  have hdescent : baseEnd_157233 < baseStart_157233 := by decide
  rcases family_descends (prefixWord ++ tailWord_157233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157247 : List Nat := [1, 1, 2, 2, 3, 3, 1, 7]
def baseStart_157247 : Nat := 118140960795 + 157247 * 2 ^ 59
def prefixEnd_157247 : Nat := 4983230072969 + 3 ^ 40 * 157247 * 2
def baseEnd_157247 : Nat := 23923938511896741952397

theorem tailTrace_157247 : CollatzResearch.WordTrace tailWord_157247 prefixEnd_157247 23923938511896741952397 := by
  unfold tailWord_157247
  simp only [CollatzResearch.WordTrace]
  refine ⟨5735269261328449494621995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3823512840885632996414663 5735269261328449494621995)
  ·
    refine ⟨8602903891992674241932993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5735269261328449494621995 8602903891992674241932993)
    ·
      refine ⟨6452177918994505681449745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8602903891992674241932993 6452177918994505681449745)
      ·
        refine ⟨4839133439245879261087309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6452177918994505681449745 4839133439245879261087309)
        ·
          refine ⟨1814675039717204722907741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4839133439245879261087309 1814675039717204722907741)
          ·
            refine ⟨680503139893951771090403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1814675039717204722907741 680503139893951771090403)
            ·
              refine ⟨1020754709840927656635605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680503139893951771090403 1020754709840927656635605)
              ·
                refine ⟨23923938511896741952397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1020754709840927656635605 23923938511896741952397)
                ·
                  rfl

theorem cell20_157247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 7].length) (baseStart_157247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157247 prefixEnd_157247 := by exact prefixLift 157247
  have htrace : WordTrace (prefixWord ++ tailWord_157247) baseStart_157247 baseEnd_157247 := by
    simpa [prefixWord, tailWord_157247, baseEnd_157247] using wordTrace_append hprefix tailTrace_157247
  have hstable : (prefixWord ++ tailWord_157247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157247).length < 2 ^ (prefixWord ++ tailWord_157247).sum := by decide
  have hdescent : baseEnd_157247 < baseStart_157247 := by decide
  rcases family_descends (prefixWord ++ tailWord_157247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157285 : List Nat := [1, 3, 1, 3, 3, 9]
def baseStart_157285 : Nat := 118140960795 + 157285 * 2 ^ 59
def prefixEnd_157285 : Nat := 4983230072969 + 3 ^ 40 * 157285 * 2
def baseEnd_157285 : Nat := 2658857769301147503347

theorem tailTrace_157285 : CollatzResearch.WordTrace tailWord_157285 prefixEnd_157285 2658857769301147503347 := by
  unfold tailWord_157285
  simp only [CollatzResearch.WordTrace]
  refine ⟨5736655235190781984505309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3824436823460521323003539 5736655235190781984505309)
  ·
    refine ⟨2151245713196543244189491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5736655235190781984505309 2151245713196543244189491)
    ·
      refine ⟨3226868569794814866284237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2151245713196543244189491 3226868569794814866284237)
      ·
        refine ⟨1210075713673055574856589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3226868569794814866284237 1210075713673055574856589)
        ·
          refine ⟨453778392627395840571221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1210075713673055574856589 453778392627395840571221)
          ·
            refine ⟨2658857769301147503347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 453778392627395840571221 2658857769301147503347)
            ·
              rfl

theorem cell20_157285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 9].length) (baseStart_157285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157285 prefixEnd_157285 := by exact prefixLift 157285
  have htrace : WordTrace (prefixWord ++ tailWord_157285) baseStart_157285 baseEnd_157285 := by
    simpa [prefixWord, tailWord_157285, baseEnd_157285] using wordTrace_append hprefix tailTrace_157285
  have hstable : (prefixWord ++ tailWord_157285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157285).length < 2 ^ (prefixWord ++ tailWord_157285).sum := by decide
  have hdescent : baseEnd_157285 < baseStart_157285 := by decide
  rcases family_descends (prefixWord ++ tailWord_157285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157288 : List Nat := [2, 1, 4, 3, 1, 1, 1, 4, 3]
def baseStart_157288 : Nat := 118140960795 + 157288 * 2 ^ 59
def prefixEnd_157288 : Nat := 4983230072969 + 3 ^ 40 * 157288 * 2
def baseEnd_157288 : Nat := 71790529052876305490357

theorem tailTrace_157288 : CollatzResearch.WordTrace tailWord_157288 prefixEnd_157288 71790529052876305490357 := by
  unfold tailWord_157288
  simp only [CollatzResearch.WordTrace]
  refine ⟨2868382327089956748432259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3824509769453275664576345 2868382327089956748432259)
  ·
    refine ⟨4302573490634935122648389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2868382327089956748432259 4302573490634935122648389)
    ·
      refine ⟨806732529494050335496573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4302573490634935122648389 806732529494050335496573)
      ·
        refine ⟨302524698560268875811215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 806732529494050335496573 302524698560268875811215)
        ·
          refine ⟨453787047840403313716823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302524698560268875811215 453787047840403313716823)
          ·
            refine ⟨680680571760604970575235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453787047840403313716823 680680571760604970575235)
            ·
              refine ⟨1021020857640907455862853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680680571760604970575235 1021020857640907455862853)
              ·
                refine ⟨191441410807670147974285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1021020857640907455862853 191441410807670147974285)
                ·
                  refine ⟨71790529052876305490357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191441410807670147974285 71790529052876305490357)
                  ·
                    rfl

theorem cell20_157288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 3].length) (baseStart_157288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157288 prefixEnd_157288 := by exact prefixLift 157288
  have htrace : WordTrace (prefixWord ++ tailWord_157288) baseStart_157288 baseEnd_157288 := by
    simpa [prefixWord, tailWord_157288, baseEnd_157288] using wordTrace_append hprefix tailTrace_157288
  have hstable : (prefixWord ++ tailWord_157288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157288).length < 2 ^ (prefixWord ++ tailWord_157288).sum := by decide
  have hdescent : baseEnd_157288 < baseStart_157288 := by decide
  rcases family_descends (prefixWord ++ tailWord_157288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157340 : List Nat := [2, 2, 3, 2, 3, 1, 7]
def baseStart_157340 : Nat := 118140960795 + 157340 * 2 ^ 59
def prefixEnd_157340 : Nat := 4983230072969 + 3 ^ 40 * 157340 * 2
def baseEnd_157340 : Nat := 7979362585532803972979

theorem tailTrace_157340 : CollatzResearch.WordTrace tailWord_157340 prefixEnd_157340 7979362585532803972979 := by
  unfold tailWord_157340
  simp only [CollatzResearch.WordTrace]
  refine ⟨2869330624995763188878737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3825774166661017585171649 2869330624995763188878737)
  ·
    refine ⟨2151997968746822391659053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2869330624995763188878737 2151997968746822391659053)
    ·
      refine ⟨806999238280058396872145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2151997968746822391659053 806999238280058396872145)
      ·
        refine ⟨605249428710043797654109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 806999238280058396872145 605249428710043797654109)
        ·
          refine ⟨226968535766266424120291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 605249428710043797654109 226968535766266424120291)
          ·
            refine ⟨340452803649399636180437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226968535766266424120291 340452803649399636180437)
            ·
              refine ⟨7979362585532803972979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 340452803649399636180437 7979362585532803972979)
              ·
                rfl

theorem cell20_157340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 7].length) (baseStart_157340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157340 prefixEnd_157340 := by exact prefixLift 157340
  have htrace : WordTrace (prefixWord ++ tailWord_157340) baseStart_157340 baseEnd_157340 := by
    simpa [prefixWord, tailWord_157340, baseEnd_157340] using wordTrace_append hprefix tailTrace_157340
  have hstable : (prefixWord ++ tailWord_157340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157340).length < 2 ^ (prefixWord ++ tailWord_157340).sum := by decide
  have hdescent : baseEnd_157340 < baseStart_157340 := by decide
  rcases family_descends (prefixWord ++ tailWord_157340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157405 : List Nat := [1, 4, 3, 3, 1, 2, 1, 1, 4]
def baseStart_157405 : Nat := 118140960795 + 157405 * 2 ^ 59
def prefixEnd_157405 : Nat := 4983230072969 + 3 ^ 40 * 157405 * 2
def baseEnd_157405 : Nat := 71843931040943898589879

theorem tailTrace_157405 : CollatzResearch.WordTrace tailWord_157405 prefixEnd_157405 71843931040943898589879 := by
  unfold tailWord_157405
  simp only [CollatzResearch.WordTrace]
  refine ⟨5741031994756042478873669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3827354663170694985915779 5741031994756042478873669)
  ·
    refine ⟨1076443499016757964788813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5741031994756042478873669 1076443499016757964788813)
    ·
      refine ⟨403666312131284236795805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1076443499016757964788813 403666312131284236795805)
      ·
        refine ⟨151374867049231588798427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 403666312131284236795805 151374867049231588798427)
        ·
          refine ⟨227062300573847383197641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151374867049231588798427 227062300573847383197641)
          ·
            refine ⟨170296725430385537398231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227062300573847383197641 170296725430385537398231)
            ·
              refine ⟨255445088145578306097347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170296725430385537398231 255445088145578306097347)
              ·
                refine ⟨383167632218367459146021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255445088145578306097347 383167632218367459146021)
                ·
                  refine ⟨71843931040943898589879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 383167632218367459146021 71843931040943898589879)
                  ·
                    rfl

theorem cell20_157405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_157405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157405 prefixEnd_157405 := by exact prefixLift 157405
  have htrace : WordTrace (prefixWord ++ tailWord_157405) baseStart_157405 baseEnd_157405 := by
    simpa [prefixWord, tailWord_157405, baseEnd_157405] using wordTrace_append hprefix tailTrace_157405
  have hstable : (prefixWord ++ tailWord_157405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157405).length < 2 ^ (prefixWord ++ tailWord_157405).sum := by decide
  have hdescent : baseEnd_157405 < baseStart_157405 := by decide
  rcases family_descends (prefixWord ++ tailWord_157405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157415 : List Nat := [1, 1, 5, 4, 2, 1, 2, 1, 3]
def baseStart_157415 : Nat := 118140960795 + 157415 * 2 ^ 59
def prefixEnd_157415 : Nat := 4983230072969 + 3 ^ 40 * 157415 * 2
def baseEnd_157415 : Nat := 71848495313428308256505

theorem tailTrace_157415 : CollatzResearch.WordTrace tailWord_157415 prefixEnd_157415 71848495313428308256505 := by
  unfold tailWord_157415
  simp only [CollatzResearch.WordTrace]
  refine ⟨5741396724719814186737699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3827597816479876124491799 5741396724719814186737699)
  ·
    refine ⟨8612095087079721280106549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5741396724719814186737699 8612095087079721280106549)
    ·
      refine ⟨807383914413723870009989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8612095087079721280106549 807383914413723870009989)
      ·
        refine ⟨151384483952573225626873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 807383914413723870009989 151384483952573225626873)
        ·
          refine ⟨113538362964429919220155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151384483952573225626873 113538362964429919220155)
          ·
            refine ⟨170307544446644878830233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113538362964429919220155 170307544446644878830233)
            ·
              refine ⟨127730658334983659122675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170307544446644878830233 127730658334983659122675)
              ·
                refine ⟨191595987502475488684013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127730658334983659122675 191595987502475488684013)
                ·
                  refine ⟨71848495313428308256505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191595987502475488684013 71848495313428308256505)
                  ·
                    rfl

theorem cell20_157415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 3].length) (baseStart_157415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157415 prefixEnd_157415 := by exact prefixLift 157415
  have htrace : WordTrace (prefixWord ++ tailWord_157415) baseStart_157415 baseEnd_157415 := by
    simpa [prefixWord, tailWord_157415, baseEnd_157415] using wordTrace_append hprefix tailTrace_157415
  have hstable : (prefixWord ++ tailWord_157415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157415).length < 2 ^ (prefixWord ++ tailWord_157415).sum := by decide
  have hdescent : baseEnd_157415 < baseStart_157415 := by decide
  rcases family_descends (prefixWord ++ tailWord_157415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157416 : List Nat := [2, 1, 4, 1, 3, 2, 2, 5]
def baseStart_157416 : Nat := 118140960795 + 157416 * 2 ^ 59
def prefixEnd_157416 : Nat := 4983230072969 + 3 ^ 40 * 157416 * 2
def baseEnd_157416 : Nat := 23949650580225583074389

theorem tailTrace_157416 : CollatzResearch.WordTrace tailWord_157416 prefixEnd_157416 23949650580225583074389 := by
  unfold tailWord_157416
  simp only [CollatzResearch.WordTrace]
  refine ⟨2870716598858095678762051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3827622131810794238349401 2870716598858095678762051)
  ·
    refine ⟨4306074898287143518143077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2870716598858095678762051 4306074898287143518143077)
    ·
      refine ⟨807389043428839409651827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4306074898287143518143077 807389043428839409651827)
      ·
        refine ⟨1211083565143259114477741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 807389043428839409651827 1211083565143259114477741)
        ·
          refine ⟨454156336928722167929153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1211083565143259114477741 454156336928722167929153)
          ·
            refine ⟨340617252696541625946865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 454156336928722167929153 340617252696541625946865)
            ·
              refine ⟨255462939522406219460149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 340617252696541625946865 255462939522406219460149)
              ·
                refine ⟨23949650580225583074389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 255462939522406219460149 23949650580225583074389)
                ·
                  rfl

theorem cell20_157416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_157416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157416 prefixEnd_157416 := by exact prefixLift 157416
  have htrace : WordTrace (prefixWord ++ tailWord_157416) baseStart_157416 baseEnd_157416 := by
    simpa [prefixWord, tailWord_157416, baseEnd_157416] using wordTrace_append hprefix tailTrace_157416
  have hstable : (prefixWord ++ tailWord_157416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157416).length < 2 ^ (prefixWord ++ tailWord_157416).sum := by decide
  have hdescent : baseEnd_157416 < baseStart_157416 := by decide
  rcases family_descends (prefixWord ++ tailWord_157416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157423 : List Nat := [1, 1, 2, 1, 5, 1, 3, 3, 3]
def baseStart_157423 : Nat := 118140960795 + 157423 * 2 ^ 59
def prefixEnd_157423 : Nat := 4983230072969 + 3 ^ 40 * 157423 * 2
def baseEnd_157423 : Nat := 71852146731415835989805

theorem tailTrace_157423 : CollatzResearch.WordTrace tailWord_157423 prefixEnd_157423 71852146731415835989805 := by
  unfold tailWord_157423
  simp only [CollatzResearch.WordTrace]
  refine ⟨5741688508690831553028923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3827792339127221035352615 5741688508690831553028923)
  ·
    refine ⟨8612532763036247329543385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5741688508690831553028923 8612532763036247329543385)
    ·
      refine ⟨6459399572277185497157539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8612532763036247329543385 6459399572277185497157539)
      ·
        refine ⟨9689099358415778245736309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6459399572277185497157539 9689099358415778245736309)
        ·
          refine ⟨908353064851479210537779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9689099358415778245736309 908353064851479210537779)
          ·
            refine ⟨1362529597277218815806669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 908353064851479210537779 1362529597277218815806669)
            ·
              refine ⟨510948598978957055927501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1362529597277218815806669 510948598978957055927501)
              ·
                refine ⟨191605724617108895972813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 510948598978957055927501 191605724617108895972813)
                ·
                  refine ⟨71852146731415835989805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191605724617108895972813 71852146731415835989805)
                  ·
                    rfl

theorem cell20_157423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 3].length) (baseStart_157423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157423 prefixEnd_157423 := by exact prefixLift 157423
  have htrace : WordTrace (prefixWord ++ tailWord_157423) baseStart_157423 baseEnd_157423 := by
    simpa [prefixWord, tailWord_157423, baseEnd_157423] using wordTrace_append hprefix tailTrace_157423
  have hstable : (prefixWord ++ tailWord_157423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157423).length < 2 ^ (prefixWord ++ tailWord_157423).sum := by decide
  have hdescent : baseEnd_157423 < baseStart_157423 := by decide
  rcases family_descends (prefixWord ++ tailWord_157423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157446 : List Nat := [6, 2, 2, 1, 2, 7]
def baseStart_157446 : Nat := 118140960795 + 157446 * 2 ^ 59
def prefixEnd_157446 : Nat := 4983230072969 + 3 ^ 40 * 157446 * 2
def baseEnd_157446 : Nat := 2661579428078888082335

theorem tailTrace_157446 : CollatzResearch.WordTrace tailWord_157446 prefixEnd_157446 2661579428078888082335 := by
  unfold tailWord_157446
  simp only [CollatzResearch.WordTrace]
  refine ⟨179453980862734577534881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3828351591738337654077461 179453980862734577534881)
  ·
    refine ⟨134590485647050933151161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179453980862734577534881 134590485647050933151161)
    ·
      refine ⟨100942864235288199863371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134590485647050933151161 100942864235288199863371)
      ·
        refine ⟨151414296352932299795057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100942864235288199863371 151414296352932299795057)
        ·
          refine ⟨113560722264699224846293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151414296352932299795057 113560722264699224846293)
          ·
            refine ⟨2661579428078888082335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 113560722264699224846293 2661579428078888082335)
            ·
              rfl

theorem cell20_157446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 7].length) (baseStart_157446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157446 prefixEnd_157446 := by exact prefixLift 157446
  have htrace : WordTrace (prefixWord ++ tailWord_157446) baseStart_157446 baseEnd_157446 := by
    simpa [prefixWord, tailWord_157446, baseEnd_157446] using wordTrace_append hprefix tailTrace_157446
  have hstable : (prefixWord ++ tailWord_157446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157446).length < 2 ^ (prefixWord ++ tailWord_157446).sum := by decide
  have hdescent : baseEnd_157446 < baseStart_157446 := by decide
  rcases family_descends (prefixWord ++ tailWord_157446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157461 : List Nat := [1, 3, 2, 1, 2, 3, 1, 4, 3]
def baseStart_157461 : Nat := 118140960795 + 157461 * 2 ^ 59
def prefixEnd_157461 : Nat := 4983230072969 + 3 ^ 40 * 157461 * 2
def baseEnd_157461 : Nat := 71869490966856592722983

theorem tailTrace_157461 : CollatzResearch.WordTrace tailWord_157461 prefixEnd_157461 71869490966856592722983 := by
  unfold tailWord_157461
  simp only [CollatzResearch.WordTrace]
  refine ⟨5743074482553164042912237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3828716321702109361941491 5743074482553164042912237)
  ·
    refine ⟨2153652930957436516092089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5743074482553164042912237 2153652930957436516092089)
    ·
      refine ⟨1615239698218077387069067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2153652930957436516092089 1615239698218077387069067)
      ·
        refine ⟨2422859547327116080603601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1615239698218077387069067 2422859547327116080603601)
        ·
          refine ⟨1817144660495337060452701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2422859547327116080603601 1817144660495337060452701)
          ·
            refine ⟨681429247685751397669763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1817144660495337060452701 681429247685751397669763)
            ·
              refine ⟨1022143871528627096504645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681429247685751397669763 1022143871528627096504645)
              ·
                refine ⟨191651975911617580594621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1022143871528627096504645 191651975911617580594621)
                ·
                  refine ⟨71869490966856592722983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191651975911617580594621 71869490966856592722983)
                  ·
                    rfl

theorem cell20_157461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_157461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157461 prefixEnd_157461 := by exact prefixLift 157461
  have htrace : WordTrace (prefixWord ++ tailWord_157461) baseStart_157461 baseEnd_157461 := by
    simpa [prefixWord, tailWord_157461, baseEnd_157461] using wordTrace_append hprefix tailTrace_157461
  have hstable : (prefixWord ++ tailWord_157461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157461).length < 2 ^ (prefixWord ++ tailWord_157461).sum := by decide
  have hdescent : baseEnd_157461 < baseStart_157461 := by decide
  rcases family_descends (prefixWord ++ tailWord_157461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157464 : List Nat := [2, 1, 2, 3, 1, 1, 6, 2, 2]
def baseStart_157464 : Nat := 118140960795 + 157464 * 2 ^ 59
def prefixEnd_157464 : Nat := 4983230072969 + 3 ^ 40 * 157464 * 2
def baseEnd_157464 : Nat := 71870860248601915622971

theorem tailTrace_157464 : CollatzResearch.WordTrace tailWord_157464 prefixEnd_157464 71870860248601915622971 := by
  unfold tailWord_157464
  simp only [CollatzResearch.WordTrace]
  refine ⟨2871591950771147777635723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3828789267694863703514297 2871591950771147777635723)
  ·
    refine ⟨4307387926156721666453585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2871591950771147777635723 4307387926156721666453585)
    ·
      refine ⟨3230540944617541249840189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4307387926156721666453585 3230540944617541249840189)
      ·
        refine ⟨1211452854231577968690071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3230540944617541249840189 1211452854231577968690071)
        ·
          refine ⟨1817179281347366953035107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1211452854231577968690071 1817179281347366953035107)
          ·
            refine ⟨2725768922021050429552661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1817179281347366953035107 2725768922021050429552661)
            ·
              refine ⟨127770418219736738885281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2725768922021050429552661 127770418219736738885281)
              ·
                refine ⟨95827813664802554163961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127770418219736738885281 95827813664802554163961)
                ·
                  refine ⟨71870860248601915622971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95827813664802554163961 71870860248601915622971)
                  ·
                    rfl

theorem cell20_157464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 2].length) (baseStart_157464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157464 prefixEnd_157464 := by exact prefixLift 157464
  have htrace : WordTrace (prefixWord ++ tailWord_157464) baseStart_157464 baseEnd_157464 := by
    simpa [prefixWord, tailWord_157464, baseEnd_157464] using wordTrace_append hprefix tailTrace_157464
  have hstable : (prefixWord ++ tailWord_157464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157464).length < 2 ^ (prefixWord ++ tailWord_157464).sum := by decide
  have hdescent : baseEnd_157464 < baseStart_157464 := by decide
  rcases family_descends (prefixWord ++ tailWord_157464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157468 : List Nat := [2, 2, 3, 1, 1, 2, 2, 3, 4]
def baseStart_157468 : Nat := 118140960795 + 157468 * 2 ^ 59
def prefixEnd_157468 : Nat := 4983230072969 + 3 ^ 40 * 157468 * 2
def baseEnd_157468 : Nat := 71872685957595679489621

theorem tailTrace_157468 : CollatzResearch.WordTrace tailWord_157468 prefixEnd_157468 71872685957595679489621 := by
  unfold tailWord_157468
  simp only [CollatzResearch.WordTrace]
  refine ⟨2871664896763902119208529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3828886529018536158944705 2871664896763902119208529)
  ·
    refine ⟨2153748672572926589406397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2871664896763902119208529 2153748672572926589406397)
    ·
      refine ⟨807655752214847471027399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2153748672572926589406397 807655752214847471027399)
      ·
        refine ⟨1211483628322271206541099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 807655752214847471027399 1211483628322271206541099)
        ·
          refine ⟨1817225442483406809811649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1211483628322271206541099 1817225442483406809811649)
          ·
            refine ⟨1362919081862555107358737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1817225442483406809811649 1362919081862555107358737)
            ·
              refine ⟨1022189311396916330519053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1362919081862555107358737 1022189311396916330519053)
              ·
                refine ⟨383320991773843623944645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1022189311396916330519053 383320991773843623944645)
                ·
                  refine ⟨71872685957595679489621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 383320991773843623944645 71872685957595679489621)
                  ·
                    rfl

theorem cell20_157468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_157468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157468 prefixEnd_157468 := by exact prefixLift 157468
  have htrace : WordTrace (prefixWord ++ tailWord_157468) baseStart_157468 baseEnd_157468 := by
    simpa [prefixWord, tailWord_157468, baseEnd_157468] using wordTrace_append hprefix tailTrace_157468
  have hstable : (prefixWord ++ tailWord_157468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157468).length < 2 ^ (prefixWord ++ tailWord_157468).sum := by decide
  have hdescent : baseEnd_157468 < baseStart_157468 := by decide
  rcases family_descends (prefixWord ++ tailWord_157468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157475 : List Nat := [1, 1, 1, 4, 2, 1, 5, 5]
def baseStart_157475 : Nat := 118140960795 + 157475 * 2 ^ 59
def prefixEnd_157475 : Nat := 4983230072969 + 3 ^ 40 * 157475 * 2
def baseEnd_157475 : Nat := 23958626982778255418753

theorem tailTrace_157475 : CollatzResearch.WordTrace tailWord_157475 prefixEnd_157475 23958626982778255418753 := by
  unfold tailWord_157475
  simp only [CollatzResearch.WordTrace]
  refine ⟨5743585104502444433921879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3829056736334962955947919 5743585104502444433921879)
  ·
    refine ⟨8615377656753666650882819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5743585104502444433921879 8615377656753666650882819)
    ·
      refine ⟨12923066485130499976324229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8615377656753666650882819 12923066485130499976324229)
      ·
        refine ⟨2423074965961968745560793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12923066485130499976324229 2423074965961968745560793)
        ·
          refine ⟨1817306224471476559170595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2423074965961968745560793 1817306224471476559170595)
          ·
            refine ⟨2725959336707214838755893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1817306224471476559170595 2725959336707214838755893)
            ·
              refine ⟨255558687816301391133365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2725959336707214838755893 255558687816301391133365)
              ·
                refine ⟨23958626982778255418753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 255558687816301391133365 23958626982778255418753)
                ·
                  rfl

theorem cell20_157475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 5].length) (baseStart_157475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157475 prefixEnd_157475 := by exact prefixLift 157475
  have htrace : WordTrace (prefixWord ++ tailWord_157475) baseStart_157475 baseEnd_157475 := by
    simpa [prefixWord, tailWord_157475, baseEnd_157475] using wordTrace_append hprefix tailTrace_157475
  have hstable : (prefixWord ++ tailWord_157475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157475).length < 2 ^ (prefixWord ++ tailWord_157475).sum := by decide
  have hdescent : baseEnd_157475 < baseStart_157475 := by decide
  rcases family_descends (prefixWord ++ tailWord_157475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157502 : List Nat := [4, 2, 1, 2, 2, 1, 1, 5, 2]
def baseStart_157502 : Nat := 118140960795 + 157502 * 2 ^ 59
def prefixEnd_157502 : Nat := 4983230072969 + 3 ^ 40 * 157502 * 2
def baseEnd_157502 : Nat := 71888204484042672356149

theorem tailTrace_157502 : CollatzResearch.WordTrace tailWord_157502 prefixEnd_157502 71888204484042672356149 := by
  unfold tailWord_157502
  simp only [CollatzResearch.WordTrace]
  refine ⟨718071234425578505644345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3829713250269752030103173 718071234425578505644345)
  ·
    refine ⟨538553425819183879233259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 718071234425578505644345 538553425819183879233259)
    ·
      refine ⟨807830138728775818849889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 538553425819183879233259 807830138728775818849889)
      ·
        refine ⟨605872604046581864137417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 807830138728775818849889 605872604046581864137417)
        ·
          refine ⟨454404453034936398103063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 605872604046581864137417 454404453034936398103063)
          ·
            refine ⟨681606679552404597154595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454404453034936398103063 681606679552404597154595)
            ·
              refine ⟨1022410019328606895731893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681606679552404597154595 1022410019328606895731893)
              ·
                refine ⟨95850939312056896474865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1022410019328606895731893 95850939312056896474865)
                ·
                  refine ⟨71888204484042672356149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95850939312056896474865 71888204484042672356149)
                  ·
                    rfl

theorem cell20_157502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_157502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157502 prefixEnd_157502 := by exact prefixLift 157502
  have htrace : WordTrace (prefixWord ++ tailWord_157502) baseStart_157502 baseEnd_157502 := by
    simpa [prefixWord, tailWord_157502, baseEnd_157502] using wordTrace_append hprefix tailTrace_157502
  have hstable : (prefixWord ++ tailWord_157502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157502).length < 2 ^ (prefixWord ++ tailWord_157502).sum := by decide
  have hdescent : baseEnd_157502 < baseStart_157502 := by decide
  rcases family_descends (prefixWord ++ tailWord_157502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157544 : List Nat := [2, 1, 4, 2, 1, 1, 1, 4, 4]
def baseStart_157544 : Nat := 118140960795 + 157544 * 2 ^ 59
def prefixEnd_157544 : Nat := 4983230072969 + 3 ^ 40 * 157544 * 2
def baseEnd_157544 : Nat := 71907374428477192955977

theorem tailTrace_157544 : CollatzResearch.WordTrace tailWord_157544 prefixEnd_157544 71907374428477192955977 := by
  unfold tailWord_157544
  simp only [CollatzResearch.WordTrace]
  refine ⟨2873050870626234609091843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3830734494168312812122457 2873050870626234609091843)
  ·
    refine ⟨4309576305939351913637765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2873050870626234609091843 4309576305939351913637765)
    ·
      refine ⟨808045557363628483807081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4309576305939351913637765 808045557363628483807081)
      ·
        refine ⟨606034168022721362855311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 808045557363628483807081 606034168022721362855311)
        ·
          refine ⟨909051252034082044282967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 606034168022721362855311 909051252034082044282967)
          ·
            refine ⟨1363576878051123066424451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 909051252034082044282967 1363576878051123066424451)
            ·
              refine ⟨2045365317076684599636677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1363576878051123066424451 2045365317076684599636677)
              ·
                refine ⟨383505996951878362431877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2045365317076684599636677 383505996951878362431877)
                ·
                  refine ⟨71907374428477192955977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 383505996951878362431877 71907374428477192955977)
                  ·
                    rfl

theorem cell20_157544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_157544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157544 prefixEnd_157544 := by exact prefixLift 157544
  have htrace : WordTrace (prefixWord ++ tailWord_157544) baseStart_157544 baseEnd_157544 := by
    simpa [prefixWord, tailWord_157544, baseEnd_157544] using wordTrace_append hprefix tailTrace_157544
  have hstable : (prefixWord ++ tailWord_157544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157544).length < 2 ^ (prefixWord ++ tailWord_157544).sum := by decide
  have hdescent : baseEnd_157544 < baseStart_157544 := by decide
  rcases family_descends (prefixWord ++ tailWord_157544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157578 : List Nat := [3, 1, 2, 4, 2, 2, 1, 1, 4]
def baseStart_157578 : Nat := 118140960795 + 157578 * 2 ^ 59
def prefixEnd_157578 : Nat := 4983230072969 + 3 ^ 40 * 157578 * 2
def baseEnd_157578 : Nat := 71922892954924185822505

theorem tailTrace_157578 : CollatzResearch.WordTrace tailWord_157578 prefixEnd_157578 71922892954924185822505 := by
  unfold tailWord_157578
  simp only [CollatzResearch.WordTrace]
  refine ⟨1436835455782323256230347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3831561215419528683280925 1436835455782323256230347)
  ·
    refine ⟨2155253183673484884345521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1436835455782323256230347 2155253183673484884345521)
    ·
      refine ⟨1616439887755113663259141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2155253183673484884345521 1616439887755113663259141)
      ·
        refine ⟨303082478954083811861089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1616439887755113663259141 303082478954083811861089)
        ·
          refine ⟨227311859215562858895817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303082478954083811861089 227311859215562858895817)
          ·
            refine ⟨170483894411672144171863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227311859215562858895817 170483894411672144171863)
            ·
              refine ⟨255725841617508216257795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170483894411672144171863 255725841617508216257795)
              ·
                refine ⟨383588762426262324386693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255725841617508216257795 383588762426262324386693)
                ·
                  refine ⟨71922892954924185822505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 383588762426262324386693 71922892954924185822505)
                  ·
                    rfl

theorem cell20_157578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_157578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157578 prefixEnd_157578 := by exact prefixLift 157578
  have htrace : WordTrace (prefixWord ++ tailWord_157578) baseStart_157578 baseEnd_157578 := by
    simpa [prefixWord, tailWord_157578, baseEnd_157578] using wordTrace_append hprefix tailTrace_157578
  have hstable : (prefixWord ++ tailWord_157578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157578).length < 2 ^ (prefixWord ++ tailWord_157578).sum := by decide
  have hdescent : baseEnd_157578 < baseStart_157578 := by decide
  rcases family_descends (prefixWord ++ tailWord_157578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157589 : List Nat := [1, 3, 2, 1, 1, 3, 4, 5]
def baseStart_157589 : Nat := 118140960795 + 157589 * 2 ^ 59
def prefixEnd_157589 : Nat := 4983230072969 + 3 ^ 40 * 157589 * 2
def baseEnd_157589 : Nat := 23975971218219012151931

theorem tailTrace_157589 : CollatzResearch.WordTrace tailWord_157589 prefixEnd_157589 23975971218219012151931 := by
  unfold tailWord_157589
  simp only [CollatzResearch.WordTrace]
  refine ⟨5747743026089441903571821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3831828684059627935714547 5747743026089441903571821)
  ·
    refine ⟨2155403634783540713839433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5747743026089441903571821 2155403634783540713839433)
    ·
      refine ⟨1616552726087655535379575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2155403634783540713839433 1616552726087655535379575)
      ·
        refine ⟨2424829089131483303069363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1616552726087655535379575 2424829089131483303069363)
        ·
          refine ⟨3637243633697224954604045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2424829089131483303069363 3637243633697224954604045)
          ·
            refine ⟨1363966362636459357976517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3637243633697224954604045 1363966362636459357976517)
            ·
              refine ⟨255743692994336129620597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1363966362636459357976517 255743692994336129620597)
              ·
                refine ⟨23975971218219012151931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 255743692994336129620597 23975971218219012151931)
                ·
                  rfl

theorem cell20_157589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 5].length) (baseStart_157589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157589 prefixEnd_157589 := by exact prefixLift 157589
  have htrace : WordTrace (prefixWord ++ tailWord_157589) baseStart_157589 baseEnd_157589 := by
    simpa [prefixWord, tailWord_157589, baseEnd_157589] using wordTrace_append hprefix tailTrace_157589
  have hstable : (prefixWord ++ tailWord_157589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157589).length < 2 ^ (prefixWord ++ tailWord_157589).sum := by decide
  have hdescent : baseEnd_157589 < baseStart_157589 := by decide
  rcases family_descends (prefixWord ++ tailWord_157589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157603 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 6]
def baseStart_157603 : Nat := 118140960795 + 157603 * 2 ^ 59
def prefixEnd_157603 : Nat := 4983230072969 + 3 ^ 40 * 157603 * 2
def baseEnd_157603 : Nat := 71934303636135209989069

theorem tailTrace_157603 : CollatzResearch.WordTrace tailWord_157603 prefixEnd_157603 71934303636135209989069 := by
  unfold tailWord_157603
  simp only [CollatzResearch.WordTrace]
  refine ⟨5748253648038722294581463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3832169098692481529720975 5748253648038722294581463)
  ·
    refine ⟨8622380472058083441872195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5748253648038722294581463 8622380472058083441872195)
    ·
      refine ⟨12933570708087125162808293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8622380472058083441872195 12933570708087125162808293)
      ·
        refine ⟨2425044507766335968026555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12933570708087125162808293 2425044507766335968026555)
        ·
          refine ⟨3637566761649503952039833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2425044507766335968026555 3637566761649503952039833)
          ·
            refine ⟨2728175071237127964029875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3637566761649503952039833 2728175071237127964029875)
            ·
              refine ⟨4092262606855691946044813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2728175071237127964029875 4092262606855691946044813)
              ·
                refine ⟨1534598477570884479766805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4092262606855691946044813 1534598477570884479766805)
                ·
                  refine ⟨71934303636135209989069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1534598477570884479766805 71934303636135209989069)
                  ·
                    rfl

theorem cell20_157603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_157603 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157603 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157603 prefixEnd_157603 := by exact prefixLift 157603
  have htrace : WordTrace (prefixWord ++ tailWord_157603) baseStart_157603 baseEnd_157603 := by
    simpa [prefixWord, tailWord_157603, baseEnd_157603] using wordTrace_append hprefix tailTrace_157603
  have hstable : (prefixWord ++ tailWord_157603).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157603).length < 2 ^ (prefixWord ++ tailWord_157603).sum := by decide
  have hdescent : baseEnd_157603 < baseStart_157603 := by decide
  rcases family_descends (prefixWord ++ tailWord_157603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157630 : List Nat := [4, 2, 1, 1, 1, 4, 2, 2, 3]
def baseStart_157630 : Nat := 118140960795 + 157630 * 2 ^ 59
def prefixEnd_157630 : Nat := 4983230072969 + 3 ^ 40 * 157630 * 2
def baseEnd_157630 : Nat := 71946627171843116088959

theorem tailTrace_157630 : CollatzResearch.WordTrace tailWord_157630 prefixEnd_157630 71946627171843116088959 := by
  unfold tailWord_157630
  simp only [CollatzResearch.WordTrace]
  refine ⟨718654802367613238226793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3832825612627270603876229 718654802367613238226793)
  ·
    refine ⟨538991101775709928670095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 718654802367613238226793 538991101775709928670095)
    ·
      refine ⟨808486652663564893005143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 538991101775709928670095 808486652663564893005143)
      ·
        refine ⟨1212729978995347339507715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 808486652663564893005143 1212729978995347339507715)
        ·
          refine ⟨1819094968493021009261573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1212729978995347339507715 1819094968493021009261573)
          ·
            refine ⟨341080306592441439236545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1819094968493021009261573 341080306592441439236545)
            ·
              refine ⟨255810229944331079427409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 341080306592441439236545 255810229944331079427409)
              ·
                refine ⟨191857672458248309570557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255810229944331079427409 191857672458248309570557)
                ·
                  refine ⟨71946627171843116088959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191857672458248309570557 71946627171843116088959)
                  ·
                    rfl

theorem cell20_157630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_157630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157630 prefixEnd_157630 := by exact prefixLift 157630
  have htrace : WordTrace (prefixWord ++ tailWord_157630) baseStart_157630 baseEnd_157630 := by
    simpa [prefixWord, tailWord_157630, baseEnd_157630] using wordTrace_append hprefix tailTrace_157630
  have hstable : (prefixWord ++ tailWord_157630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157630).length < 2 ^ (prefixWord ++ tailWord_157630).sum := by decide
  have hdescent : baseEnd_157630 < baseStart_157630 := by decide
  rcases family_descends (prefixWord ++ tailWord_157630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157644 : List Nat := [2, 2, 1, 4, 1, 4, 1, 5]
def baseStart_157644 : Nat := 118140960795 + 157644 * 2 ^ 59
def prefixEnd_157644 : Nat := 4983230072969 + 3 ^ 40 * 157644 * 2
def baseEnd_157644 : Nat := 23984339051107096540745

theorem tailTrace_157644 : CollatzResearch.WordTrace tailWord_157644 prefixEnd_157644 23984339051107096540745 := by
  unfold tailWord_157644
  simp only [CollatzResearch.WordTrace]
  refine ⟨2874874520445093148411993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3833166027260124197882657 2874874520445093148411993)
  ·
    refine ⟨2156155890333819861308995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2874874520445093148411993 2156155890333819861308995)
    ·
      refine ⟨3234233835500729791963493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2156155890333819861308995 3234233835500729791963493)
      ·
        refine ⟨606418844156386835993155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3234233835500729791963493 606418844156386835993155)
        ·
          refine ⟨909628266234580253989733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 606418844156386835993155 909628266234580253989733)
          ·
            refine ⟨170555299918983797623075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 909628266234580253989733 170555299918983797623075)
            ·
              refine ⟨255832949878475696434613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170555299918983797623075 255832949878475696434613)
              ·
                refine ⟨23984339051107096540745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 255832949878475696434613 23984339051107096540745)
                ·
                  rfl

theorem cell20_157644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 5].length) (baseStart_157644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157644 prefixEnd_157644 := by exact prefixLift 157644
  have htrace : WordTrace (prefixWord ++ tailWord_157644) baseStart_157644 baseEnd_157644 := by
    simpa [prefixWord, tailWord_157644, baseEnd_157644] using wordTrace_append hprefix tailTrace_157644
  have hstable : (prefixWord ++ tailWord_157644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157644).length < 2 ^ (prefixWord ++ tailWord_157644).sum := by decide
  have hdescent : baseEnd_157644 < baseStart_157644 := by decide
  rcases family_descends (prefixWord ++ tailWord_157644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157654 : List Nat := [5, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_157654 : Nat := 118140960795 + 157654 * 2 ^ 59
def prefixEnd_157654 : Nat := 4983230072969 + 3 ^ 40 * 157654 * 2
def baseEnd_157654 : Nat := 71957581425805699288861

theorem tailTrace_157654 : CollatzResearch.WordTrace tailWord_157654 prefixEnd_157654 71957581425805699288861 := by
  unfold tailWord_157654
  simp only [CollatzResearch.WordTrace]
  refine ⟨359382110678372375293001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3833409180569305336458677 359382110678372375293001)
  ·
    refine ⟨269536583008779281469751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 359382110678372375293001 269536583008779281469751)
    ·
      refine ⟨404304874513168922204627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269536583008779281469751 404304874513168922204627)
      ·
        refine ⟨606457311769753383306941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404304874513168922204627 606457311769753383306941)
        ·
          refine ⟨227421491913657518740103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 606457311769753383306941 227421491913657518740103)
          ·
            refine ⟨341132237870486278110155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227421491913657518740103 341132237870486278110155)
            ·
              refine ⟨511698356805729417165233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341132237870486278110155 511698356805729417165233)
              ·
                refine ⟨383773767604297062873925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 511698356805729417165233 383773767604297062873925)
                ·
                  refine ⟨71957581425805699288861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 383773767604297062873925 71957581425805699288861)
                  ·
                    rfl

theorem cell20_157654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_157654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157654 prefixEnd_157654 := by exact prefixLift 157654
  have htrace : WordTrace (prefixWord ++ tailWord_157654) baseStart_157654 baseEnd_157654 := by
    simpa [prefixWord, tailWord_157654, baseEnd_157654] using wordTrace_append hprefix tailTrace_157654
  have hstable : (prefixWord ++ tailWord_157654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157654).length < 2 ^ (prefixWord ++ tailWord_157654).sum := by decide
  have hdescent : baseEnd_157654 < baseStart_157654 := by decide
  rcases family_descends (prefixWord ++ tailWord_157654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157661 : List Nat := [1, 4, 3, 1, 3, 1, 3, 4]
def baseStart_157661 : Nat := 118140960795 + 157661 * 2 ^ 59
def prefixEnd_157661 : Nat := 4983230072969 + 3 ^ 40 * 157661 * 2
def baseEnd_157661 : Nat := 23986925472181595351833

theorem tailTrace_157661 : CollatzResearch.WordTrace tailWord_157661 prefixEnd_157661 23986925472181595351833 := by
  unfold tailWord_157661
  simp only [CollatzResearch.WordTrace]
  refine ⟨5750369081828598200192837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3833579387885732133461891 5750369081828598200192837)
  ·
    refine ⟨1078194202842862162536157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5750369081828598200192837 1078194202842862162536157)
    ·
      refine ⟨404322826066073310951059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1078194202842862162536157 404322826066073310951059)
      ·
        refine ⟨606484239099109966426589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404322826066073310951059 606484239099109966426589)
        ·
          refine ⟨227431589662166237409971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 606484239099109966426589 227431589662166237409971)
          ·
            refine ⟨341147384493249356114957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227431589662166237409971 341147384493249356114957)
            ·
              refine ⟨127930269184968508543109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 341147384493249356114957 127930269184968508543109)
              ·
                refine ⟨23986925472181595351833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127930269184968508543109 23986925472181595351833)
                ·
                  rfl

theorem cell20_157661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 4].length) (baseStart_157661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157661 prefixEnd_157661 := by exact prefixLift 157661
  have htrace : WordTrace (prefixWord ++ tailWord_157661) baseStart_157661 baseEnd_157661 := by
    simpa [prefixWord, tailWord_157661, baseEnd_157661] using wordTrace_append hprefix tailTrace_157661
  have hstable : (prefixWord ++ tailWord_157661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157661).length < 2 ^ (prefixWord ++ tailWord_157661).sum := by decide
  have hdescent : baseEnd_157661 < baseStart_157661 := by decide
  rcases family_descends (prefixWord ++ tailWord_157661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157672 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 5]
def baseStart_157672 : Nat := 118140960795 + 157672 * 2 ^ 59
def prefixEnd_157672 : Nat := 4983230072969 + 3 ^ 40 * 157672 * 2
def baseEnd_157672 : Nat := 71965797116277636688787

theorem tailTrace_157672 : CollatzResearch.WordTrace tailWord_157672 prefixEnd_157672 71965797116277636688787 := by
  unfold tailWord_157672
  simp only [CollatzResearch.WordTrace]
  refine ⟨2875385142394373539421635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3833846856525831385895513 2875385142394373539421635)
  ·
    refine ⟨4313077713591560309132453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2875385142394373539421635 4313077713591560309132453)
    ·
      refine ⟨808702071298417557962335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4313077713591560309132453 808702071298417557962335)
      ·
        refine ⟨1213053106947626336943503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 808702071298417557962335 1213053106947626336943503)
        ·
          refine ⟨1819579660421439505415255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1213053106947626336943503 1819579660421439505415255)
          ·
            refine ⟨2729369490632159258122883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1819579660421439505415255 2729369490632159258122883)
            ·
              refine ⟨4094054235948238887184325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2729369490632159258122883 4094054235948238887184325)
              ·
                refine ⟨767635169240294791347061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4094054235948238887184325 767635169240294791347061)
                ·
                  refine ⟨71965797116277636688787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 767635169240294791347061 71965797116277636688787)
                  ·
                    rfl

theorem cell20_157672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_157672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157672 prefixEnd_157672 := by exact prefixLift 157672
  have htrace : WordTrace (prefixWord ++ tailWord_157672) baseStart_157672 baseEnd_157672 := by
    simpa [prefixWord, tailWord_157672, baseEnd_157672] using wordTrace_append hprefix tailTrace_157672
  have hstable : (prefixWord ++ tailWord_157672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157672).length < 2 ^ (prefixWord ++ tailWord_157672).sum := by decide
  have hdescent : baseEnd_157672 < baseStart_157672 := by decide
  rcases family_descends (prefixWord ++ tailWord_157672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157679 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 6]
def baseStart_157679 : Nat := 118140960795 + 157679 * 2 ^ 59
def prefixEnd_157679 : Nat := 4983230072969 + 3 ^ 40 * 157679 * 2
def baseEnd_157679 : Nat := 71968992107016723455425

theorem tailTrace_157679 : CollatzResearch.WordTrace tailWord_157679 prefixEnd_157679 71968992107016723455425 := by
  unfold tailWord_157679
  simp only [CollatzResearch.WordTrace]
  refine ⟨5751025595763387274348091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3834017063842258182898727 5751025595763387274348091)
  ·
    refine ⟨8626538393645080911522137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5751025595763387274348091 8626538393645080911522137)
    ·
      refine ⟨6469903795233810683641603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8626538393645080911522137 6469903795233810683641603)
      ·
        refine ⟨9704855692850716025462405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6469903795233810683641603 9704855692850716025462405)
        ·
          refine ⟨1819660442409509254774201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9704855692850716025462405 1819660442409509254774201)
          ·
            refine ⟨1364745331807131941080651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1819660442409509254774201 1364745331807131941080651)
            ·
              refine ⟨2047117997710697911620977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1364745331807131941080651 2047117997710697911620977)
              ·
                refine ⟨1535338498283023433715733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2047117997710697911620977 1535338498283023433715733)
                ·
                  refine ⟨71968992107016723455425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1535338498283023433715733 71968992107016723455425)
                  ·
                    rfl

theorem cell20_157679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_157679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157679 prefixEnd_157679 := by exact prefixLift 157679
  have htrace : WordTrace (prefixWord ++ tailWord_157679) baseStart_157679 baseEnd_157679 := by
    simpa [prefixWord, tailWord_157679, baseEnd_157679] using wordTrace_append hprefix tailTrace_157679
  have hstable : (prefixWord ++ tailWord_157679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157679).length < 2 ^ (prefixWord ++ tailWord_157679).sum := by decide
  have hdescent : baseEnd_157679 < baseStart_157679 := by decide
  rcases family_descends (prefixWord ++ tailWord_157679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157689 : List Nat := [1, 2, 1, 3, 1, 4, 3, 2, 3]
def baseStart_157689 : Nat := 118140960795 + 157689 * 2 ^ 59
def prefixEnd_157689 : Nat := 4983230072969 + 3 ^ 40 * 157689 * 2
def baseEnd_157689 : Nat := 71973556379501133122051

theorem tailTrace_157689 : CollatzResearch.WordTrace tailWord_157689 prefixEnd_157689 71973556379501133122051 := by
  unfold tailWord_157689
  simp only [CollatzResearch.WordTrace]
  refine ⟨5751390325727158982212121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3834260217151439321474747 5751390325727158982212121)
  ·
    refine ⟨4313542744295369236659091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5751390325727158982212121 4313542744295369236659091)
    ·
      refine ⟨6470314116443053854988637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4313542744295369236659091 6470314116443053854988637)
      ·
        refine ⟨2426367793666145195620739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6470314116443053854988637 2426367793666145195620739)
        ·
          refine ⟨3639551690499217793431109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2426367793666145195620739 3639551690499217793431109)
          ·
            refine ⟨682415941968603336268333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3639551690499217793431109 682415941968603336268333)
            ·
              refine ⟨255905978238226251100625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 682415941968603336268333 255905978238226251100625)
              ·
                refine ⟨191929483678669688325469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255905978238226251100625 191929483678669688325469)
                ·
                  refine ⟨71973556379501133122051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191929483678669688325469 71973556379501133122051)
                  ·
                    rfl

theorem cell20_157689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 3].length) (baseStart_157689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157689 prefixEnd_157689 := by exact prefixLift 157689
  have htrace : WordTrace (prefixWord ++ tailWord_157689) baseStart_157689 baseEnd_157689 := by
    simpa [prefixWord, tailWord_157689, baseEnd_157689] using wordTrace_append hprefix tailTrace_157689
  have hstable : (prefixWord ++ tailWord_157689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157689).length < 2 ^ (prefixWord ++ tailWord_157689).sum := by decide
  have hdescent : baseEnd_157689 < baseStart_157689 := by decide
  rcases family_descends (prefixWord ++ tailWord_157689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157761 : List Nat := [1, 2, 5, 1, 2, 3, 2, 1, 3]
def baseStart_157761 : Nat := 118140960795 + 157761 * 2 ^ 59
def prefixEnd_157761 : Nat := 4983230072969 + 3 ^ 40 * 157761 * 2
def baseEnd_157761 : Nat := 72006419141388882721757

theorem tailTrace_157761 : CollatzResearch.WordTrace tailWord_157761 prefixEnd_157761 72006419141388882721757 := by
  unfold tailWord_157761
  simp only [CollatzResearch.WordTrace]
  refine ⟨5754016381466315278833137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3836010920977543519222091 5754016381466315278833137)
  ·
    refine ⟨4315512286099736459124853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5754016381466315278833137 4315512286099736459124853)
    ·
      refine ⟨404579276821850293042955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4315512286099736459124853 404579276821850293042955)
      ·
        refine ⟨606868915232775439564433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404579276821850293042955 606868915232775439564433)
        ·
          refine ⟨455151686424581579673325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 606868915232775439564433 455151686424581579673325)
          ·
            refine ⟨170681882409218092377497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 455151686424581579673325 170681882409218092377497)
            ·
              refine ⟨128011411806913569283123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170681882409218092377497 128011411806913569283123)
              ·
                refine ⟨192017117710370353924685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128011411806913569283123 192017117710370353924685)
                ·
                  refine ⟨72006419141388882721757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 192017117710370353924685 72006419141388882721757)
                  ·
                    rfl

theorem cell20_157761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 3].length) (baseStart_157761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157761 prefixEnd_157761 := by exact prefixLift 157761
  have htrace : WordTrace (prefixWord ++ tailWord_157761) baseStart_157761 baseEnd_157761 := by
    simpa [prefixWord, tailWord_157761, baseEnd_157761] using wordTrace_append hprefix tailTrace_157761
  have hstable : (prefixWord ++ tailWord_157761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157761).length < 2 ^ (prefixWord ++ tailWord_157761).sum := by decide
  have hdescent : baseEnd_157761 < baseStart_157761 := by decide
  rcases family_descends (prefixWord ++ tailWord_157761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157800 : List Nat := [2, 1, 4, 13]
def baseStart_157800 : Nat := 118140960795 + 157800 * 2 ^ 59
def prefixEnd_157800 : Nat := 4983230072969 + 3 ^ 40 * 157800 * 2
def baseEnd_157800 : Nat := 296395966271926256879

theorem tailTrace_157800 : CollatzResearch.WordTrace tailWord_157800 prefixEnd_157800 296395966271926256879 := by
  unfold tailWord_157800
  simp only [CollatzResearch.WordTrace]
  refine ⟨2877719414162512469751427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3836959218883349959668569 2877719414162512469751427)
  ·
    refine ⟨4316579121243768704627141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2877719414162512469751427 4316579121243768704627141)
    ·
      refine ⟨809358585233206632117589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4316579121243768704627141 809358585233206632117589)
      ·
        refine ⟨296395966271926256879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 809358585233206632117589 296395966271926256879)
        ·
          rfl

theorem cell20_157800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 13].length) (baseStart_157800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157800 prefixEnd_157800 := by exact prefixLift 157800
  have htrace : WordTrace (prefixWord ++ tailWord_157800) baseStart_157800 baseEnd_157800 := by
    simpa [prefixWord, tailWord_157800, baseEnd_157800] using wordTrace_append hprefix tailTrace_157800
  have hstable : (prefixWord ++ tailWord_157800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157800).length < 2 ^ (prefixWord ++ tailWord_157800).sum := by decide
  have hdescent : baseEnd_157800 < baseStart_157800 := by decide
  rcases family_descends (prefixWord ++ tailWord_157800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157802 : List Nat := [3, 1, 3, 2, 4, 1, 2, 2, 2]
def baseStart_157802 : Nat := 118140960795 + 157802 * 2 ^ 59
def prefixEnd_157802 : Nat := 4983230072969 + 3 ^ 40 * 157802 * 2
def baseEnd_157802 : Nat := 72025132658574962354923

theorem tailTrace_157802 : CollatzResearch.WordTrace tailWord_157802 prefixEnd_157802 72025132658574962354923 := by
  unfold tailWord_157802
  simp only [CollatzResearch.WordTrace]
  refine ⟨1438877943579444820268915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3837007849545186187383773 1438877943579444820268915)
  ·
    refine ⟨2158316915369167230403373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1438877943579444820268915 2158316915369167230403373)
    ·
      refine ⟨809368843263437711401265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2158316915369167230403373 809368843263437711401265)
      ·
        refine ⟨607026632447578283550949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 809368843263437711401265 607026632447578283550949)
        ·
          refine ⟨113817493583920928165803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 607026632447578283550949 113817493583920928165803)
          ·
            refine ⟨170726240375881392248705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113817493583920928165803 170726240375881392248705)
            ·
              refine ⟨128044680281911044186529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170726240375881392248705 128044680281911044186529)
              ·
                refine ⟨96033510211433283139897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128044680281911044186529 96033510211433283139897)
                ·
                  refine ⟨72025132658574962354923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96033510211433283139897 72025132658574962354923)
                  ·
                    rfl

theorem cell20_157802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 2].length) (baseStart_157802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157802 prefixEnd_157802 := by exact prefixLift 157802
  have htrace : WordTrace (prefixWord ++ tailWord_157802) baseStart_157802 baseEnd_157802 := by
    simpa [prefixWord, tailWord_157802, baseEnd_157802] using wordTrace_append hprefix tailTrace_157802
  have hstable : (prefixWord ++ tailWord_157802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157802).length < 2 ^ (prefixWord ++ tailWord_157802).sum := by decide
  have hdescent : baseEnd_157802 < baseStart_157802 := by decide
  rcases family_descends (prefixWord ++ tailWord_157802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157817 : List Nat := [1, 2, 1, 3, 4, 1, 3, 5]
def baseStart_157817 : Nat := 118140960795 + 157817 * 2 ^ 59
def prefixEnd_157817 : Nat := 4983230072969 + 3 ^ 40 * 157817 * 2
def baseEnd_157817 : Nat := 24010659689100525618287

theorem tailTrace_157817 : CollatzResearch.WordTrace tailWord_157817 prefixEnd_157817 24010659689100525618287 := by
  unfold tailWord_157817
  simp only [CollatzResearch.WordTrace]
  refine ⟨5756058869263436842871705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3837372579508957895247803 5756058869263436842871705)
  ·
    refine ⟨4317044151947577632153779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5756058869263436842871705 4317044151947577632153779)
    ·
      refine ⟨6475566227921366448230669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4317044151947577632153779 6475566227921366448230669)
      ·
        refine ⟨2428337335470512418086501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6475566227921366448230669 2428337335470512418086501)
        ·
          refine ⟨455313250400721078391219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2428337335470512418086501 455313250400721078391219)
          ·
            refine ⟨682969875601081617586829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455313250400721078391219 682969875601081617586829)
            ·
              refine ⟨256113703350405606595061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 682969875601081617586829 256113703350405606595061)
              ·
                refine ⟨24010659689100525618287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 256113703350405606595061 24010659689100525618287)
                ·
                  rfl

theorem cell20_157817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 5].length) (baseStart_157817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157817 prefixEnd_157817 := by exact prefixLift 157817
  have htrace : WordTrace (prefixWord ++ tailWord_157817) baseStart_157817 baseEnd_157817 := by
    simpa [prefixWord, tailWord_157817, baseEnd_157817] using wordTrace_append hprefix tailTrace_157817
  have hstable : (prefixWord ++ tailWord_157817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157817).length < 2 ^ (prefixWord ++ tailWord_157817).sum := by decide
  have hdescent : baseEnd_157817 < baseStart_157817 := by decide
  rcases family_descends (prefixWord ++ tailWord_157817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157831 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 6]
def baseStart_157831 : Nat := 118140960795 + 157831 * 2 ^ 59
def prefixEnd_157831 : Nat := 4983230072969 + 3 ^ 40 * 157831 * 2
def baseEnd_157831 : Nat := 72038369048779750388137

theorem tailTrace_157831 : CollatzResearch.WordTrace tailWord_157831 prefixEnd_157831 72038369048779750388137 := by
  unfold tailWord_157831
  simp only [CollatzResearch.WordTrace]
  refine ⟨5756569491212717233881347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3837712994141811489254231 5756569491212717233881347)
  ·
    refine ⟨8634854236819075850822021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5756569491212717233881347 8634854236819075850822021)
    ·
      refine ⟨1619035169403576722029129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8634854236819075850822021 1619035169403576722029129)
      ·
        refine ⟨1214276377052682541521847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1619035169403576722029129 1214276377052682541521847)
        ·
          refine ⟨1821414565579023812282771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1214276377052682541521847 1821414565579023812282771)
          ·
            refine ⟨2732121848368535718424157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1821414565579023812282771 2732121848368535718424157)
            ·
              refine ⟨1024545693138200894409059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2732121848368535718424157 1024545693138200894409059)
              ·
                refine ⟨1536818539707301341613589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1024545693138200894409059 1536818539707301341613589)
                ·
                  refine ⟨72038369048779750388137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1536818539707301341613589 72038369048779750388137)
                  ·
                    rfl

theorem cell20_157831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_157831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157831 prefixEnd_157831 := by exact prefixLift 157831
  have htrace : WordTrace (prefixWord ++ tailWord_157831) baseStart_157831 baseEnd_157831 := by
    simpa [prefixWord, tailWord_157831, baseEnd_157831] using wordTrace_append hprefix tailTrace_157831
  have hstable : (prefixWord ++ tailWord_157831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157831).length < 2 ^ (prefixWord ++ tailWord_157831).sum := by decide
  have hdescent : baseEnd_157831 < baseStart_157831 := by decide
  rcases family_descends (prefixWord ++ tailWord_157831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157834 : List Nat := [3, 1, 2, 3, 1, 3, 3, 4]
def baseStart_157834 : Nat := 118140960795 + 157834 * 2 ^ 59
def prefixEnd_157834 : Nat := 4983230072969 + 3 ^ 40 * 157834 * 2
def baseEnd_157834 : Nat := 24013246110175024429375

theorem tailTrace_157834 : CollatzResearch.WordTrace tailWord_157834 prefixEnd_157834 24013246110175024429375 := by
  unfold tailWord_157834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1439169727550462186560139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3837785940134565830827037 1439169727550462186560139)
  ·
    refine ⟨2158754591325693279840209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1439169727550462186560139 2158754591325693279840209)
    ·
      refine ⟨1619065943494269959880157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2158754591325693279840209 1619065943494269959880157)
      ·
        refine ⟨607149728810351234955059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1619065943494269959880157 607149728810351234955059)
        ·
          refine ⟨910724593215526852432589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607149728810351234955059 910724593215526852432589)
          ·
            refine ⟨341521722455822569662221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 910724593215526852432589 341521722455822569662221)
            ·
              refine ⟨128070645920933463623333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 341521722455822569662221 128070645920933463623333)
              ·
                refine ⟨24013246110175024429375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128070645920933463623333 24013246110175024429375)
                ·
                  rfl

theorem cell20_157834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_157834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157834 prefixEnd_157834 := by exact prefixLift 157834
  have htrace : WordTrace (prefixWord ++ tailWord_157834) baseStart_157834 baseEnd_157834 := by
    simpa [prefixWord, tailWord_157834, baseEnd_157834] using wordTrace_append hprefix tailTrace_157834
  have hstable : (prefixWord ++ tailWord_157834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157834).length < 2 ^ (prefixWord ++ tailWord_157834).sum := by decide
  have hdescent : baseEnd_157834 < baseStart_157834 := by decide
  rcases family_descends (prefixWord ++ tailWord_157834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157854 : List Nat := [4, 3, 1, 1, 4, 1, 1, 2, 3]
def baseStart_157854 : Nat := 118140960795 + 157854 * 2 ^ 59
def prefixEnd_157854 : Nat := 4983230072969 + 3 ^ 40 * 157854 * 2
def baseEnd_157854 : Nat := 72048866875493892621377

theorem tailTrace_157854 : CollatzResearch.WordTrace tailWord_157854 prefixEnd_157854 72048866875493892621377 := by
  unfold tailWord_157854
  simp only [CollatzResearch.WordTrace]
  refine ⟨719676046266174020246077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3838272246752928107979077 719676046266174020246077)
  ·
    refine ⟨269878517349815257592279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 719676046266174020246077 269878517349815257592279)
    ·
      refine ⟨404817776024722886388419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269878517349815257592279 404817776024722886388419)
      ·
        refine ⟨607226664037084329582629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404817776024722886388419 607226664037084329582629)
        ·
          refine ⟨113854999506953311796743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 607226664037084329582629 113854999506953311796743)
          ·
            refine ⟨170782499260429967695115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113854999506953311796743 170782499260429967695115)
            ·
              refine ⟨256173748890644951542673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170782499260429967695115 256173748890644951542673)
              ·
                refine ⟨192130311667983713657005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256173748890644951542673 192130311667983713657005)
                ·
                  refine ⟨72048866875493892621377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 192130311667983713657005 72048866875493892621377)
                  ·
                    rfl

theorem cell20_157854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_157854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157854 prefixEnd_157854 := by exact prefixLift 157854
  have htrace : WordTrace (prefixWord ++ tailWord_157854) baseStart_157854 baseEnd_157854 := by
    simpa [prefixWord, tailWord_157854, baseEnd_157854] using wordTrace_append hprefix tailTrace_157854
  have hstable : (prefixWord ++ tailWord_157854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157854).length < 2 ^ (prefixWord ++ tailWord_157854).sum := by decide
  have hdescent : baseEnd_157854 < baseStart_157854 := by decide
  rcases family_descends (prefixWord ++ tailWord_157854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157855 : List Nat := [1, 1, 2, 6, 1, 2, 7]
def baseStart_157855 : Nat := 118140960795 + 157855 * 2 ^ 59
def prefixEnd_157855 : Nat := 4983230072969 + 3 ^ 40 * 157855 * 2
def baseEnd_157855 : Nat := 8005480366971370398671

theorem tailTrace_157855 : CollatzResearch.WordTrace tailWord_157855 prefixEnd_157855 8005480366971370398671 := by
  unfold tailWord_157855
  simp only [CollatzResearch.WordTrace]
  refine ⟨5757444843125769332755019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3838296562083846221836679 5757444843125769332755019)
  ·
    refine ⟨8636167264688653999132529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5757444843125769332755019 8636167264688653999132529)
    ·
      refine ⟨6477125448516490499349397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8636167264688653999132529 6477125448516490499349397)
      ·
        refine ⟨303615255399210492157003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6477125448516490499349397 303615255399210492157003)
        ·
          refine ⟨455422883098815738235505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303615255399210492157003 455422883098815738235505)
          ·
            refine ⟨341567162324111803676629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 455422883098815738235505 341567162324111803676629)
            ·
              refine ⟨8005480366971370398671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 341567162324111803676629 8005480366971370398671)
              ·
                rfl

theorem cell20_157855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 7].length) (baseStart_157855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157855 prefixEnd_157855 := by exact prefixLift 157855
  have htrace : WordTrace (prefixWord ++ tailWord_157855) baseStart_157855 baseEnd_157855 := by
    simpa [prefixWord, tailWord_157855, baseEnd_157855] using wordTrace_append hprefix tailTrace_157855
  have hstable : (prefixWord ++ tailWord_157855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157855).length < 2 ^ (prefixWord ++ tailWord_157855).sum := by decide
  have hdescent : baseEnd_157855 < baseStart_157855 := by decide
  rcases family_descends (prefixWord ++ tailWord_157855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157858 : List Nat := [3, 3, 1, 3, 1, 1, 3, 2, 3]
def baseStart_157858 : Nat := 118140960795 + 157858 * 2 ^ 59
def prefixEnd_157858 : Nat := 4983230072969 + 3 ^ 40 * 157858 * 2
def baseEnd_157858 : Nat := 72050692584487656488027

theorem tailTrace_157858 : CollatzResearch.WordTrace tailWord_157858 prefixEnd_157858 72050692584487656488027 := by
  unfold tailWord_157858
  simp only [CollatzResearch.WordTrace]
  refine ⟨1439388565528725211278557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3838369508076600563409485 1439388565528725211278557)
  ·
    refine ⟨539770712073271954229459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1439388565528725211278557 539770712073271954229459)
    ·
      refine ⟨809656068109907931344189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 539770712073271954229459 809656068109907931344189)
      ·
        refine ⟨303621025541215474254071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 809656068109907931344189 303621025541215474254071)
        ·
          refine ⟨455431538311823211381107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303621025541215474254071 455431538311823211381107)
          ·
            refine ⟨683147307467734817071661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455431538311823211381107 683147307467734817071661)
            ·
              refine ⟨256180240300400556401873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 683147307467734817071661 256180240300400556401873)
              ·
                refine ⟨192135180225300417301405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256180240300400556401873 192135180225300417301405)
                ·
                  refine ⟨72050692584487656488027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 192135180225300417301405 72050692584487656488027)
                  ·
                    rfl

theorem cell20_157858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_157858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157858 prefixEnd_157858 := by exact prefixLift 157858
  have htrace : WordTrace (prefixWord ++ tailWord_157858) baseStart_157858 baseEnd_157858 := by
    simpa [prefixWord, tailWord_157858, baseEnd_157858] using wordTrace_append hprefix tailTrace_157858
  have hstable : (prefixWord ++ tailWord_157858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157858).length < 2 ^ (prefixWord ++ tailWord_157858).sum := by decide
  have hdescent : baseEnd_157858 < baseStart_157858 := by decide
  rcases family_descends (prefixWord ++ tailWord_157858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157893 : List Nat := [1, 3, 1, 1, 1, 1, 8, 4]
def baseStart_157893 : Nat := 118140960795 + 157893 * 2 ^ 59
def prefixEnd_157893 : Nat := 4983230072969 + 3 ^ 40 * 157893 * 2
def baseEnd_157893 : Nat := 24022222512727696773739

theorem tailTrace_157893 : CollatzResearch.WordTrace tailWord_157893 prefixEnd_157893 24022222512727696773739 := by
  unfold tailWord_157893
  simp only [CollatzResearch.WordTrace]
  refine ⟨5758830816988101822638333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3839220544658734548425555 5758830816988101822638333)
  ·
    refine ⟨2159561556370538183489375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5758830816988101822638333 2159561556370538183489375)
    ·
      refine ⟨3239342334555807275234063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2159561556370538183489375 3239342334555807275234063)
      ·
        refine ⟨4859013501833710912851095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3239342334555807275234063 4859013501833710912851095)
        ·
          refine ⟨7288520252750566369276643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4859013501833710912851095 7288520252750566369276643)
          ·
            refine ⟨10932780379125849553914965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7288520252750566369276643 10932780379125849553914965)
            ·
              refine ⟨128118520067881049459941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 10932780379125849553914965 128118520067881049459941)
              ·
                refine ⟨24022222512727696773739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128118520067881049459941 24022222512727696773739)
                ·
                  rfl

theorem cell20_157893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 4].length) (baseStart_157893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157893 prefixEnd_157893 := by exact prefixLift 157893
  have htrace : WordTrace (prefixWord ++ tailWord_157893) baseStart_157893 baseEnd_157893 := by
    simpa [prefixWord, tailWord_157893, baseEnd_157893] using wordTrace_append hprefix tailTrace_157893
  have hstable : (prefixWord ++ tailWord_157893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157893).length < 2 ^ (prefixWord ++ tailWord_157893).sum := by decide
  have hdescent : baseEnd_157893 < baseStart_157893 := by decide
  rcases family_descends (prefixWord ++ tailWord_157893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157910 : List Nat := [5, 2, 1, 2, 1, 1, 8]
def baseStart_157910 : Nat := 118140960795 + 157910 * 2 ^ 59
def prefixEnd_157910 : Nat := 4983230072969 + 3 ^ 40 * 157910 * 2
def baseEnd_157910 : Nat := 8008269644600731861609

theorem tailTrace_157910 : CollatzResearch.WordTrace tailWord_157910 prefixEnd_157910 8008269644600731861609 := by
  unfold tailWord_157910
  simp only [CollatzResearch.WordTrace]
  refine ⟨359965678620407107875449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3839633905284342484004789 359965678620407107875449)
  ·
    refine ⟨269974258965305330906587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 359965678620407107875449 269974258965305330906587)
    ·
      refine ⟨404961388447957996359881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269974258965305330906587 404961388447957996359881)
      ·
        refine ⟨303721041335968497269911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 404961388447957996359881 303721041335968497269911)
        ·
          refine ⟨455581562003952745904867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303721041335968497269911 455581562003952745904867)
          ·
            refine ⟨683372343005929118857301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455581562003952745904867 683372343005929118857301)
            ·
              refine ⟨8008269644600731861609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 683372343005929118857301 8008269644600731861609)
              ·
                rfl

theorem cell20_157910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 8].length) (baseStart_157910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157910 prefixEnd_157910 := by exact prefixLift 157910
  have htrace : WordTrace (prefixWord ++ tailWord_157910) baseStart_157910 baseEnd_157910 := by
    simpa [prefixWord, tailWord_157910, baseEnd_157910] using wordTrace_append hprefix tailTrace_157910
  have hstable : (prefixWord ++ tailWord_157910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157910).length < 2 ^ (prefixWord ++ tailWord_157910).sum := by decide
  have hdescent : baseEnd_157910 < baseStart_157910 := by decide
  rcases family_descends (prefixWord ++ tailWord_157910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157914 : List Nat := [3, 1, 1, 2, 2, 1, 10]
def baseStart_157914 : Nat := 118140960795 + 157914 * 2 ^ 59
def prefixEnd_157914 : Nat := 4983230072969 + 3 ^ 40 * 157914 * 2
def baseEnd_157914 : Nat := 8008472501155594513459

theorem tailTrace_157914 : CollatzResearch.WordTrace tailWord_157914 prefixEnd_157914 8008472501155594513459 := by
  unfold tailWord_157914
  simp only [CollatzResearch.WordTrace]
  refine ⟨1439899187478005602288199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3839731166608014939435197 1439899187478005602288199)
  ·
    refine ⟨2159848781217008403432299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1439899187478005602288199 2159848781217008403432299)
    ·
      refine ⟨3239773171825512605148449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2159848781217008403432299 3239773171825512605148449)
      ·
        refine ⟨2429829878869134453861337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3239773171825512605148449 2429829878869134453861337)
        ·
          refine ⟨1822372409151850840396003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2429829878869134453861337 1822372409151850840396003)
          ·
            refine ⟨2733558613727776260594005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1822372409151850840396003 2733558613727776260594005)
            ·
              refine ⟨8008472501155594513459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2733558613727776260594005 8008472501155594513459)
              ·
                rfl

theorem cell20_157914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 10].length) (baseStart_157914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157914 prefixEnd_157914 := by exact prefixLift 157914
  have htrace : WordTrace (prefixWord ++ tailWord_157914) baseStart_157914 baseEnd_157914 := by
    simpa [prefixWord, tailWord_157914, baseEnd_157914] using wordTrace_append hprefix tailTrace_157914
  have hstable : (prefixWord ++ tailWord_157914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157914).length < 2 ^ (prefixWord ++ tailWord_157914).sum := by decide
  have hdescent : baseEnd_157914 < baseStart_157914 := by decide
  rcases family_descends (prefixWord ++ tailWord_157914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157916 : List Nat := [2, 2, 5, 2, 1, 1, 3, 2, 2]
def baseStart_157916 : Nat := 118140960795 + 157916 * 2 ^ 59
def prefixEnd_157916 : Nat := 4983230072969 + 3 ^ 40 * 157916 * 2
def baseEnd_157916 : Nat := 72077165364897232554457

theorem tailTrace_157916 : CollatzResearch.WordTrace tailWord_157916 prefixEnd_157916 72077165364897232554457 := by
  unfold tailWord_157916
  simp only [CollatzResearch.WordTrace]
  refine ⟨2879834847952388375362801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3839779797269851167150401 2879834847952388375362801)
  ·
    refine ⟨2159876135964291281522101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2879834847952388375362801 2159876135964291281522101)
    ·
      refine ⟨202488387746652307642697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2159876135964291281522101 202488387746652307642697)
      ·
        refine ⟨151866290809989230732023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202488387746652307642697 151866290809989230732023)
        ·
          refine ⟨227799436214983846098035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151866290809989230732023 227799436214983846098035)
          ·
            refine ⟨341699154322475769147053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227799436214983846098035 341699154322475769147053)
            ·
              refine ⟨128137182870928413430145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 341699154322475769147053 128137182870928413430145)
              ·
                refine ⟨96102887153196310072609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128137182870928413430145 96102887153196310072609)
                ·
                  refine ⟨72077165364897232554457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96102887153196310072609 72077165364897232554457)
                  ·
                    rfl

theorem cell20_157916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 2].length) (baseStart_157916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157916 prefixEnd_157916 := by exact prefixLift 157916
  have htrace : WordTrace (prefixWord ++ tailWord_157916) baseStart_157916 baseEnd_157916 := by
    simpa [prefixWord, tailWord_157916, baseEnd_157916] using wordTrace_append hprefix tailTrace_157916
  have hstable : (prefixWord ++ tailWord_157916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157916).length < 2 ^ (prefixWord ++ tailWord_157916).sum := by decide
  have hdescent : baseEnd_157916 < baseStart_157916 := by decide
  rcases family_descends (prefixWord ++ tailWord_157916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157917 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 5]
def baseStart_157917 : Nat := 118140960795 + 157917 * 2 ^ 59
def prefixEnd_157917 : Nat := 4983230072969 + 3 ^ 40 * 157917 * 2
def baseEnd_157917 : Nat := 72077621792145673521119

theorem tailTrace_157917 : CollatzResearch.WordTrace tailWord_157917 prefixEnd_157917 72077621792145673521119 := by
  unfold tailWord_157917
  simp only [CollatzResearch.WordTrace]
  refine ⟨5759706168901153921512005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3839804112600769281008003 5759706168901153921512005)
  ·
    refine ⟨1079944906668966360283501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5759706168901153921512005 1079944906668966360283501)
    ·
      refine ⟨404979340000862385106313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1079944906668966360283501 404979340000862385106313)
      ·
        refine ⟨303734505000646788829735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 404979340000862385106313 303734505000646788829735)
        ·
          refine ⟨455601757500970183244603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303734505000646788829735 455601757500970183244603)
          ·
            refine ⟨683402636251455274866905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455601757500970183244603 683402636251455274866905)
            ·
              refine ⟨512551977188591456150179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 683402636251455274866905 512551977188591456150179)
              ·
                refine ⟨768827965782887184225269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 512551977188591456150179 768827965782887184225269)
                ·
                  refine ⟨72077621792145673521119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 768827965782887184225269 72077621792145673521119)
                  ·
                    rfl

theorem cell20_157917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_157917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157917 prefixEnd_157917 := by exact prefixLift 157917
  have htrace : WordTrace (prefixWord ++ tailWord_157917) baseStart_157917 baseEnd_157917 := by
    simpa [prefixWord, tailWord_157917, baseEnd_157917] using wordTrace_append hprefix tailTrace_157917
  have hstable : (prefixWord ++ tailWord_157917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157917).length < 2 ^ (prefixWord ++ tailWord_157917).sum := by decide
  have hdescent : baseEnd_157917 < baseStart_157917 := by decide
  rcases family_descends (prefixWord ++ tailWord_157917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157952 : List Nat := [2, 1, 1, 2, 1, 1, 6, 6]
def baseStart_157952 : Nat := 118140960795 + 157952 * 2 ^ 59
def prefixEnd_157952 : Nat := 4983230072969 + 3 ^ 40 * 157952 * 2
def baseEnd_157952 : Nat := 24031198915280369118103

theorem tailTrace_157952 : CollatzResearch.WordTrace tailWord_157952 prefixEnd_157952 24031198915280369118103 := by
  unfold tailWord_157952
  simp only [CollatzResearch.WordTrace]
  refine ⟨2880491361887177449518055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3840655149182903266024073 2880491361887177449518055)
  ·
    refine ⟨4320737042830766174277083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2880491361887177449518055 4320737042830766174277083)
    ·
      refine ⟨6481105564246149261415625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4320737042830766174277083 6481105564246149261415625)
      ·
        refine ⟨4860829173184611946061719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6481105564246149261415625 4860829173184611946061719)
        ·
          refine ⟨7291243759776917919092579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4860829173184611946061719 7291243759776917919092579)
          ·
            refine ⟨10936865639665376878638869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7291243759776917919092579 10936865639665376878638869)
            ·
              refine ⟨512665576859314541186197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10936865639665376878638869 512665576859314541186197)
              ·
                refine ⟨24031198915280369118103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 512665576859314541186197 24031198915280369118103)
                ·
                  rfl

theorem cell20_157952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_157952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157952 prefixEnd_157952 := by exact prefixLift 157952
  have htrace : WordTrace (prefixWord ++ tailWord_157952) baseStart_157952 baseEnd_157952 := by
    simpa [prefixWord, tailWord_157952, baseEnd_157952] using wordTrace_append hprefix tailTrace_157952
  have hstable : (prefixWord ++ tailWord_157952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157952).length < 2 ^ (prefixWord ++ tailWord_157952).sum := by decide
  have hdescent : baseEnd_157952 < baseStart_157952 := by decide
  rcases family_descends (prefixWord ++ tailWord_157952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157979 : List Nat := [1, 1, 1, 1, 1, 1, 10, 2, 2]
def baseStart_157979 : Nat := 118140960795 + 157979 * 2 ^ 59
def prefixEnd_157979 : Nat := 4983230072969 + 3 ^ 40 * 157979 * 2
def baseEnd_157979 : Nat := 72105920281549013454199

theorem tailTrace_157979 : CollatzResearch.WordTrace tailWord_157979 prefixEnd_157979 72105920281549013454199 := by
  unfold tailWord_157979
  simp only [CollatzResearch.WordTrace]
  refine ⟨5761967494676538510268991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3841311663117692340179327 5761967494676538510268991)
  ·
    refine ⟨8642951242014807765403487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5761967494676538510268991 8642951242014807765403487)
    ·
      refine ⟨12964426863022211648105231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8642951242014807765403487 12964426863022211648105231)
      ·
        refine ⟨19446640294533317472157847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12964426863022211648105231 19446640294533317472157847)
        ·
          refine ⟨29169960441799976208236771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19446640294533317472157847 29169960441799976208236771)
          ·
            refine ⟨43754940662699964312355157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29169960441799976208236771 43754940662699964312355157)
            ·
              refine ⟨128188302722753801696353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 43754940662699964312355157 128188302722753801696353)
              ·
                refine ⟨96141227042065351272265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128188302722753801696353 96141227042065351272265)
                ·
                  refine ⟨72105920281549013454199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96141227042065351272265 72105920281549013454199)
                  ·
                    rfl

theorem cell20_157979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 2].length) (baseStart_157979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157979 prefixEnd_157979 := by exact prefixLift 157979
  have htrace : WordTrace (prefixWord ++ tailWord_157979) baseStart_157979 baseEnd_157979 := by
    simpa [prefixWord, tailWord_157979, baseEnd_157979] using wordTrace_append hprefix tailTrace_157979
  have hstable : (prefixWord ++ tailWord_157979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157979).length < 2 ^ (prefixWord ++ tailWord_157979).sum := by decide
  have hdescent : baseEnd_157979 < baseStart_157979 := by decide
  rcases family_descends (prefixWord ++ tailWord_157979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157986 : List Nat := [3, 3, 1, 1, 3, 3, 1, 5]
def baseStart_157986 : Nat := 118140960795 + 157986 * 2 ^ 59
def prefixEnd_157986 : Nat := 4983230072969 + 3 ^ 40 * 157986 * 2
def baseEnd_157986 : Nat := 24036371757429366740279

theorem tailTrace_157986 : CollatzResearch.WordTrace tailWord_157986 prefixEnd_157986 24036371757429366740279 := by
  unfold tailWord_157986
  simp only [CollatzResearch.WordTrace]
  refine ⟨1440555701412794676443453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3841481870434119137182541 1440555701412794676443453)
  ·
    refine ⟨540208388029798003666295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1440555701412794676443453 540208388029798003666295)
    ·
      refine ⟨810312582044697005499443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 540208388029798003666295 810312582044697005499443)
      ·
        refine ⟨1215468873067045508249165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 810312582044697005499443 1215468873067045508249165)
        ·
          refine ⟨455800827400142065593437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1215468873067045508249165 455800827400142065593437)
          ·
            refine ⟨170925310275053274597539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 455800827400142065593437 170925310275053274597539)
            ·
              refine ⟨256387965412579911896309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170925310275053274597539 256387965412579911896309)
              ·
                refine ⟨24036371757429366740279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 256387965412579911896309 24036371757429366740279)
                ·
                  rfl

theorem cell20_157986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_157986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_157986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_157986 prefixEnd_157986 := by exact prefixLift 157986
  have htrace : WordTrace (prefixWord ++ tailWord_157986) baseStart_157986 baseEnd_157986 := by
    simpa [prefixWord, tailWord_157986, baseEnd_157986] using wordTrace_append hprefix tailTrace_157986
  have hstable : (prefixWord ++ tailWord_157986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157986).length < 2 ^ (prefixWord ++ tailWord_157986).sum := by decide
  have hdescent : baseEnd_157986 < baseStart_157986 := by decide
  rcases family_descends (prefixWord ++ tailWord_157986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158028 : List Nat := [2, 2, 1, 3, 2, 1, 9]
def baseStart_158028 : Nat := 118140960795 + 158028 * 2 ^ 59
def prefixEnd_158028 : Nat := 4983230072969 + 3 ^ 40 * 158028 * 2
def baseEnd_158028 : Nat := 8014253912969180091185

theorem tailTrace_158028 : CollatzResearch.WordTrace tailWord_158028 prefixEnd_158028 8014253912969180091185 := by
  unfold tailWord_158028
  simp only [CollatzResearch.WordTrace]
  refine ⟨2881877335749509939401369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3842503114332679919201825 2881877335749509939401369)
  ·
    refine ⟨2161408001812132454551027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2881877335749509939401369 2161408001812132454551027)
    ·
      refine ⟨3242112002718198681826541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2161408001812132454551027 3242112002718198681826541)
      ·
        refine ⟨1215792001019324505684953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3242112002718198681826541 1215792001019324505684953)
        ·
          refine ⟨911844000764493379263715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1215792001019324505684953 911844000764493379263715)
          ·
            refine ⟨1367766001146740068895573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 911844000764493379263715 1367766001146740068895573)
            ·
              refine ⟨8014253912969180091185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1367766001146740068895573 8014253912969180091185)
              ·
                rfl

theorem cell20_158028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 9].length) (baseStart_158028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158028 prefixEnd_158028 := by exact prefixLift 158028
  have htrace : WordTrace (prefixWord ++ tailWord_158028) baseStart_158028 baseEnd_158028 := by
    simpa [prefixWord, tailWord_158028, baseEnd_158028] using wordTrace_append hprefix tailTrace_158028
  have hstable : (prefixWord ++ tailWord_158028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158028).length < 2 ^ (prefixWord ++ tailWord_158028).sum := by decide
  have hdescent : baseEnd_158028 < baseStart_158028 := by decide
  rcases family_descends (prefixWord ++ tailWord_158028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158048 : List Nat := [2, 1, 1, 3, 5, 1, 3, 1, 3]
def baseStart_158048 : Nat := 118140960795 + 158048 * 2 ^ 59
def prefixEnd_158048 : Nat := 4983230072969 + 3 ^ 40 * 158048 * 2
def baseEnd_158048 : Nat := 72137413761691440153917

theorem tailTrace_158048 : CollatzResearch.WordTrace tailWord_158048 prefixEnd_158048 72137413761691440153917 := by
  unfold tailWord_158048
  simp only [CollatzResearch.WordTrace]
  refine ⟨2882242065713281647265399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3842989420951042196353865 2882242065713281647265399)
  ·
    refine ⟨4323363098569922470898099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2882242065713281647265399 4323363098569922470898099)
    ·
      refine ⟨6485044647854883706347149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4323363098569922470898099 6485044647854883706347149)
      ·
        refine ⟨2431891742945581389880181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6485044647854883706347149 2431891742945581389880181)
        ·
          refine ⟨227989850901148255301267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2431891742945581389880181 227989850901148255301267)
          ·
            refine ⟨341984776351722382951901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227989850901148255301267 341984776351722382951901)
            ·
              refine ⟨128244291131895893606963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 341984776351722382951901 128244291131895893606963)
              ·
                refine ⟨192366436697843840410445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128244291131895893606963 192366436697843840410445)
                ·
                  refine ⟨72137413761691440153917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 192366436697843840410445 72137413761691440153917)
                  ·
                    rfl

theorem cell20_158048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 3].length) (baseStart_158048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158048 prefixEnd_158048 := by exact prefixLift 158048
  have htrace : WordTrace (prefixWord ++ tailWord_158048) baseStart_158048 baseEnd_158048 := by
    simpa [prefixWord, tailWord_158048, baseEnd_158048] using wordTrace_append hprefix tailTrace_158048
  have hstable : (prefixWord ++ tailWord_158048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158048).length < 2 ^ (prefixWord ++ tailWord_158048).sum := by decide
  have hdescent : baseEnd_158048 < baseStart_158048 := by decide
  rcases family_descends (prefixWord ++ tailWord_158048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158076 : List Nat := [2, 2, 2, 1, 1, 1, 2, 7, 2]
def baseStart_158076 : Nat := 118140960795 + 158076 * 2 ^ 59
def prefixEnd_158076 : Nat := 4983230072969 + 3 ^ 40 * 158076 * 2
def baseEnd_158076 : Nat := 72150193724647787220469

theorem tailTrace_158076 : CollatzResearch.WordTrace tailWord_158076 prefixEnd_158076 72150193724647787220469 := by
  unfold tailWord_158076
  simp only [CollatzResearch.WordTrace]
  refine ⟨2882752687662562038275041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3843670250216749384366721 2882752687662562038275041)
  ·
    refine ⟨2162064515746921528706281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2882752687662562038275041 2162064515746921528706281)
    ·
      refine ⟨1621548386810191146529711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2162064515746921528706281 1621548386810191146529711)
      ·
        refine ⟨2432322580215286719794567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1621548386810191146529711 2432322580215286719794567)
        ·
          refine ⟨3648483870322930079691851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2432322580215286719794567 3648483870322930079691851)
          ·
            refine ⟨5472725805484395119537777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3648483870322930079691851 5472725805484395119537777)
            ·
              refine ⟨4104544354113296339653333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5472725805484395119537777 4104544354113296339653333)
              ·
                refine ⟨96200258299530382960625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4104544354113296339653333 96200258299530382960625)
                ·
                  refine ⟨72150193724647787220469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96200258299530382960625 72150193724647787220469)
                  ·
                    rfl

theorem cell20_158076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 2].length) (baseStart_158076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158076 prefixEnd_158076 := by exact prefixLift 158076
  have htrace : WordTrace (prefixWord ++ tailWord_158076) baseStart_158076 baseEnd_158076 := by
    simpa [prefixWord, tailWord_158076, baseEnd_158076] using wordTrace_append hprefix tailTrace_158076
  have hstable : (prefixWord ++ tailWord_158076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158076).length < 2 ^ (prefixWord ++ tailWord_158076).sum := by decide
  have hdescent : baseEnd_158076 < baseStart_158076 := by decide
  rcases family_descends (prefixWord ++ tailWord_158076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158083 : List Nat := [1, 1, 1, 3, 6, 2, 6]
def baseStart_158083 : Nat := 118140960795 + 158083 * 2 ^ 59
def prefixEnd_158083 : Nat := 4983230072969 + 3 ^ 40 * 158083 * 2
def baseEnd_158083 : Nat := 8017043190598541554123

theorem tailTrace_158083 : CollatzResearch.WordTrace tailWord_158083 prefixEnd_158083 8017043190598541554123 := by
  unfold tailWord_158083
  simp only [CollatzResearch.WordTrace]
  refine ⟨5765760686299764272054903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3843840457533176181369935 5765760686299764272054903)
  ·
    refine ⟨8648641029449646408082355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5765760686299764272054903 8648641029449646408082355)
    ·
      refine ⟨12972961544174469612123533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8648641029449646408082355 12972961544174469612123533)
      ·
        refine ⟨4864860579065426104546325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12972961544174469612123533 4864860579065426104546325)
        ·
          refine ⟨228040339643691848650609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4864860579065426104546325 228040339643691848650609)
          ·
            refine ⟨171030254732768886487957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228040339643691848650609 171030254732768886487957)
            ·
              refine ⟨8017043190598541554123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 171030254732768886487957 8017043190598541554123)
              ·
                rfl

theorem cell20_158083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 6].length) (baseStart_158083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158083 prefixEnd_158083 := by exact prefixLift 158083
  have htrace : WordTrace (prefixWord ++ tailWord_158083) baseStart_158083 baseEnd_158083 := by
    simpa [prefixWord, tailWord_158083, baseEnd_158083] using wordTrace_append hprefix tailTrace_158083
  have hstable : (prefixWord ++ tailWord_158083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158083).length < 2 ^ (prefixWord ++ tailWord_158083).sum := by decide
  have hdescent : baseEnd_158083 < baseStart_158083 := by decide
  rcases family_descends (prefixWord ++ tailWord_158083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158100 : List Nat := [2, 4, 2, 1, 3, 1, 2, 5]
def baseStart_158100 : Nat := 118140960795 + 158100 * 2 ^ 59
def prefixEnd_158100 : Nat := 4983230072969 + 3 ^ 40 * 158100 * 2
def baseEnd_158100 : Nat := 24053715992870123473457

theorem tailTrace_158100 : CollatzResearch.WordTrace tailWord_158100 prefixEnd_158100 24053715992870123473457 := by
  unfold tailWord_158100
  simp only [CollatzResearch.WordTrace]
  refine ⟨2883190363619088087711877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3844253818158784116949169 2883190363619088087711877)
  ·
    refine ⟨540598193178579016445977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2883190363619088087711877 540598193178579016445977)
    ·
      refine ⟨405448644883934262334483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 540598193178579016445977 405448644883934262334483)
      ·
        refine ⟨608172967325901393501725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405448644883934262334483 608172967325901393501725)
        ·
          refine ⟨228064862747213022563147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 608172967325901393501725 228064862747213022563147)
          ·
            refine ⟨342097294120819533844721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228064862747213022563147 342097294120819533844721)
            ·
              refine ⟨256572970590614650383541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342097294120819533844721 256572970590614650383541)
              ·
                refine ⟨24053715992870123473457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 256572970590614650383541 24053715992870123473457)
                ·
                  rfl

theorem cell20_158100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 5].length) (baseStart_158100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158100 prefixEnd_158100 := by exact prefixLift 158100
  have htrace : WordTrace (prefixWord ++ tailWord_158100) baseStart_158100 baseEnd_158100 := by
    simpa [prefixWord, tailWord_158100, baseEnd_158100] using wordTrace_append hprefix tailTrace_158100
  have hstable : (prefixWord ++ tailWord_158100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158100).length < 2 ^ (prefixWord ++ tailWord_158100).sum := by decide
  have hdescent : baseEnd_158100 < baseStart_158100 := by decide
  rcases family_descends (prefixWord ++ tailWord_158100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158148 : List Nat := [2, 3, 3, 2, 2, 1, 1, 4, 2]
def baseStart_158148 : Nat := 118140960795 + 158148 * 2 ^ 59
def prefixEnd_158148 : Nat := 4983230072969 + 3 ^ 40 * 158148 * 2
def baseEnd_158148 : Nat := 72183056486535536820175

theorem tailTrace_158148 : CollatzResearch.WordTrace tailWord_158148 prefixEnd_158148 72183056486535536820175 := by
  unfold tailWord_158148
  simp only [CollatzResearch.WordTrace]
  refine ⟨2884065715532140186585549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3845420954042853582114065 2884065715532140186585549)
  ·
    refine ⟨1081524643324552569969581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2884065715532140186585549 1081524643324552569969581)
    ·
      refine ⟨405571741246707213738593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1081524643324552569969581 405571741246707213738593)
      ·
        refine ⟨304178805935030410303945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 405571741246707213738593 304178805935030410303945)
        ·
          refine ⟨228134104451272807727959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304178805935030410303945 228134104451272807727959)
          ·
            refine ⟨342201156676909211591939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228134104451272807727959 342201156676909211591939)
            ·
              refine ⟨513301735015363817387909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342201156676909211591939 513301735015363817387909)
              ·
                refine ⟨96244075315380715760233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 513301735015363817387909 96244075315380715760233)
                ·
                  refine ⟨72183056486535536820175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96244075315380715760233 72183056486535536820175)
                  ·
                    rfl

theorem cell20_158148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_158148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158148 prefixEnd_158148 := by exact prefixLift 158148
  have htrace : WordTrace (prefixWord ++ tailWord_158148) baseStart_158148 baseEnd_158148 := by
    simpa [prefixWord, tailWord_158148, baseEnd_158148] using wordTrace_append hprefix tailTrace_158148
  have hstable : (prefixWord ++ tailWord_158148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158148).length < 2 ^ (prefixWord ++ tailWord_158148).sum := by decide
  have hdescent : baseEnd_158148 < baseStart_158148 := by decide
  rcases family_descends (prefixWord ++ tailWord_158148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158187 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 5]
def baseStart_158187 : Nat := 118140960795 + 158187 * 2 ^ 59
def prefixEnd_158187 : Nat := 4983230072969 + 3 ^ 40 * 158187 * 2
def baseEnd_158187 : Nat := 72200857149224734520015

theorem tailTrace_158187 : CollatzResearch.WordTrace tailWord_158187 prefixEnd_158187 72200857149224734520015 := by
  unfold tailWord_158187
  simp only [CollatzResearch.WordTrace]
  refine ⟨5769553877922990033840815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3846369251948660022560543 5769553877922990033840815)
  ·
    refine ⟨8654330816884485050761223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5769553877922990033840815 8654330816884485050761223)
    ·
      refine ⟨12981496225326727576141835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8654330816884485050761223 12981496225326727576141835)
      ·
        refine ⟨19472244337990091364212753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12981496225326727576141835 19472244337990091364212753)
        ·
          refine ⟨14604183253492568523159565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19472244337990091364212753 14604183253492568523159565)
          ·
            refine ⟨5476568720059713196184837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14604183253492568523159565 5476568720059713196184837)
            ·
              refine ⟨1026856635011196224284657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5476568720059713196184837 1026856635011196224284657)
              ·
                refine ⟨770142476258397168213493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1026856635011196224284657 770142476258397168213493)
                ·
                  refine ⟨72200857149224734520015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 770142476258397168213493 72200857149224734520015)
                  ·
                    rfl

theorem cell20_158187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_158187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158187 prefixEnd_158187 := by exact prefixLift 158187
  have htrace : WordTrace (prefixWord ++ tailWord_158187) baseStart_158187 baseEnd_158187 := by
    simpa [prefixWord, tailWord_158187, baseEnd_158187] using wordTrace_append hprefix tailTrace_158187
  have hstable : (prefixWord ++ tailWord_158187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158187).length < 2 ^ (prefixWord ++ tailWord_158187).sum := by decide
  have hdescent : baseEnd_158187 < baseStart_158187 := by decide
  rcases family_descends (prefixWord ++ tailWord_158187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158211 : List Nat := [1, 1, 1, 3, 2, 1, 6, 1, 4]
def baseStart_158211 : Nat := 118140960795 + 158211 * 2 ^ 59
def prefixEnd_158211 : Nat := 4983230072969 + 3 ^ 40 * 158211 * 2
def baseEnd_158211 : Nat := 72211811403187317719917

theorem tailTrace_158211 : CollatzResearch.WordTrace tailWord_158211 prefixEnd_158211 72211811403187317719917 := by
  unfold tailWord_158211
  simp only [CollatzResearch.WordTrace]
  refine ⟨5770429229836042132714487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3846952819890694755142991 5770429229836042132714487)
  ·
    refine ⟨8655643844754063199071731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5770429229836042132714487 8655643844754063199071731)
    ·
      refine ⟨12983465767131094798607597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8655643844754063199071731 12983465767131094798607597)
      ·
        refine ⟨4868799662674160549477849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12983465767131094798607597 4868799662674160549477849)
        ·
          refine ⟨3651599747005620412108387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4868799662674160549477849 3651599747005620412108387)
          ·
            refine ⟨5477399620508430618162581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3651599747005620412108387 5477399620508430618162581)
            ·
              refine ⟨256753107211332685226371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5477399620508430618162581 256753107211332685226371)
              ·
                refine ⟨385129660816999027839557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256753107211332685226371 385129660816999027839557)
                ·
                  refine ⟨72211811403187317719917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 385129660816999027839557 72211811403187317719917)
                  ·
                    rfl

theorem cell20_158211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 4].length) (baseStart_158211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158211 prefixEnd_158211 := by exact prefixLift 158211
  have htrace : WordTrace (prefixWord ++ tailWord_158211) baseStart_158211 baseEnd_158211 := by
    simpa [prefixWord, tailWord_158211, baseEnd_158211] using wordTrace_append hprefix tailTrace_158211
  have hstable : (prefixWord ++ tailWord_158211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158211).length < 2 ^ (prefixWord ++ tailWord_158211).sum := by decide
  have hdescent : baseEnd_158211 < baseStart_158211 := by decide
  rcases family_descends (prefixWord ++ tailWord_158211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158218 : List Nat := [3, 1, 2, 2, 2, 1, 2, 7]
def baseStart_158218 : Nat := 118140960795 + 158218 * 2 ^ 59
def prefixEnd_158218 : Nat := 4983230072969 + 3 ^ 40 * 158218 * 2
def baseEnd_158218 : Nat := 24071668797975468162185

theorem tailTrace_158218 : CollatzResearch.WordTrace tailWord_158218 prefixEnd_158218 24071668797975468162185 := by
  unfold tailWord_158218
  simp only [CollatzResearch.WordTrace]
  refine ⟨1442671135202670582054827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3847123027207121552146205 1442671135202670582054827)
  ·
    refine ⟨2164006702804005873082241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1442671135202670582054827 2164006702804005873082241)
    ·
      refine ⟨1623005027103004404811681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2164006702804005873082241 1623005027103004404811681)
      ·
        refine ⟨1217253770327253303608761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1623005027103004404811681 1217253770327253303608761)
        ·
          refine ⟨912940327745439977706571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1217253770327253303608761 912940327745439977706571)
          ·
            refine ⟨1369410491618159966559857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912940327745439977706571 1369410491618159966559857)
            ·
              refine ⟨1027057868713619974919893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1369410491618159966559857 1027057868713619974919893)
              ·
                refine ⟨24071668797975468162185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1027057868713619974919893 24071668797975468162185)
                ·
                  rfl

theorem cell20_158218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_158218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158218 prefixEnd_158218 := by exact prefixLift 158218
  have htrace : WordTrace (prefixWord ++ tailWord_158218) baseStart_158218 baseEnd_158218 := by
    simpa [prefixWord, tailWord_158218, baseEnd_158218] using wordTrace_append hprefix tailTrace_158218
  have hstable : (prefixWord ++ tailWord_158218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158218).length < 2 ^ (prefixWord ++ tailWord_158218).sum := by decide
  have hdescent : baseEnd_158218 < baseStart_158218 := by decide
  rcases family_descends (prefixWord ++ tailWord_158218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158231 : List Nat := [1, 1, 3, 6, 1, 2, 2, 4]
def baseStart_158231 : Nat := 118140960795 + 158231 * 2 ^ 59
def prefixEnd_158231 : Nat := 4983230072969 + 3 ^ 40 * 158231 * 2
def baseEnd_158231 : Nat := 24073646649385379017723

theorem tailTrace_158231 : CollatzResearch.WordTrace tailWord_158231 prefixEnd_158231 24073646649385379017723 := by
  unfold tailWord_158231
  simp only [CollatzResearch.WordTrace]
  refine ⟨5771158689763585548442547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3847439126509057032295031 5771158689763585548442547)
  ·
    refine ⟨8656738034645378322663821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5771158689763585548442547 8656738034645378322663821)
    ·
      refine ⟨3246276762992016870998933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8656738034645378322663821 3246276762992016870998933)
      ·
        refine ⟨152169223265250790828075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3246276762992016870998933 152169223265250790828075)
        ·
          refine ⟨228253834897876186242113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152169223265250790828075 228253834897876186242113)
          ·
            refine ⟨171190376173407139681585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228253834897876186242113 171190376173407139681585)
            ·
              refine ⟨128392782130055354761189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171190376173407139681585 128392782130055354761189)
              ·
                refine ⟨24073646649385379017723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128392782130055354761189 24073646649385379017723)
                ·
                  rfl

theorem cell20_158231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 4].length) (baseStart_158231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158231 prefixEnd_158231 := by exact prefixLift 158231
  have htrace : WordTrace (prefixWord ++ tailWord_158231) baseStart_158231 baseEnd_158231 := by
    simpa [prefixWord, tailWord_158231, baseEnd_158231] using wordTrace_append hprefix tailTrace_158231
  have hstable : (prefixWord ++ tailWord_158231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158231).length < 2 ^ (prefixWord ++ tailWord_158231).sum := by decide
  have hdescent : baseEnd_158231 < baseStart_158231 := by decide
  rcases family_descends (prefixWord ++ tailWord_158231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158263 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 5]
def baseStart_158263 : Nat := 118140960795 + 158263 * 2 ^ 59
def prefixEnd_158263 : Nat := 4983230072969 + 3 ^ 40 * 158263 * 2
def baseEnd_158263 : Nat := 72235545620106247986371

theorem tailTrace_158263 : CollatzResearch.WordTrace tailWord_158263 prefixEnd_158263 72235545620106247986371 := by
  unfold tailWord_158263
  simp only [CollatzResearch.WordTrace]
  refine ⟨5772325825647655013607443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3848217217098436675738295 5772325825647655013607443)
  ·
    refine ⟨8658488738471482520411165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5772325825647655013607443 8658488738471482520411165)
    ·
      refine ⟨3246933276926805945154187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8658488738471482520411165 3246933276926805945154187)
      ·
        refine ⟨4870399915390208917731281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3246933276926805945154187 4870399915390208917731281)
        ·
          refine ⟨3652799936542656688298461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4870399915390208917731281 3652799936542656688298461)
          ·
            refine ⟨1369799976203496258111923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3652799936542656688298461 1369799976203496258111923)
            ·
              refine ⟨2054699964305244387167885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1369799976203496258111923 2054699964305244387167885)
              ·
                refine ⟨770512486614466645187957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2054699964305244387167885 770512486614466645187957)
                ·
                  refine ⟨72235545620106247986371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 770512486614466645187957 72235545620106247986371)
                  ·
                    rfl

theorem cell20_158263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_158263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158263 prefixEnd_158263 := by exact prefixLift 158263
  have htrace : WordTrace (prefixWord ++ tailWord_158263) baseStart_158263 baseEnd_158263 := by
    simpa [prefixWord, tailWord_158263, baseEnd_158263] using wordTrace_append hprefix tailTrace_158263
  have hstable : (prefixWord ++ tailWord_158263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158263).length < 2 ^ (prefixWord ++ tailWord_158263).sum := by decide
  have hdescent : baseEnd_158263 < baseStart_158263 := by decide
  rcases family_descends (prefixWord ++ tailWord_158263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158266 : List Nat := [3, 1, 1, 1, 3, 5, 1, 1, 4]
def baseStart_158266 : Nat := 118140960795 + 158266 * 2 ^ 59
def prefixEnd_158266 : Nat := 4983230072969 + 3 ^ 40 * 158266 * 2
def baseEnd_158266 : Nat := 72236914901851570886359

theorem tailTrace_158266 : CollatzResearch.WordTrace tailWord_158266 prefixEnd_158266 72236914901851570886359 := by
  unfold tailWord_158266
  simp only [CollatzResearch.WordTrace]
  refine ⟨1443108811159196631491663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3848290163091191017311101 1443108811159196631491663)
  ·
    refine ⟨2164663216738794947237495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1443108811159196631491663 2164663216738794947237495)
    ·
      refine ⟨3246994825108192420856243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2164663216738794947237495 3246994825108192420856243)
      ·
        refine ⟨4870492237662288631284365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3246994825108192420856243 4870492237662288631284365)
        ·
          refine ⟨1826434589123358236731637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4870492237662288631284365 1826434589123358236731637)
          ·
            refine ⟨171228242730314834693591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1826434589123358236731637 171228242730314834693591)
            ·
              refine ⟨256842364095472252040387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171228242730314834693591 256842364095472252040387)
              ·
                refine ⟨385263546143208378060581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256842364095472252040387 385263546143208378060581)
                ·
                  refine ⟨72236914901851570886359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 385263546143208378060581 72236914901851570886359)
                  ·
                    rfl

theorem cell20_158266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_158266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158266 prefixEnd_158266 := by exact prefixLift 158266
  have htrace : WordTrace (prefixWord ++ tailWord_158266) baseStart_158266 baseEnd_158266 := by
    simpa [prefixWord, tailWord_158266, baseEnd_158266] using wordTrace_append hprefix tailTrace_158266
  have hstable : (prefixWord ++ tailWord_158266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158266).length < 2 ^ (prefixWord ++ tailWord_158266).sum := by decide
  have hdescent : baseEnd_158266 < baseStart_158266 := by decide
  rcases family_descends (prefixWord ++ tailWord_158266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158273 : List Nat := [1, 2, 5, 1, 1, 3, 2, 5]
def baseStart_158273 : Nat := 118140960795 + 158273 * 2 ^ 59
def prefixEnd_158273 : Nat := 4983230072969 + 3 ^ 40 * 158273 * 2
def baseEnd_158273 : Nat := 24080036630863552550999

theorem tailTrace_158273 : CollatzResearch.WordTrace tailWord_158273 prefixEnd_158273 24080036630863552550999 := by
  unfold tailWord_158273
  simp only [CollatzResearch.WordTrace]
  refine ⟨5772690555611426721471473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3848460370407617814314315 5772690555611426721471473)
  ·
    refine ⟨4329517916708570041103605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5772690555611426721471473 4329517916708570041103605)
    ·
      refine ⟨405892304691428441353463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4329517916708570041103605 405892304691428441353463)
      ·
        refine ⟨608838457037142662030195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405892304691428441353463 608838457037142662030195)
        ·
          refine ⟨913257685555713993045293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 608838457037142662030195 913257685555713993045293)
          ·
            refine ⟨342471632083392747391985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 913257685555713993045293 342471632083392747391985)
            ·
              refine ⟨256853724062544560543989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342471632083392747391985 256853724062544560543989)
              ·
                refine ⟨24080036630863552550999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 256853724062544560543989 24080036630863552550999)
                ·
                  rfl

theorem cell20_158273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 5].length) (baseStart_158273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158273 prefixEnd_158273 := by exact prefixLift 158273
  have htrace : WordTrace (prefixWord ++ tailWord_158273) baseStart_158273 baseEnd_158273 := by
    simpa [prefixWord, tailWord_158273, baseEnd_158273] using wordTrace_append hprefix tailTrace_158273
  have hstable : (prefixWord ++ tailWord_158273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158273).length < 2 ^ (prefixWord ++ tailWord_158273).sum := by decide
  have hdescent : baseEnd_158273 < baseStart_158273 := by decide
  rcases family_descends (prefixWord ++ tailWord_158273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158332 : List Nat := [2, 2, 2, 1, 1, 2, 5, 5]
def baseStart_158332 : Nat := 118140960795 + 158332 * 2 ^ 59
def prefixEnd_158332 : Nat := 4983230072969 + 3 ^ 40 * 158332 * 2
def baseEnd_158332 : Nat := 24089013033416224895363

theorem tailTrace_158332 : CollatzResearch.WordTrace tailWord_158332 prefixEnd_158332 24089013033416224895363 := by
  unfold tailWord_158332
  simp only [CollatzResearch.WordTrace]
  refine ⟨2887421231198839898934625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3849894974931786531912833 2887421231198839898934625)
  ·
    refine ⟨2165565923399129924200969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2887421231198839898934625 2165565923399129924200969)
    ·
      refine ⟨1624174442549347443150727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2165565923399129924200969 1624174442549347443150727)
      ·
        refine ⟨2436261663824021164726091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1624174442549347443150727 2436261663824021164726091)
        ·
          refine ⟨3654392495736031747089137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2436261663824021164726091 3654392495736031747089137)
          ·
            refine ⟨2740794371802023810316853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3654392495736031747089137 2740794371802023810316853)
            ·
              refine ⟨256949472356439732217205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2740794371802023810316853 256949472356439732217205)
              ·
                refine ⟨24089013033416224895363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 256949472356439732217205 24089013033416224895363)
                ·
                  rfl

theorem cell20_158332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_158332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158332 prefixEnd_158332 := by exact prefixLift 158332
  have htrace : WordTrace (prefixWord ++ tailWord_158332) baseStart_158332 baseEnd_158332 := by
    simpa [prefixWord, tailWord_158332, baseEnd_158332] using wordTrace_append hprefix tailTrace_158332
  have hstable : (prefixWord ++ tailWord_158332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158332).length < 2 ^ (prefixWord ++ tailWord_158332).sum := by decide
  have hdescent : baseEnd_158332 < baseStart_158332 := by decide
  rcases family_descends (prefixWord ++ tailWord_158332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158404 : List Nat := [2, 3, 3, 1, 1, 4, 2, 4]
def baseStart_158404 : Nat := 118140960795 + 158404 * 2 ^ 59
def prefixEnd_158404 : Nat := 4983230072969 + 3 ^ 40 * 158404 * 2
def baseEnd_158404 : Nat := 24099967287378808095265

theorem tailTrace_158404 : CollatzResearch.WordTrace tailWord_158404 prefixEnd_158404 24099967287378808095265 := by
  unfold tailWord_158404
  simp only [CollatzResearch.WordTrace]
  refine ⟨2888734259068418047245133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3851645678757890729660177 2888734259068418047245133)
  ·
    refine ⟨1083275347150656767716925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2888734259068418047245133 1083275347150656767716925)
    ·
      refine ⟨406228255181496287893847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1083275347150656767716925 406228255181496287893847)
      ·
        refine ⟨609342382772244431840771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406228255181496287893847 609342382772244431840771)
        ·
          refine ⟨914013574158366647761157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609342382772244431840771 914013574158366647761157)
          ·
            refine ⟨171377545154693746455217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 914013574158366647761157 171377545154693746455217)
            ·
              refine ⟨128533158866020309841413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171377545154693746455217 128533158866020309841413)
              ·
                refine ⟨24099967287378808095265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128533158866020309841413 24099967287378808095265)
                ·
                  rfl

theorem cell20_158404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 4].length) (baseStart_158404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158404 prefixEnd_158404 := by exact prefixLift 158404
  have htrace : WordTrace (prefixWord ++ tailWord_158404) baseStart_158404 baseEnd_158404 := by
    simpa [prefixWord, tailWord_158404, baseEnd_158404] using wordTrace_append hprefix tailTrace_158404
  have hstable : (prefixWord ++ tailWord_158404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158404).length < 2 ^ (prefixWord ++ tailWord_158404).sum := by decide
  have hdescent : baseEnd_158404 < baseStart_158404 := by decide
  rcases family_descends (prefixWord ++ tailWord_158404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158408 : List Nat := [2, 1, 3, 1, 2, 4, 1, 6]
def baseStart_158408 : Nat := 118140960795 + 158408 * 2 ^ 59
def prefixEnd_158408 : Nat := 4983230072969 + 3 ^ 40 * 158408 * 2
def baseEnd_158408 : Nat := 24100575857043396050815

theorem tailTrace_158408 : CollatzResearch.WordTrace tailWord_158408 prefixEnd_158408 24100575857043396050815 := by
  unfold tailWord_158408
  simp only [CollatzResearch.WordTrace]
  refine ⟨2888807205061172388817939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3851742940081563185090585 2888807205061172388817939)
  ·
    refine ⟨4333210807591758583226909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2888807205061172388817939 4333210807591758583226909)
    ·
      refine ⟨1624954052846909468710091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4333210807591758583226909 1624954052846909468710091)
      ·
        refine ⟨2437431079270364203065137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1624954052846909468710091 2437431079270364203065137)
        ·
          refine ⟨1828073309452773152298853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2437431079270364203065137 1828073309452773152298853)
          ·
            refine ⟨342763745522394966056035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1828073309452773152298853 342763745522394966056035)
            ·
              refine ⟨514145618283592449084053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342763745522394966056035 514145618283592449084053)
              ·
                refine ⟨24100575857043396050815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 514145618283592449084053 24100575857043396050815)
                ·
                  rfl

theorem cell20_158408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_158408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158408 prefixEnd_158408 := by exact prefixLift 158408
  have htrace : WordTrace (prefixWord ++ tailWord_158408) baseStart_158408 baseEnd_158408 := by
    simpa [prefixWord, tailWord_158408, baseEnd_158408] using wordTrace_append hprefix tailTrace_158408
  have hstable : (prefixWord ++ tailWord_158408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158408).length < 2 ^ (prefixWord ++ tailWord_158408).sum := by decide
  have hdescent : baseEnd_158408 < baseStart_158408 := by decide
  rcases family_descends (prefixWord ++ tailWord_158408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158446 : List Nat := [4, 1, 2, 1, 1, 3, 1, 7]
def baseStart_158446 : Nat := 118140960795 + 158446 * 2 ^ 59
def prefixEnd_158446 : Nat := 4983230072969 + 3 ^ 40 * 158446 * 2
def baseEnd_158446 : Nat := 24106357268856981628541

theorem tailTrace_158446 : CollatzResearch.WordTrace tailWord_158446 prefixEnd_158446 24106357268856981628541 := by
  unfold tailWord_158446
  simp only [CollatzResearch.WordTrace]
  refine ⟨722375047998084658439899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3852666922656451511679461 722375047998084658439899)
  ·
    refine ⟨1083562571997126987659849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 722375047998084658439899 1083562571997126987659849)
    ·
      refine ⟨812671928997845240744887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1083562571997126987659849 812671928997845240744887)
      ·
        refine ⟨1219007893496767861117331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 812671928997845240744887 1219007893496767861117331)
        ·
          refine ⟨1828511840245151791675997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1219007893496767861117331 1828511840245151791675997)
          ·
            refine ⟨685691940091931921878499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1828511840245151791675997 685691940091931921878499)
            ·
              refine ⟨1028537910137897882817749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685691940091931921878499 1028537910137897882817749)
              ·
                refine ⟨24106357268856981628541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1028537910137897882817749 24106357268856981628541)
                ·
                  rfl

theorem cell20_158446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_158446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158446 prefixEnd_158446 := by exact prefixLift 158446
  have htrace : WordTrace (prefixWord ++ tailWord_158446) baseStart_158446 baseEnd_158446 := by
    simpa [prefixWord, tailWord_158446, baseEnd_158446] using wordTrace_append hprefix tailTrace_158446
  have hstable : (prefixWord ++ tailWord_158446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158446).length < 2 ^ (prefixWord ++ tailWord_158446).sum := by decide
  have hdescent : baseEnd_158446 < baseStart_158446 := by decide
  rcases family_descends (prefixWord ++ tailWord_158446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158487 : List Nat := [1, 1, 3, 4, 3, 1, 2, 2, 3]
def baseStart_158487 : Nat := 118140960795 + 158487 * 2 ^ 59
def prefixEnd_158487 : Nat := 4983230072969 + 3 ^ 40 * 158487 * 2
def baseEnd_158487 : Nat := 72337785323757024518789

theorem tailTrace_158487 : CollatzResearch.WordTrace tailWord_158487 prefixEnd_158487 72337785323757024518789 := by
  unfold tailWord_158487
  simp only [CollatzResearch.WordTrace]
  refine ⟨5780495776836141269761715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3853663851224094179841143 5780495776836141269761715)
  ·
    refine ⟨8670743665254211904642573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5780495776836141269761715 8670743665254211904642573)
    ·
      refine ⟨3251528874470329464240965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8670743665254211904642573 3251528874470329464240965)
      ·
        refine ⟨609661663963186774545181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3251528874470329464240965 609661663963186774545181)
        ·
          refine ⟨228623123986195040454443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 609661663963186774545181 228623123986195040454443)
          ·
            refine ⟨342934685979292560681665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228623123986195040454443 342934685979292560681665)
            ·
              refine ⟨257201014484469420511249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342934685979292560681665 257201014484469420511249)
              ·
                refine ⟨192900760863352065383437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 257201014484469420511249 192900760863352065383437)
                ·
                  refine ⟨72337785323757024518789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 192900760863352065383437 72337785323757024518789)
                  ·
                    rfl

theorem cell20_158487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 3].length) (baseStart_158487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158487 prefixEnd_158487 := by exact prefixLift 158487
  have htrace : WordTrace (prefixWord ++ tailWord_158487) baseStart_158487 baseEnd_158487 := by
    simpa [prefixWord, tailWord_158487, baseEnd_158487] using wordTrace_append hprefix tailTrace_158487
  have hstable : (prefixWord ++ tailWord_158487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158487).length < 2 ^ (prefixWord ++ tailWord_158487).sum := by decide
  have hdescent : baseEnd_158487 < baseStart_158487 := by decide
  rcases family_descends (prefixWord ++ tailWord_158487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158515 : List Nat := [1, 1, 1, 2, 6, 2, 1, 2, 4]
def baseStart_158515 : Nat := 118140960795 + 158515 * 2 ^ 59
def prefixEnd_158515 : Nat := 4983230072969 + 3 ^ 40 * 158515 * 2
def baseEnd_158515 : Nat := 72350565286713371585341

theorem tailTrace_158515 : CollatzResearch.WordTrace tailWord_158515 prefixEnd_158515 72350565286713371585341 := by
  unfold tailWord_158515
  simp only [CollatzResearch.WordTrace]
  refine ⟨5781517020734702051780999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3854344680489801367853999 5781517020734702051780999)
  ·
    refine ⟨8672275531102053077671499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5781517020734702051780999 8672275531102053077671499)
    ·
      refine ⟨13008413296653079616507249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8672275531102053077671499 13008413296653079616507249)
      ·
        refine ⟨9756309972489809712380437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13008413296653079616507249 9756309972489809712380437)
        ·
          refine ⟨457327029960459830267833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9756309972489809712380437 457327029960459830267833)
          ·
            refine ⟨342995272470344872700875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 457327029960459830267833 342995272470344872700875)
            ·
              refine ⟨514492908705517309051313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342995272470344872700875 514492908705517309051313)
              ·
                refine ⟨385869681529137981788485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 514492908705517309051313 385869681529137981788485)
                ·
                  refine ⟨72350565286713371585341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 385869681529137981788485 72350565286713371585341)
                  ·
                    rfl

theorem cell20_158515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 4].length) (baseStart_158515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158515 prefixEnd_158515 := by exact prefixLift 158515
  have htrace : WordTrace (prefixWord ++ tailWord_158515) baseStart_158515 baseEnd_158515 := by
    simpa [prefixWord, tailWord_158515, baseEnd_158515] using wordTrace_append hprefix tailTrace_158515
  have hstable : (prefixWord ++ tailWord_158515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158515).length < 2 ^ (prefixWord ++ tailWord_158515).sum := by decide
  have hdescent : baseEnd_158515 < baseStart_158515 := by decide
  rcases family_descends (prefixWord ++ tailWord_158515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158536 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 6]
def baseStart_158536 : Nat := 118140960795 + 158536 * 2 ^ 59
def prefixEnd_158536 : Nat := 4983230072969 + 3 ^ 40 * 158536 * 2
def baseEnd_158536 : Nat := 72360150258930631885255

theorem tailTrace_158536 : CollatzResearch.WordTrace tailWord_158536 prefixEnd_158536 72360150258930631885255 := by
  unfold tailWord_158536
  simp only [CollatzResearch.WordTrace]
  refine ⟨2891141476829311319147731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3854855302439081758863641 2891141476829311319147731)
  ·
    refine ⟨4336712215243966978721597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2891141476829311319147731 4336712215243966978721597)
    ·
      refine ⟨1626267080716487617020599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4336712215243966978721597 1626267080716487617020599)
      ·
        refine ⟨2439400621074731425530899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1626267080716487617020599 2439400621074731425530899)
        ·
          refine ⟨3659100931612097138296349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2439400621074731425530899 3659100931612097138296349)
          ·
            refine ⟨1372162849354536426861131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3659100931612097138296349 1372162849354536426861131)
            ·
              refine ⟨2058244274031804640291697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1372162849354536426861131 2058244274031804640291697)
              ·
                refine ⟨1543683205523853480218773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2058244274031804640291697 1543683205523853480218773)
                ·
                  refine ⟨72360150258930631885255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1543683205523853480218773 72360150258930631885255)
                  ·
                    rfl

theorem cell20_158536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_158536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158536 prefixEnd_158536 := by exact prefixLift 158536
  have htrace : WordTrace (prefixWord ++ tailWord_158536) baseStart_158536 baseEnd_158536 := by
    simpa [prefixWord, tailWord_158536, baseEnd_158536] using wordTrace_append hprefix tailTrace_158536
  have hstable : (prefixWord ++ tailWord_158536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158536).length < 2 ^ (prefixWord ++ tailWord_158536).sum := by decide
  have hdescent : baseEnd_158536 < baseStart_158536 := by decide
  rcases family_descends (prefixWord ++ tailWord_158536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158553 : List Nat := [1, 2, 1, 2, 2, 5, 2, 1, 4]
def baseStart_158553 : Nat := 118140960795 + 158553 * 2 ^ 59
def prefixEnd_158553 : Nat := 4983230072969 + 3 ^ 40 * 158553 * 2
def baseEnd_158553 : Nat := 72367909522154128318519

theorem tailTrace_158553 : CollatzResearch.WordTrace tailWord_158553 prefixEnd_158553 72367909522154128318519 := by
  unfold tailWord_158553
  simp only [CollatzResearch.WordTrace]
  refine ⟨5782902994597034541664313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3855268663064689694442875 5782902994597034541664313)
  ·
    refine ⟨4337177245947775906248235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5782902994597034541664313 4337177245947775906248235)
    ·
      refine ⟨6505765868921663859372353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4337177245947775906248235 6505765868921663859372353)
      ·
        refine ⟨4879324401691247894529265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6505765868921663859372353 4879324401691247894529265)
        ·
          refine ⟨3659493301268435920896949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4879324401691247894529265 3659493301268435920896949)
          ·
            refine ⟨343077496993915867584089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3659493301268435920896949 343077496993915867584089)
            ·
              refine ⟨257308122745436900688067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343077496993915867584089 257308122745436900688067)
              ·
                refine ⟨385962184118155351032101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257308122745436900688067 385962184118155351032101)
                ·
                  refine ⟨72367909522154128318519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 385962184118155351032101 72367909522154128318519)
                  ·
                    rfl

theorem cell20_158553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_158553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158553 prefixEnd_158553 := by exact prefixLift 158553
  have htrace : WordTrace (prefixWord ++ tailWord_158553) baseStart_158553 baseEnd_158553 := by
    simpa [prefixWord, tailWord_158553, baseEnd_158553] using wordTrace_append hprefix tailTrace_158553
  have hstable : (prefixWord ++ tailWord_158553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158553).length < 2 ^ (prefixWord ++ tailWord_158553).sum := by decide
  have hdescent : baseEnd_158553 < baseStart_158553 := by decide
  rcases family_descends (prefixWord ++ tailWord_158553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158563 : List Nat := [1, 1, 1, 5, 3, 2, 3, 1, 3]
def baseStart_158563 : Nat := 118140960795 + 158563 * 2 ^ 59
def prefixEnd_158563 : Nat := 4983230072969 + 3 ^ 40 * 158563 * 2
def baseEnd_158563 : Nat := 72372473794638537985145

theorem tailTrace_158563 : CollatzResearch.WordTrace tailWord_158563 prefixEnd_158563 72372473794638537985145 := by
  unfold tailWord_158563
  simp only [CollatzResearch.WordTrace]
  refine ⟨5783267724560806249528343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3855511816373870833018895 5783267724560806249528343)
  ·
    refine ⟨8674901586841209374292515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5783267724560806249528343 8674901586841209374292515)
    ·
      refine ⟨13012352380261814061438773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8674901586841209374292515 13012352380261814061438773)
      ·
        refine ⟨1219908035649545068259885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13012352380261814061438773 1219908035649545068259885)
        ·
          refine ⟨457465513368579400597457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1219908035649545068259885 457465513368579400597457)
          ·
            refine ⟨343099135026434550448093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 457465513368579400597457 343099135026434550448093)
            ·
              refine ⟨128662175634912956418035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 343099135026434550448093 128662175634912956418035)
              ·
                refine ⟨192993263452369434627053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128662175634912956418035 192993263452369434627053)
                ·
                  refine ⟨72372473794638537985145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 192993263452369434627053 72372473794638537985145)
                  ·
                    rfl

theorem cell20_158563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 3].length) (baseStart_158563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158563 prefixEnd_158563 := by exact prefixLift 158563
  have htrace : WordTrace (prefixWord ++ tailWord_158563) baseStart_158563 baseEnd_158563 := by
    simpa [prefixWord, tailWord_158563, baseEnd_158563] using wordTrace_append hprefix tailTrace_158563
  have hstable : (prefixWord ++ tailWord_158563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158563).length < 2 ^ (prefixWord ++ tailWord_158563).sum := by decide
  have hdescent : baseEnd_158563 < baseStart_158563 := by decide
  rcases family_descends (prefixWord ++ tailWord_158563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158577 : List Nat := [1, 2, 2, 2, 1, 6, 2, 4]
def baseStart_158577 : Nat := 118140960795 + 158577 * 2 ^ 59
def prefixEnd_158577 : Nat := 4983230072969 + 3 ^ 40 * 158577 * 2
def baseEnd_158577 : Nat := 24126287925372237172807

theorem tailTrace_158577 : CollatzResearch.WordTrace tailWord_158577 prefixEnd_158577 24126287925372237172807 := by
  unfold tailWord_158577
  simp only [CollatzResearch.WordTrace]
  refine ⟨5783778346510086640537985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3855852231006724427025323 5783778346510086640537985)
  ·
    refine ⟨4337833759882564980403489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5783778346510086640537985 4337833759882564980403489)
    ·
      refine ⟨3253375319911923735302617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4337833759882564980403489 3253375319911923735302617)
      ·
        refine ⟨2440031489933942801476963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3253375319911923735302617 2440031489933942801476963)
        ·
          refine ⟨3660047234900914202215445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2440031489933942801476963 3660047234900914202215445)
          ·
            refine ⟨171564714135980353228849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3660047234900914202215445 171564714135980353228849)
            ·
              refine ⟨128673535601985264921637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171564714135980353228849 128673535601985264921637)
              ·
                refine ⟨24126287925372237172807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128673535601985264921637 24126287925372237172807)
                ·
                  rfl

theorem cell20_158577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 4].length) (baseStart_158577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158577 prefixEnd_158577 := by exact prefixLift 158577
  have htrace : WordTrace (prefixWord ++ tailWord_158577) baseStart_158577 baseEnd_158577 := by
    simpa [prefixWord, tailWord_158577, baseEnd_158577] using wordTrace_append hprefix tailTrace_158577
  have hstable : (prefixWord ++ tailWord_158577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158577).length < 2 ^ (prefixWord ++ tailWord_158577).sum := by decide
  have hdescent : baseEnd_158577 < baseStart_158577 := by decide
  rcases family_descends (prefixWord ++ tailWord_158577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158614 : List Nat := [5, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_158614 : Nat := 118140960795 + 158614 * 2 ^ 59
def prefixEnd_158614 : Nat := 4983230072969 + 3 ^ 40 * 158614 * 2
def baseEnd_158614 : Nat := 72395751584309027284937

theorem tailTrace_158614 : CollatzResearch.WordTrace tailWord_158614 prefixEnd_158614 72395751584309027284937 := by
  unfold tailWord_158614
  simp only [CollatzResearch.WordTrace]
  refine ⟨361570490461002622477181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3856751898250694639756597 361570490461002622477181)
  ·
    refine ⟨135588933922875983428943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 361570490461002622477181 135588933922875983428943)
    ·
      refine ⟨203383400884313975143415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135588933922875983428943 203383400884313975143415)
      ·
        refine ⟨305075101326470962715123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203383400884313975143415 305075101326470962715123)
        ·
          refine ⟨457612651989706444072685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305075101326470962715123 457612651989706444072685)
          ·
            refine ⟨171604744496139916527257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 457612651989706444072685 171604744496139916527257)
            ·
              refine ⟨128703558372104937395443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171604744496139916527257 128703558372104937395443)
              ·
                refine ⟨193055337558157406093165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128703558372104937395443 193055337558157406093165)
                ·
                  refine ⟨72395751584309027284937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 193055337558157406093165 72395751584309027284937)
                  ·
                    rfl

theorem cell20_158614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_158614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158614 prefixEnd_158614 := by exact prefixLift 158614
  have htrace : WordTrace (prefixWord ++ tailWord_158614) baseStart_158614 baseEnd_158614 := by
    simpa [prefixWord, tailWord_158614, baseEnd_158614] using wordTrace_append hprefix tailTrace_158614
  have hstable : (prefixWord ++ tailWord_158614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158614).length < 2 ^ (prefixWord ++ tailWord_158614).sum := by decide
  have hdescent : baseEnd_158614 < baseStart_158614 := by decide
  rcases family_descends (prefixWord ++ tailWord_158614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158618 : List Nat := [3, 1, 1, 4, 3, 2, 2, 1, 3]
def baseStart_158618 : Nat := 118140960795 + 158618 * 2 ^ 59
def prefixEnd_158618 : Nat := 4983230072969 + 3 ^ 40 * 158618 * 2
def baseEnd_158618 : Nat := 72397577293302791151587

theorem tailTrace_158618 : CollatzResearch.WordTrace tailWord_158618 prefixEnd_158618 72397577293302791151587 := by
  unfold tailWord_158618
  simp only [CollatzResearch.WordTrace]
  refine ⟨1446318434840387660695127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3856849159574367095187005 1446318434840387660695127)
  ·
    refine ⟨2169477652260581491042691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1446318434840387660695127 2169477652260581491042691)
    ·
      refine ⟨3254216478390872236564037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2169477652260581491042691 3254216478390872236564037)
      ·
        refine ⟨610165589698288544355757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3254216478390872236564037 610165589698288544355757)
        ·
          refine ⟨228812096136858204133409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 610165589698288544355757 228812096136858204133409)
          ·
            refine ⟨171609072102643653100057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228812096136858204133409 171609072102643653100057)
            ·
              refine ⟨128706804076982739825043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171609072102643653100057 128706804076982739825043)
              ·
                refine ⟨193060206115474109737565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128706804076982739825043 193060206115474109737565)
                ·
                  refine ⟨72397577293302791151587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 193060206115474109737565 72397577293302791151587)
                  ·
                    rfl

theorem cell20_158618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_158618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158618 prefixEnd_158618 := by exact prefixLift 158618
  have htrace : WordTrace (prefixWord ++ tailWord_158618) baseStart_158618 baseEnd_158618 := by
    simpa [prefixWord, tailWord_158618, baseEnd_158618] using wordTrace_append hprefix tailTrace_158618
  have hstable : (prefixWord ++ tailWord_158618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158618).length < 2 ^ (prefixWord ++ tailWord_158618).sum := by decide
  have hdescent : baseEnd_158618 < baseStart_158618 := by decide
  rcases family_descends (prefixWord ++ tailWord_158618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158743 : List Nat := [1, 1, 3, 5, 1, 1, 2, 2, 4]
def baseStart_158743 : Nat := 118140960795 + 158743 * 2 ^ 59
def prefixEnd_158743 : Nat := 4983230072969 + 3 ^ 40 * 158743 * 2
def baseEnd_158743 : Nat := 72454630699357911984409

theorem tailTrace_158743 : CollatzResearch.WordTrace tailWord_158743 prefixEnd_158743 72454630699357911984409 := by
  unfold tailWord_158743
  simp only [CollatzResearch.WordTrace]
  refine ⟨5789832863908696991080883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3859888575939131327387255 5789832863908696991080883)
  ·
    refine ⟨8684749295863045486621325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5789832863908696991080883 8684749295863045486621325)
    ·
      refine ⟨3256780985948642057482997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8684749295863045486621325 3256780985948642057482997)
      ·
        refine ⟨305323217432685192889031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3256780985948642057482997 305323217432685192889031)
        ·
          refine ⟨457984826149027789333547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305323217432685192889031 457984826149027789333547)
          ·
            refine ⟨686977239223541684000321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457984826149027789333547 686977239223541684000321)
            ·
              refine ⟨515232929417656263000241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 686977239223541684000321 515232929417656263000241)
              ·
                refine ⟨386424697063242197250181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 515232929417656263000241 386424697063242197250181)
                ·
                  refine ⟨72454630699357911984409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 386424697063242197250181 72454630699357911984409)
                  ·
                    rfl

theorem cell20_158743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 4].length) (baseStart_158743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158743 prefixEnd_158743 := by exact prefixLift 158743
  have htrace : WordTrace (prefixWord ++ tailWord_158743) baseStart_158743 baseEnd_158743 := by
    simpa [prefixWord, tailWord_158743, baseEnd_158743] using wordTrace_append hprefix tailTrace_158743
  have hstable : (prefixWord ++ tailWord_158743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158743).length < 2 ^ (prefixWord ++ tailWord_158743).sum := by decide
  have hdescent : baseEnd_158743 < baseStart_158743 := by decide
  rcases family_descends (prefixWord ++ tailWord_158743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158774 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_158774 : Nat := 118140960795 + 158774 * 2 ^ 59
def prefixEnd_158774 : Nat := 4983230072969 + 3 ^ 40 * 158774 * 2
def baseEnd_158774 : Nat := 72468779944059581950949

theorem tailTrace_158774 : CollatzResearch.WordTrace tailWord_158774 prefixEnd_158774 72468779944059581950949 := by
  unfold tailWord_158774
  simp only [CollatzResearch.WordTrace]
  refine ⟨361935220424774330341211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3860642351197592856972917 361935220424774330341211)
  ·
    refine ⟨542902830637161495511817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 361935220424774330341211 542902830637161495511817)
    ·
      refine ⟨407177122977871121633863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 542902830637161495511817 407177122977871121633863)
      ·
        refine ⟨610765684466806682450795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407177122977871121633863 610765684466806682450795)
        ·
          refine ⟨916148526700210023676193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610765684466806682450795 916148526700210023676193)
          ·
            refine ⟨687111395025157517757145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 916148526700210023676193 687111395025157517757145)
            ·
              refine ⟨515333546268868138317859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 687111395025157517757145 515333546268868138317859)
              ·
                refine ⟨773000319403302207476789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515333546268868138317859 773000319403302207476789)
                ·
                  refine ⟨72468779944059581950949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 773000319403302207476789 72468779944059581950949)
                  ·
                    rfl

theorem cell20_158774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_158774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158774 prefixEnd_158774 := by exact prefixLift 158774
  have htrace : WordTrace (prefixWord ++ tailWord_158774) baseStart_158774 baseEnd_158774 := by
    simpa [prefixWord, tailWord_158774, baseEnd_158774] using wordTrace_append hprefix tailTrace_158774
  have hstable : (prefixWord ++ tailWord_158774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158774).length < 2 ^ (prefixWord ++ tailWord_158774).sum := by decide
  have hdescent : baseEnd_158774 < baseStart_158774 := by decide
  rcases family_descends (prefixWord ++ tailWord_158774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158777 : List Nat := [1, 2, 1, 5, 2, 2, 3, 2, 2]
def baseStart_158777 : Nat := 118140960795 + 158777 * 2 ^ 59
def prefixEnd_158777 : Nat := 4983230072969 + 3 ^ 40 * 158777 * 2
def baseEnd_158777 : Nat := 72470149225804904850937

theorem tailTrace_158777 : CollatzResearch.WordTrace tailWord_158777 prefixEnd_158777 72470149225804904850937 := by
  unfold tailWord_158777
  simp only [CollatzResearch.WordTrace]
  refine ⟨5791072945785520797818585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3860715297190347198545723 5791072945785520797818585)
  ·
    refine ⟨4343304709339140598363939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5791072945785520797818585 4343304709339140598363939)
    ·
      refine ⟨6514957064008710897545909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4343304709339140598363939 6514957064008710897545909)
      ·
        refine ⟨610777224750816646644929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6514957064008710897545909 610777224750816646644929)
        ·
          refine ⟨458082918563112484983697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 610777224750816646644929 458082918563112484983697)
          ·
            refine ⟨343562188922334363737773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 458082918563112484983697 343562188922334363737773)
            ·
              refine ⟨128835820845875386401665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 343562188922334363737773 128835820845875386401665)
              ·
                refine ⟨96626865634406539801249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128835820845875386401665 96626865634406539801249)
                ·
                  refine ⟨72470149225804904850937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96626865634406539801249 72470149225804904850937)
                  ·
                    rfl

theorem cell20_158777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 2].length) (baseStart_158777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158777 prefixEnd_158777 := by exact prefixLift 158777
  have htrace : WordTrace (prefixWord ++ tailWord_158777) baseStart_158777 baseEnd_158777 := by
    simpa [prefixWord, tailWord_158777, baseEnd_158777] using wordTrace_append hprefix tailTrace_158777
  have hstable : (prefixWord ++ tailWord_158777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158777).length < 2 ^ (prefixWord ++ tailWord_158777).sum := by decide
  have hdescent : baseEnd_158777 < baseStart_158777 := by decide
  rcases family_descends (prefixWord ++ tailWord_158777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158781 : List Nat := [1, 4, 1, 3, 1, 2, 3, 1, 4]
def baseStart_158781 : Nat := 118140960795 + 158781 * 2 ^ 59
def prefixEnd_158781 : Nat := 4983230072969 + 3 ^ 40 * 158781 * 2
def baseEnd_158781 : Nat := 72471974934798668717587

theorem tailTrace_158781 : CollatzResearch.WordTrace tailWord_158781 prefixEnd_158781 72471974934798668717587 := by
  unfold tailWord_158781
  simp only [CollatzResearch.WordTrace]
  refine ⟨5791218837771029480964197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3860812558514019653976131 5791218837771029480964197)
  ·
    refine ⟨1085853532082068027680787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5791218837771029480964197 1085853532082068027680787)
    ·
      refine ⟨1628780298123102041521181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1085853532082068027680787 1628780298123102041521181)
      ·
        refine ⟨610792611796163265570443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1628780298123102041521181 610792611796163265570443)
        ·
          refine ⟨916188917694244898355665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610792611796163265570443 916188917694244898355665)
          ·
            refine ⟨687141688270683673766749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 916188917694244898355665 687141688270683673766749)
            ·
              refine ⟨257678133101506377662531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 687141688270683673766749 257678133101506377662531)
              ·
                refine ⟨386517199652259566493797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257678133101506377662531 386517199652259566493797)
                ·
                  refine ⟨72471974934798668717587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 386517199652259566493797 72471974934798668717587)
                  ·
                    rfl

theorem cell20_158781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_158781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158781 prefixEnd_158781 := by exact prefixLift 158781
  have htrace : WordTrace (prefixWord ++ tailWord_158781) baseStart_158781 baseEnd_158781 := by
    simpa [prefixWord, tailWord_158781, baseEnd_158781] using wordTrace_append hprefix tailTrace_158781
  have hstable : (prefixWord ++ tailWord_158781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158781).length < 2 ^ (prefixWord ++ tailWord_158781).sum := by decide
  have hdescent : baseEnd_158781 < baseStart_158781 := by decide
  rcases family_descends (prefixWord ++ tailWord_158781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
