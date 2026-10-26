import V185TrunkScan20Chunk003

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_23795 : List Nat := [1, 1, 1, 2, 2, 6, 2, 1, 4]
def baseStart_23795 : Nat := 118140960795 + 23795 * 2 ^ 59
def prefixEnd_23795 : Nat := 4983230072969 + 3 ^ 40 * 23795 * 2
def baseEnd_23795 : Nat := 10860686376746342802733

theorem tailTrace_23795 : CollatzResearch.WordTrace tailWord_23795 prefixEnd_23795 10860686376746342802733 := by
  unfold tailWord_23795
  simp only [CollatzResearch.WordTrace]
  refine ⟨867874948802253707568839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 578583299201502471712559 867874948802253707568839)
  ·
    refine ⟨1301812423203380561353259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 867874948802253707568839 1301812423203380561353259)
    ·
      refine ⟨1952718634805070842029889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1301812423203380561353259 1952718634805070842029889)
      ·
        refine ⟨1464538976103803131522417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1952718634805070842029889 1464538976103803131522417)
        ·
          refine ⟨1098404232077852348641813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1464538976103803131522417 1098404232077852348641813)
          ·
            refine ⟨51487698378649328842585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1098404232077852348641813 51487698378649328842585)
            ·
              refine ⟨38615773783986996631939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51487698378649328842585 38615773783986996631939)
              ·
                refine ⟨57923660675980494947909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38615773783986996631939 57923660675980494947909)
                ·
                  refine ⟨10860686376746342802733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57923660675980494947909 10860686376746342802733)
                  ·
                    rfl

theorem cell20_23795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 4].length) (baseStart_23795 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23795 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23795 prefixEnd_23795 := by exact prefixLift 23795
  have htrace : WordTrace (prefixWord ++ tailWord_23795) baseStart_23795 baseEnd_23795 := by
    simpa [prefixWord, tailWord_23795, baseEnd_23795] using wordTrace_append hprefix tailTrace_23795
  have hstable : (prefixWord ++ tailWord_23795).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23795).length < 2 ^ (prefixWord ++ tailWord_23795).sum := by decide
  have hdescent : baseEnd_23795 < baseStart_23795 := by decide
  rcases family_descends (prefixWord ++ tailWord_23795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23819 : List Nat := [1, 1, 1, 1, 5, 5, 2, 4]
def baseStart_23819 : Nat := 118140960795 + 23819 * 2 ^ 59
def prefixEnd_23819 : Nat := 4983230072969 + 3 ^ 40 * 23819 * 2
def baseEnd_23819 : Nat := 3623880210236308667545

theorem tailTrace_23819 : CollatzResearch.WordTrace tailWord_23819 prefixEnd_23819 3623880210236308667545 := by
  unfold tailWord_23819
  simp only [CollatzResearch.WordTrace]
  refine ⟨868750300715305806442511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 579166867143537204295007 868750300715305806442511)
  ·
    refine ⟨1303125451072958709663767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 868750300715305806442511 1303125451072958709663767)
    ·
      refine ⟨1954688176609438064495651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1303125451072958709663767 1954688176609438064495651)
      ·
        refine ⟨2932032264914157096743477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1954688176609438064495651 2932032264914157096743477)
        ·
          refine ⟨274878024835702227819701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2932032264914157096743477 274878024835702227819701)
          ·
            refine ⟨25769814828347083858097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 274878024835702227819701 25769814828347083858097)
            ·
              refine ⟨19327361121260312893573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25769814828347083858097 19327361121260312893573)
              ·
                refine ⟨3623880210236308667545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19327361121260312893573 3623880210236308667545)
                ·
                  rfl

theorem cell20_23819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 4].length) (baseStart_23819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23819 prefixEnd_23819 := by exact prefixLift 23819
  have htrace : WordTrace (prefixWord ++ tailWord_23819) baseStart_23819 baseEnd_23819 := by
    simpa [prefixWord, tailWord_23819, baseEnd_23819] using wordTrace_append hprefix tailTrace_23819
  have hstable : (prefixWord ++ tailWord_23819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23819).length < 2 ^ (prefixWord ++ tailWord_23819).sum := by decide
  have hdescent : baseEnd_23819 < baseStart_23819 := by decide
  rcases family_descends (prefixWord ++ tailWord_23819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23850 : List Nat := [3, 1, 4, 2, 1, 1, 3, 1, 4]
def baseStart_23850 : Nat := 118140960795 + 23850 * 2 ^ 59
def prefixEnd_23850 : Nat := 4983230072969 + 3 ^ 40 * 23850 * 2
def baseEnd_23850 : Nat := 10885789875410595969175

theorem tailTrace_23850 : CollatzResearch.WordTrace tailWord_23850 prefixEnd_23850 10885789875410595969175 := by
  unfold tailWord_23850
  simp only [CollatzResearch.WordTrace]
  refine ⟨217470240900749525205251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 579920642401998733880669 217470240900749525205251)
  ·
    refine ⟨326205361351124287807877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217470240900749525205251 326205361351124287807877)
    ·
      refine ⟨61163505253335803963977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 326205361351124287807877 61163505253335803963977)
      ·
        refine ⟨45872628940001852972983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61163505253335803963977 45872628940001852972983)
        ·
          refine ⟨68808943410002779459475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45872628940001852972983 68808943410002779459475)
          ·
            refine ⟨103213415115004169189213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68808943410002779459475 103213415115004169189213)
            ·
              refine ⟨38705030668126563445955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103213415115004169189213 38705030668126563445955)
              ·
                refine ⟨58057546002189845168933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38705030668126563445955 58057546002189845168933)
                ·
                  refine ⟨10885789875410595969175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58057546002189845168933 10885789875410595969175)
                  ·
                    rfl

theorem cell20_23850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_23850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23850 prefixEnd_23850 := by exact prefixLift 23850
  have htrace : WordTrace (prefixWord ++ tailWord_23850) baseStart_23850 baseEnd_23850 := by
    simpa [prefixWord, tailWord_23850, baseEnd_23850] using wordTrace_append hprefix tailTrace_23850
  have hstable : (prefixWord ++ tailWord_23850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23850).length < 2 ^ (prefixWord ++ tailWord_23850).sum := by decide
  have hdescent : baseEnd_23850 < baseStart_23850 := by decide
  rcases family_descends (prefixWord ++ tailWord_23850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23894 : List Nat := [5, 2, 3, 1, 1, 1, 2, 2, 3]
def baseStart_23894 : Nat := 118140960795 + 23894 * 2 ^ 59
def prefixEnd_23894 : Nat := 4983230072969 + 3 ^ 40 * 23894 * 2
def baseEnd_23894 : Nat := 10905872674341998502329

theorem tailTrace_23894 : CollatzResearch.WordTrace tailWord_23894 prefixEnd_23894 10905872674341998502329 := by
  unfold tailWord_23894
  simp only [CollatzResearch.WordTrace]
  refine ⟨54467860965224600963921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 580990516962395743615157 54467860965224600963921)
  ·
    refine ⟨40850895723918450722941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54467860965224600963921 40850895723918450722941)
    ·
      refine ⟨15319085896469419021103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40850895723918450722941 15319085896469419021103)
      ·
        refine ⟨22978628844704128531655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15319085896469419021103 22978628844704128531655)
        ·
          refine ⟨34467943267056192797483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22978628844704128531655 34467943267056192797483)
          ·
            refine ⟨51701914900584289196225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34467943267056192797483 51701914900584289196225)
            ·
              refine ⟨38776436175438216897169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51701914900584289196225 38776436175438216897169)
              ·
                refine ⟨29082327131578662672877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38776436175438216897169 29082327131578662672877)
                ·
                  refine ⟨10905872674341998502329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29082327131578662672877 10905872674341998502329)
                  ·
                    rfl

theorem cell20_23894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_23894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23894 prefixEnd_23894 := by exact prefixLift 23894
  have htrace : WordTrace (prefixWord ++ tailWord_23894) baseStart_23894 baseEnd_23894 := by
    simpa [prefixWord, tailWord_23894, baseEnd_23894] using wordTrace_append hprefix tailTrace_23894
  have hstable : (prefixWord ++ tailWord_23894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23894).length < 2 ^ (prefixWord ++ tailWord_23894).sum := by decide
  have hdescent : baseEnd_23894 < baseStart_23894 := by decide
  rcases family_descends (prefixWord ++ tailWord_23894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23901 : List Nat := [1, 4, 5, 1, 1, 1, 1, 4, 2]
def baseStart_23901 : Nat := 118140960795 + 23901 * 2 ^ 59
def prefixEnd_23901 : Nat := 4983230072969 + 3 ^ 40 * 23901 * 2
def baseEnd_23901 : Nat := 10909067665081085268967

theorem tailTrace_23901 : CollatzResearch.WordTrace tailWord_23901 prefixEnd_23901 10909067665081085268967 := by
  unfold tailWord_23901
  simp only [CollatzResearch.WordTrace]
  refine ⟨871741086418233810927557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 581160724278822540618371 871741086418233810927557)
  ·
    refine ⟨163451453703418839548917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 871741086418233810927557 163451453703418839548917)
    ·
      refine ⟨15323573784695516207711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 163451453703418839548917 15323573784695516207711)
      ·
        refine ⟨22985360677043274311567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15323573784695516207711 22985360677043274311567)
        ·
          refine ⟨34478041015564911467351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22985360677043274311567 34478041015564911467351)
          ·
            refine ⟨51717061523347367201027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34478041015564911467351 51717061523347367201027)
            ·
              refine ⟨77575592285021050801541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51717061523347367201027 77575592285021050801541)
              ·
                refine ⟨14545423553441447025289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77575592285021050801541 14545423553441447025289)
                ·
                  refine ⟨10909067665081085268967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14545423553441447025289 10909067665081085268967)
                  ·
                    rfl

theorem cell20_23901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_23901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23901 prefixEnd_23901 := by exact prefixLift 23901
  have htrace : WordTrace (prefixWord ++ tailWord_23901) baseStart_23901 baseEnd_23901 := by
    simpa [prefixWord, tailWord_23901, baseEnd_23901] using wordTrace_append hprefix tailTrace_23901
  have hstable : (prefixWord ++ tailWord_23901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23901).length < 2 ^ (prefixWord ++ tailWord_23901).sum := by decide
  have hdescent : baseEnd_23901 < baseStart_23901 := by decide
  rcases family_descends (prefixWord ++ tailWord_23901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23912 : List Nat := [2, 1, 4, 2, 4, 1, 1, 5]
def baseStart_23912 : Nat := 118140960795 + 23912 * 2 ^ 59
def prefixEnd_23912 : Nat := 4983230072969 + 3 ^ 40 * 23912 * 2
def baseEnd_23912 : Nat := 3638029454937978634085

theorem tailTrace_23912 : CollatzResearch.WordTrace tailWord_23912 prefixEnd_23912 3638029454937978634085 := by
  unfold tailWord_23912
  simp only [CollatzResearch.WordTrace]
  refine ⟨436071144689191344788995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 581428192918921793051993 436071144689191344788995)
  ·
    refine ⟨654106717033787017183493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 436071144689191344788995 654106717033787017183493)
    ·
      refine ⟨122645009443835065721905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 654106717033787017183493 122645009443835065721905)
      ·
        refine ⟨91983757082876299291429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122645009443835065721905 91983757082876299291429)
        ·
          refine ⟨17246954453039306117143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91983757082876299291429 17246954453039306117143)
          ·
            refine ⟨25870431679558959175715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17246954453039306117143 25870431679558959175715)
            ·
              refine ⟨38805647519338438763573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25870431679558959175715 38805647519338438763573)
              ·
                refine ⟨3638029454937978634085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38805647519338438763573 3638029454937978634085)
                ·
                  rfl

theorem cell20_23912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 5].length) (baseStart_23912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23912 prefixEnd_23912 := by exact prefixLift 23912
  have htrace : WordTrace (prefixWord ++ tailWord_23912) baseStart_23912 baseEnd_23912 := by
    simpa [prefixWord, tailWord_23912, baseEnd_23912] using wordTrace_append hprefix tailTrace_23912
  have hstable : (prefixWord ++ tailWord_23912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23912).length < 2 ^ (prefixWord ++ tailWord_23912).sum := by decide
  have hdescent : baseEnd_23912 < baseStart_23912 := by decide
  rcases family_descends (prefixWord ++ tailWord_23912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23916 : List Nat := [2, 2, 1, 1, 5, 1, 3, 5]
def baseStart_23916 : Nat := 118140960795 + 23916 * 2 ^ 59
def prefixEnd_23916 : Nat := 4983230072969 + 3 ^ 40 * 23916 * 2
def baseEnd_23916 : Nat := 3638638024602566589635

theorem tailTrace_23916 : CollatzResearch.WordTrace tailWord_23916 prefixEnd_23916 3638638024602566589635 := by
  unfold tailWord_23916
  simp only [CollatzResearch.WordTrace]
  refine ⟨436144090681945686361801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 581525454242594248482401 436144090681945686361801)
  ·
    refine ⟨327108068011459264771351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 436144090681945686361801 327108068011459264771351)
    ·
      refine ⟨490662102017188897157027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327108068011459264771351 490662102017188897157027)
      ·
        refine ⟨735993153025783345735541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490662102017188897157027 735993153025783345735541)
        ·
          refine ⟨68999358096167188662707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 735993153025783345735541 68999358096167188662707)
          ·
            refine ⟨103499037144250782994061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68999358096167188662707 103499037144250782994061)
            ·
              refine ⟨38812138929094043622773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103499037144250782994061 38812138929094043622773)
              ·
                refine ⟨3638638024602566589635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38812138929094043622773 3638638024602566589635)
                ·
                  rfl

theorem cell20_23916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_23916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23916 prefixEnd_23916 := by exact prefixLift 23916
  have htrace : WordTrace (prefixWord ++ tailWord_23916) baseStart_23916 baseEnd_23916 := by
    simpa [prefixWord, tailWord_23916, baseEnd_23916] using wordTrace_append hprefix tailTrace_23916
  have hstable : (prefixWord ++ tailWord_23916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23916).length < 2 ^ (prefixWord ++ tailWord_23916).sum := by decide
  have hdescent : baseEnd_23916 < baseStart_23916 := by decide
  rcases family_descends (prefixWord ++ tailWord_23916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23930 : List Nat := [3, 1, 1, 1, 1, 1, 2, 6, 4]
def baseStart_23930 : Nat := 118140960795 + 23930 * 2 ^ 59
def prefixEnd_23930 : Nat := 4983230072969 + 3 ^ 40 * 23930 * 2
def baseEnd_23930 : Nat := 10922304055285873302181

theorem tailTrace_23930 : CollatzResearch.WordTrace tailWord_23930 prefixEnd_23930 10922304055285873302181 := by
  unfold tailWord_23930
  simp only [CollatzResearch.WordTrace]
  refine ⟨218199700828292940933311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 581865868875447842488829 218199700828292940933311)
  ·
    refine ⟨327299551242439411399967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218199700828292940933311 327299551242439411399967)
    ·
      refine ⟨490949326863659117099951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327299551242439411399967 490949326863659117099951)
      ·
        refine ⟨736423990295488675649927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490949326863659117099951 736423990295488675649927)
        ·
          refine ⟨1104635985443233013474891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 736423990295488675649927 1104635985443233013474891)
          ·
            refine ⟨1656953978164849520212337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104635985443233013474891 1656953978164849520212337)
            ·
              refine ⟨1242715483623637140159253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1656953978164849520212337 1242715483623637140159253)
              ·
                refine ⟨58252288294857990944965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1242715483623637140159253 58252288294857990944965)
                ·
                  refine ⟨10922304055285873302181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58252288294857990944965 10922304055285873302181)
                  ·
                    rfl

theorem cell20_23930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_23930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23930 prefixEnd_23930 := by exact prefixLift 23930
  have htrace : WordTrace (prefixWord ++ tailWord_23930) baseStart_23930 baseEnd_23930 := by
    simpa [prefixWord, tailWord_23930, baseEnd_23930] using wordTrace_append hprefix tailTrace_23930
  have hstable : (prefixWord ++ tailWord_23930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23930).length < 2 ^ (prefixWord ++ tailWord_23930).sum := by decide
  have hdescent : baseEnd_23930 < baseStart_23930 := by decide
  rcases family_descends (prefixWord ++ tailWord_23930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23961 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 5]
def baseStart_23961 : Nat := 118140960795 + 23961 * 2 ^ 59
def prefixEnd_23961 : Nat := 4983230072969 + 3 ^ 40 * 23961 * 2
def baseEnd_23961 : Nat := 10936453299987543268721

theorem tailTrace_23961 : CollatzResearch.WordTrace tailWord_23961 prefixEnd_23961 10936453299987543268721 := by
  unfold tailWord_23961
  simp only [CollatzResearch.WordTrace]
  refine ⟨873929466200864058111737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 582619644133909372074491 873929466200864058111737)
  ·
    refine ⟨655447099650648043583803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 873929466200864058111737 655447099650648043583803)
    ·
      refine ⟨983170649475972065375705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 655447099650648043583803 983170649475972065375705)
      ·
        refine ⟨737377987106979049031779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 983170649475972065375705 737377987106979049031779)
        ·
          refine ⟨1106066980660468573547669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 737377987106979049031779 1106066980660468573547669)
          ·
            refine ⟨51846889718459464385047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1106066980660468573547669 51846889718459464385047)
            ·
              refine ⟨77770334577689196577571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51846889718459464385047 77770334577689196577571)
              ·
                refine ⟨116655501866533794866357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77770334577689196577571 116655501866533794866357)
                ·
                  refine ⟨10936453299987543268721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116655501866533794866357 10936453299987543268721)
                  ·
                    rfl

theorem cell20_23961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_23961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23961 prefixEnd_23961 := by exact prefixLift 23961
  have htrace : WordTrace (prefixWord ++ tailWord_23961) baseStart_23961 baseEnd_23961 := by
    simpa [prefixWord, tailWord_23961, baseEnd_23961] using wordTrace_append hprefix tailTrace_23961
  have hstable : (prefixWord ++ tailWord_23961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23961).length < 2 ^ (prefixWord ++ tailWord_23961).sum := by decide
  have hdescent : baseEnd_23961 < baseStart_23961 := by decide
  rcases family_descends (prefixWord ++ tailWord_23961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23992 : List Nat := [2, 1, 2, 1, 2, 2, 6, 4]
def baseStart_23992 : Nat := 118140960795 + 23992 * 2 ^ 59
def prefixEnd_23992 : Nat := 4983230072969 + 3 ^ 40 * 23992 * 2
def baseEnd_23992 : Nat := 3650200848229737745087

theorem tailTrace_23992 : CollatzResearch.WordTrace tailWord_23992 prefixEnd_23992 3650200848229737745087 := by
  unfold tailWord_23992
  simp only [CollatzResearch.WordTrace]
  refine ⟨437530064544278176245115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 583373419392370901660153 437530064544278176245115)
  ·
    refine ⟨656295096816417264367673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 437530064544278176245115 656295096816417264367673)
    ·
      refine ⟨492221322612312948275755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 656295096816417264367673 492221322612312948275755)
      ·
        refine ⟨738331983918469422413633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492221322612312948275755 738331983918469422413633)
        ·
          refine ⟨553748987938852066810225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 738331983918469422413633 553748987938852066810225)
          ·
            refine ⟨415311740954139050107669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 553748987938852066810225 415311740954139050107669)
            ·
              refine ⟨19467737857225267973797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 415311740954139050107669 19467737857225267973797)
              ·
                refine ⟨3650200848229737745087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19467737857225267973797 3650200848229737745087)
                ·
                  rfl

theorem cell20_23992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 4].length) (baseStart_23992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23992 prefixEnd_23992 := by exact prefixLift 23992
  have htrace : WordTrace (prefixWord ++ tailWord_23992) baseStart_23992 baseEnd_23992 := by
    simpa [prefixWord, tailWord_23992, baseEnd_23992] using wordTrace_append hprefix tailTrace_23992
  have hstable : (prefixWord ++ tailWord_23992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23992).length < 2 ^ (prefixWord ++ tailWord_23992).sum := by decide
  have hdescent : baseEnd_23992 < baseStart_23992 := by decide
  rcases family_descends (prefixWord ++ tailWord_23992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24023 : List Nat := [1, 1, 3, 2, 1, 1, 1, 8, 2]
def baseStart_24023 : Nat := 118140960795 + 24023 * 2 ^ 59
def prefixEnd_24023 : Nat := 4983230072969 + 3 ^ 40 * 24023 * 2
def baseEnd_24023 : Nat := 10964751789390883201801

theorem tailTrace_24023 : CollatzResearch.WordTrace tailWord_24023 prefixEnd_24023 10964751789390883201801 := by
  unfold tailWord_24023
  simp only [CollatzResearch.WordTrace]
  refine ⟨876190791976248646868723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 584127194650832431245815 876190791976248646868723)
  ·
    refine ⟨1314286187964372970303085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 876190791976248646868723 1314286187964372970303085)
    ·
      refine ⟨492857320486639863863657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1314286187964372970303085 492857320486639863863657)
      ·
        refine ⟨369642990364979897897743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 492857320486639863863657 369642990364979897897743)
        ·
          refine ⟨554464485547469846846615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369642990364979897897743 554464485547469846846615)
          ·
            refine ⟨831696728321204770269923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554464485547469846846615 831696728321204770269923)
            ·
              refine ⟨1247545092481807155404885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831696728321204770269923 1247545092481807155404885)
              ·
                refine ⟨14619669052521177602401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1247545092481807155404885 14619669052521177602401)
                ·
                  refine ⟨10964751789390883201801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14619669052521177602401 10964751789390883201801)
                  ·
                    rfl

theorem cell20_24023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 2].length) (baseStart_24023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24023 prefixEnd_24023 := by exact prefixLift 24023
  have htrace : WordTrace (prefixWord ++ tailWord_24023) baseStart_24023 baseEnd_24023 := by
    simpa [prefixWord, tailWord_24023, baseEnd_24023] using wordTrace_append hprefix tailTrace_24023
  have hstable : (prefixWord ++ tailWord_24023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24023).length < 2 ^ (prefixWord ++ tailWord_24023).sum := by decide
  have hdescent : baseEnd_24023 < baseStart_24023 := by decide
  rcases family_descends (prefixWord ++ tailWord_24023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24033 : List Nat := [1, 2, 3, 1, 2, 5, 2, 1, 3]
def baseStart_24033 : Nat := 118140960795 + 24033 * 2 ^ 59
def prefixEnd_24033 : Nat := 4983230072969 + 3 ^ 40 * 24033 * 2
def baseEnd_24033 : Nat := 10969316061875292868427

theorem tailTrace_24033 : CollatzResearch.WordTrace tailWord_24033 prefixEnd_24033 10969316061875292868427 := by
  unfold tailWord_24033
  simp only [CollatzResearch.WordTrace]
  refine ⟨876555521940020354732753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 584370347960013569821835 876555521940020354732753)
  ·
    refine ⟨657416641455015266049565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 876555521940020354732753 657416641455015266049565)
    ·
      refine ⟨246531240545630724768587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 657416641455015266049565 246531240545630724768587)
      ·
        refine ⟨369796860818446087152881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246531240545630724768587 369796860818446087152881)
        ·
          refine ⟨277347645613834565364661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369796860818446087152881 277347645613834565364661)
          ·
            refine ⟨26001341776296990502937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 277347645613834565364661 26001341776296990502937)
            ·
              refine ⟨19501006332222742877203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26001341776296990502937 19501006332222742877203)
              ·
                refine ⟨29251509498334114315805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19501006332222742877203 29251509498334114315805)
                ·
                  refine ⟨10969316061875292868427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29251509498334114315805 10969316061875292868427)
                  ·
                    rfl

theorem cell20_24033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 3].length) (baseStart_24033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24033 prefixEnd_24033 := by exact prefixLift 24033
  have htrace : WordTrace (prefixWord ++ tailWord_24033) baseStart_24033 baseEnd_24033 := by
    simpa [prefixWord, tailWord_24033, baseEnd_24033] using wordTrace_append hprefix tailTrace_24033
  have hstable : (prefixWord ++ tailWord_24033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24033).length < 2 ^ (prefixWord ++ tailWord_24033).sum := by decide
  have hdescent : baseEnd_24033 < baseStart_24033 := by decide
  rcases family_descends (prefixWord ++ tailWord_24033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24068 : List Nat := [2, 3, 2, 3, 2, 8]
def baseStart_24068 : Nat := 118140960795 + 24068 * 2 ^ 59
def prefixEnd_24068 : Nat := 4983230072969 + 3 ^ 40 * 24068 * 2
def baseEnd_24068 : Nat := 406862630206323211171

theorem tailTrace_24068 : CollatzResearch.WordTrace tailWord_24068 prefixEnd_24068 406862630206323211171 := by
  unfold tailWord_24068
  simp only [CollatzResearch.WordTrace]
  refine ⟨438916038406610666128429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 585221384542147554837905 438916038406610666128429)
  ·
    refine ⟨164593514402478999798161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 438916038406610666128429 164593514402478999798161)
    ·
      refine ⟨123445135801859249848621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164593514402478999798161 123445135801859249848621)
      ·
        refine ⟨46291925925697218693233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123445135801859249848621 46291925925697218693233)
        ·
          refine ⟨34718944444272914019925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46291925925697218693233 34718944444272914019925)
          ·
            refine ⟨406862630206323211171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 34718944444272914019925 406862630206323211171)
            ·
              rfl

theorem cell20_24068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 8].length) (baseStart_24068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24068 prefixEnd_24068 := by exact prefixLift 24068
  have htrace : WordTrace (prefixWord ++ tailWord_24068) baseStart_24068 baseEnd_24068 := by
    simpa [prefixWord, tailWord_24068, baseEnd_24068] using wordTrace_append hprefix tailTrace_24068
  have hstable : (prefixWord ++ tailWord_24068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24068).length < 2 ^ (prefixWord ++ tailWord_24068).sum := by decide
  have hdescent : baseEnd_24068 < baseStart_24068 := by decide
  rcases family_descends (prefixWord ++ tailWord_24068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24099 : List Nat := [1, 1, 1, 4, 5, 1, 1, 2, 4]
def baseStart_24099 : Nat := 118140960795 + 24099 * 2 ^ 59
def prefixEnd_24099 : Nat := 4983230072969 + 3 ^ 40 * 24099 * 2
def baseEnd_24099 : Nat := 10999440260272396668157

theorem tailTrace_24099 : CollatzResearch.WordTrace tailWord_24099 prefixEnd_24099 10999440260272396668157 := by
  unfold tailWord_24099
  simp only [CollatzResearch.WordTrace]
  refine ⟨878962739700913626635351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 585975159800609084423567 878962739700913626635351)
  ·
    refine ⟨1318444109551370439953027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 878962739700913626635351 1318444109551370439953027)
    ·
      refine ⟨1977666164327055659929541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1318444109551370439953027 1977666164327055659929541)
      ·
        refine ⟨370812405811322936236789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1977666164327055659929541 370812405811322936236789)
        ·
          refine ⟨34763663044811525272199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 370812405811322936236789 34763663044811525272199)
          ·
            refine ⟨52145494567217287908299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34763663044811525272199 52145494567217287908299)
            ·
              refine ⟨78218241850825931862449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52145494567217287908299 78218241850825931862449)
              ·
                refine ⟨58663681388119448896837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78218241850825931862449 58663681388119448896837)
                ·
                  refine ⟨10999440260272396668157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58663681388119448896837 10999440260272396668157)
                  ·
                    rfl

theorem cell20_24099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 4].length) (baseStart_24099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24099 prefixEnd_24099 := by exact prefixLift 24099
  have htrace : WordTrace (prefixWord ++ tailWord_24099) baseStart_24099 baseEnd_24099 := by
    simpa [prefixWord, tailWord_24099, baseEnd_24099] using wordTrace_append hprefix tailTrace_24099
  have hstable : (prefixWord ++ tailWord_24099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24099).length < 2 ^ (prefixWord ++ tailWord_24099).sum := by decide
  have hdescent : baseEnd_24099 < baseStart_24099 := by decide
  rcases family_descends (prefixWord ++ tailWord_24099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24127 : List Nat := [1, 1, 2, 2, 3, 4, 7]
def baseStart_24127 : Nat := 118140960795 + 24127 * 2 ^ 59
def prefixEnd_24127 : Nat := 4983230072969 + 3 ^ 40 * 24127 * 2
def baseEnd_24127 : Nat := 1223580024803193748301

theorem tailTrace_24127 : CollatzResearch.WordTrace tailWord_24127 prefixEnd_24127 1223580024803193748301 := by
  unfold tailWord_24127
  simp only [CollatzResearch.WordTrace]
  refine ⟨879983983599474408654635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 586655989066316272436423 879983983599474408654635)
  ·
    refine ⟨1319975975399211612981953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 879983983599474408654635 1319975975399211612981953)
    ·
      refine ⟨989981981549408709736465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1319975975399211612981953 989981981549408709736465)
      ·
        refine ⟨742486486162056532302349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 989981981549408709736465 742486486162056532302349)
        ·
          refine ⟨278432432310771199613381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 742486486162056532302349 278432432310771199613381)
          ·
            refine ⟨52206081058269599927509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 278432432310771199613381 52206081058269599927509)
            ·
              refine ⟨1223580024803193748301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 52206081058269599927509 1223580024803193748301)
              ·
                rfl

theorem cell20_24127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 7].length) (baseStart_24127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24127 prefixEnd_24127 := by exact prefixLift 24127
  have htrace : WordTrace (prefixWord ++ tailWord_24127) baseStart_24127 baseEnd_24127 := by
    simpa [prefixWord, tailWord_24127, baseEnd_24127] using wordTrace_append hprefix tailTrace_24127
  have hstable : (prefixWord ++ tailWord_24127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24127).length < 2 ^ (prefixWord ++ tailWord_24127).sum := by decide
  have hdescent : baseEnd_24127 < baseStart_24127 := by decide
  rcases family_descends (prefixWord ++ tailWord_24127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24157 : List Nat := [1, 4, 4, 2, 1, 2, 2, 4]
def baseStart_24157 : Nat := 118140960795 + 24157 * 2 ^ 59
def prefixEnd_24157 : Nat := 4983230072969 + 3 ^ 40 * 24157 * 2
def baseEnd_24157 : Nat := 3675304346893990911529

theorem tailTrace_24157 : CollatzResearch.WordTrace tailWord_24157 prefixEnd_24157 3675304346893990911529 := by
  unfold tailWord_24157
  simp only [CollatzResearch.WordTrace]
  refine ⟨881078173490789532246725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 587385448993859688164483 881078173490789532246725)
  ·
    refine ⟨165202157529523037296261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 881078173490789532246725 165202157529523037296261)
    ·
      refine ⟨30975404536785569493049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165202157529523037296261 30975404536785569493049)
      ·
        refine ⟨23231553402589177119787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30975404536785569493049 23231553402589177119787)
        ·
          refine ⟨34847330103883765679681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23231553402589177119787 34847330103883765679681)
          ·
            refine ⟨26135497577912824259761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34847330103883765679681 26135497577912824259761)
            ·
              refine ⟨19601623183434618194821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26135497577912824259761 19601623183434618194821)
              ·
                refine ⟨3675304346893990911529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19601623183434618194821 3675304346893990911529)
                ·
                  rfl

theorem cell20_24157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 4].length) (baseStart_24157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24157 prefixEnd_24157 := by exact prefixLift 24157
  have htrace : WordTrace (prefixWord ++ tailWord_24157) baseStart_24157 baseEnd_24157 := by
    simpa [prefixWord, tailWord_24157, baseEnd_24157] using wordTrace_append hprefix tailTrace_24157
  have hstable : (prefixWord ++ tailWord_24157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24157).length < 2 ^ (prefixWord ++ tailWord_24157).sum := by decide
  have hdescent : baseEnd_24157 < baseStart_24157 := by decide
  rcases family_descends (prefixWord ++ tailWord_24157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24182 : List Nat := [5, 1, 1, 2, 2, 1, 8]
def baseStart_24182 : Nat := 118140960795 + 24182 * 2 ^ 59
def prefixEnd_24182 : Nat := 4983230072969 + 3 ^ 40 * 24182 * 2
def baseEnd_24182 : Nat := 1226369302432555211239

theorem tailTrace_24182 : CollatzResearch.WordTrace tailWord_24182 prefixEnd_24182 1226369302432555211239 := by
  unfold tailWord_24182
  simp only [CollatzResearch.WordTrace]
  refine ⟨55124374900013675119175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 587993332266812534604533 55124374900013675119175)
  ·
    refine ⟨82686562350020512678763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55124374900013675119175 82686562350020512678763)
    ·
      refine ⟨124029843525030769018145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82686562350020512678763 124029843525030769018145)
      ·
        refine ⟨93022382643773076763609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124029843525030769018145 93022382643773076763609)
        ·
          refine ⟨69766786982829807572707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93022382643773076763609 69766786982829807572707)
          ·
            refine ⟨104650180474244711359061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69766786982829807572707 104650180474244711359061)
            ·
              refine ⟨1226369302432555211239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 104650180474244711359061 1226369302432555211239)
              ·
                rfl

theorem cell20_24182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 8].length) (baseStart_24182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24182 prefixEnd_24182 := by exact prefixLift 24182
  have htrace : WordTrace (prefixWord ++ tailWord_24182) baseStart_24182 baseEnd_24182 := by
    simpa [prefixWord, tailWord_24182, baseEnd_24182] using wordTrace_append hprefix tailTrace_24182
  have hstable : (prefixWord ++ tailWord_24182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24182).length < 2 ^ (prefixWord ++ tailWord_24182).sum := by decide
  have hdescent : baseEnd_24182 < baseStart_24182 := by decide
  rcases family_descends (prefixWord ++ tailWord_24182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24189 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 5]
def baseStart_24189 : Nat := 118140960795 + 24189 * 2 ^ 59
def prefixEnd_24189 : Nat := 4983230072969 + 3 ^ 40 * 24189 * 2
def baseEnd_24189 : Nat := 11040518712632083667789

theorem tailTrace_24189 : CollatzResearch.WordTrace tailWord_24189 prefixEnd_24189 11040518712632083667789 := by
  unfold tailWord_24189
  simp only [CollatzResearch.WordTrace]
  refine ⟨882245309374858997411621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 588163539583239331607747 882245309374858997411621)
  ·
    refine ⟨165420995507786062014679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 882245309374858997411621 165420995507786062014679)
    ·
      refine ⟨248131493261679093022019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165420995507786062014679 248131493261679093022019)
      ·
        refine ⟨372197239892518639533029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248131493261679093022019 372197239892518639533029)
        ·
          refine ⟨69786982479847244912443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 372197239892518639533029 69786982479847244912443)
          ·
            refine ⟨104680473719770867368665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69786982479847244912443 104680473719770867368665)
            ·
              refine ⟨78510355289828150526499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104680473719770867368665 78510355289828150526499)
              ·
                refine ⟨117765532934742225789749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78510355289828150526499 117765532934742225789749)
                ·
                  refine ⟨11040518712632083667789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117765532934742225789749 11040518712632083667789)
                  ·
                    rfl

theorem cell20_24189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_24189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24189 prefixEnd_24189 := by exact prefixLift 24189
  have htrace : WordTrace (prefixWord ++ tailWord_24189) baseStart_24189 baseEnd_24189 := by
    simpa [prefixWord, tailWord_24189, baseEnd_24189] using wordTrace_append hprefix tailTrace_24189
  have hstable : (prefixWord ++ tailWord_24189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24189).length < 2 ^ (prefixWord ++ tailWord_24189).sum := by decide
  have hdescent : baseEnd_24189 < baseStart_24189 := by decide
  rcases family_descends (prefixWord ++ tailWord_24189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24192 : List Nat := [2, 1, 1, 2, 1, 4, 5, 2, 2]
def baseStart_24192 : Nat := 118140960795 + 24192 * 2 ^ 59
def prefixEnd_24192 : Nat := 4983230072969 + 3 ^ 40 * 24192 * 2
def baseEnd_24192 : Nat := 11041887994377406567777

theorem tailTrace_24192 : CollatzResearch.WordTrace tailWord_24192 prefixEnd_24192 11041887994377406567777 := by
  unfold tailWord_24192
  simp only [CollatzResearch.WordTrace]
  refine ⟨441177364181995254885415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 588236485575993673180553 441177364181995254885415)
  ·
    refine ⟨661766046272992882328123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 441177364181995254885415 661766046272992882328123)
    ·
      refine ⟨992649069409489323492185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 661766046272992882328123 992649069409489323492185)
      ·
        refine ⟨744486802057116992619139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 992649069409489323492185 744486802057116992619139)
        ·
          refine ⟨1116730203085675488928709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 744486802057116992619139 1116730203085675488928709)
          ·
            refine ⟨209386913078564154174133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1116730203085675488928709 209386913078564154174133)
            ·
              refine ⟨19630023101115389453825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 209386913078564154174133 19630023101115389453825)
              ·
                refine ⟨14722517325836542090369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19630023101115389453825 14722517325836542090369)
                ·
                  refine ⟨11041887994377406567777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14722517325836542090369 11041887994377406567777)
                  ·
                    rfl

theorem cell20_24192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 2].length) (baseStart_24192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24192 prefixEnd_24192 := by exact prefixLift 24192
  have htrace : WordTrace (prefixWord ++ tailWord_24192) baseStart_24192 baseEnd_24192 := by
    simpa [prefixWord, tailWord_24192, baseEnd_24192] using wordTrace_append hprefix tailTrace_24192
  have hstable : (prefixWord ++ tailWord_24192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24192).length < 2 ^ (prefixWord ++ tailWord_24192).sum := by decide
  have hdescent : baseEnd_24192 < baseStart_24192 := by decide
  rcases family_descends (prefixWord ++ tailWord_24192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24203 : List Nat := [1, 1, 1, 1, 4, 1, 6, 5]
def baseStart_24203 : Nat := 118140960795 + 24203 * 2 ^ 59
def prefixEnd_24203 : Nat := 4983230072969 + 3 ^ 40 * 24203 * 2
def baseEnd_24203 : Nat := 3682302898036752400355

theorem tailTrace_24203 : CollatzResearch.WordTrace tailWord_24203 prefixEnd_24203 3682302898036752400355 := by
  unfold tailWord_24203
  simp only [CollatzResearch.WordTrace]
  refine ⟨882755931324139388421263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 588503954216092925614175 882755931324139388421263)
  ·
    refine ⟨1324133896986209082631895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 882755931324139388421263 1324133896986209082631895)
    ·
      refine ⟨1986200845479313623947843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1324133896986209082631895 1986200845479313623947843)
      ·
        refine ⟨2979301268218970435921765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1986200845479313623947843 2979301268218970435921765)
        ·
          refine ⟨558618987791056956735331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2979301268218970435921765 558618987791056956735331)
          ·
            refine ⟨837928481686585435102997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558618987791056956735331 837928481686585435102997)
            ·
              refine ⟨39277897579058692270453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 837928481686585435102997 39277897579058692270453)
              ·
                refine ⟨3682302898036752400355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39277897579058692270453 3682302898036752400355)
                ·
                  rfl

theorem cell20_24203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 5].length) (baseStart_24203 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24203 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24203 prefixEnd_24203 := by exact prefixLift 24203
  have htrace : WordTrace (prefixWord ++ tailWord_24203) baseStart_24203 baseEnd_24203 := by
    simpa [prefixWord, tailWord_24203, baseEnd_24203] using wordTrace_append hprefix tailTrace_24203
  have hstable : (prefixWord ++ tailWord_24203).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24203).length < 2 ^ (prefixWord ++ tailWord_24203).sum := by decide
  have hdescent : baseEnd_24203 < baseStart_24203 := by decide
  rcases family_descends (prefixWord ++ tailWord_24203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24206 : List Nat := [4, 1, 1, 3, 1, 3, 1, 3, 3]
def baseStart_24206 : Nat := 118140960795 + 24206 * 2 ^ 59
def prefixEnd_24206 : Nat := 4983230072969 + 3 ^ 40 * 24206 * 2
def baseEnd_24206 : Nat := 11048277975855580101053

theorem tailTrace_24206 : CollatzResearch.WordTrace tailWord_24206 prefixEnd_24206 11048277975855580101053 := by
  unfold tailWord_24206
  simp only [CollatzResearch.WordTrace]
  refine ⟨110358168789158862597559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 588576900208847267186981 110358168789158862597559)
  ·
    refine ⟨165537253183738293896339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110358168789158862597559 165537253183738293896339)
    ·
      refine ⟨248305879775607440844509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165537253183738293896339 248305879775607440844509)
      ·
        refine ⟨93114704915852790316691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248305879775607440844509 93114704915852790316691)
        ·
          refine ⟨139672057373779185475037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93114704915852790316691 139672057373779185475037)
          ·
            refine ⟨52377021515167194553139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139672057373779185475037 52377021515167194553139)
            ·
              refine ⟨78565532272750791829709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52377021515167194553139 78565532272750791829709)
              ·
                refine ⟨29462074602281546936141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78565532272750791829709 29462074602281546936141)
                ·
                  refine ⟨11048277975855580101053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29462074602281546936141 11048277975855580101053)
                  ·
                    rfl

theorem cell20_24206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_24206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24206 prefixEnd_24206 := by exact prefixLift 24206
  have htrace : WordTrace (prefixWord ++ tailWord_24206) baseStart_24206 baseEnd_24206 := by
    simpa [prefixWord, tailWord_24206, baseEnd_24206] using wordTrace_append hprefix tailTrace_24206
  have hstable : (prefixWord ++ tailWord_24206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24206).length < 2 ^ (prefixWord ++ tailWord_24206).sum := by decide
  have hdescent : baseEnd_24206 < baseStart_24206 := by decide
  rcases family_descends (prefixWord ++ tailWord_24206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24247 : List Nat := [1, 1, 3, 1, 5, 3, 2, 2, 2]
def baseStart_24247 : Nat := 118140960795 + 24247 * 2 ^ 59
def prefixEnd_24247 : Nat := 4983230072969 + 3 ^ 40 * 24247 * 2
def baseEnd_24247 : Nat := 11066991493041659734219

theorem tailTrace_24247 : CollatzResearch.WordTrace tailWord_24247 prefixEnd_24247 11066991493041659734219 := by
  unfold tailWord_24247
  simp only [CollatzResearch.WordTrace]
  refine ⟨884360743164734903022995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 589573828776489935348663 884360743164734903022995)
  ·
    refine ⟨1326541114747102354534493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 884360743164734903022995 1326541114747102354534493)
    ·
      refine ⟨497452918030163382950435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1326541114747102354534493 497452918030163382950435)
      ·
        refine ⟨746179377045245074425653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497452918030163382950435 746179377045245074425653)
        ·
          refine ⟨69954316597991725727405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 746179377045245074425653 69954316597991725727405)
          ·
            refine ⟨26232868724246897147777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69954316597991725727405 26232868724246897147777)
            ·
              refine ⟨19674651543185172860833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26232868724246897147777 19674651543185172860833)
              ·
                refine ⟨14755988657388879645625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19674651543185172860833 14755988657388879645625)
                ·
                  refine ⟨11066991493041659734219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14755988657388879645625 11066991493041659734219)
                  ·
                    rfl

theorem cell20_24247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 2].length) (baseStart_24247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24247 prefixEnd_24247 := by exact prefixLift 24247
  have htrace : WordTrace (prefixWord ++ tailWord_24247) baseStart_24247 baseEnd_24247 := by
    simpa [prefixWord, tailWord_24247, baseEnd_24247] using wordTrace_append hprefix tailTrace_24247
  have hstable : (prefixWord ++ tailWord_24247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24247).length < 2 ^ (prefixWord ++ tailWord_24247).sum := by decide
  have hdescent : baseEnd_24247 < baseStart_24247 := by decide
  rcases family_descends (prefixWord ++ tailWord_24247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24248 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 5]
def baseStart_24248 : Nat := 118140960795 + 24248 * 2 ^ 59
def prefixEnd_24248 : Nat := 4983230072969 + 3 ^ 40 * 24248 * 2
def baseEnd_24248 : Nat := 11067447920290100700881

theorem tailTrace_24248 : CollatzResearch.WordTrace tailWord_24248 prefixEnd_24248 11067447920290100700881 := by
  unfold tailWord_24248
  simp only [CollatzResearch.WordTrace]
  refine ⟨442198608080556036904699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 589598144107408049206265 442198608080556036904699)
  ·
    refine ⟨663297912120834055357049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 442198608080556036904699 663297912120834055357049)
    ·
      refine ⟨497473434090625541517787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 663297912120834055357049 497473434090625541517787)
      ·
        refine ⟨746210151135938312276681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497473434090625541517787 746210151135938312276681)
        ·
          refine ⟨559657613351953734207511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 746210151135938312276681 559657613351953734207511)
          ·
            refine ⟨839486420027930601311267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559657613351953734207511 839486420027930601311267)
            ·
              refine ⟨1259229630041895901966901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 839486420027930601311267 1259229630041895901966901)
              ·
                refine ⟨118052777816427740809397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1259229630041895901966901 118052777816427740809397)
                ·
                  refine ⟨11067447920290100700881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118052777816427740809397 11067447920290100700881)
                  ·
                    rfl

theorem cell20_24248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_24248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24248 prefixEnd_24248 := by exact prefixLift 24248
  have htrace : WordTrace (prefixWord ++ tailWord_24248) baseStart_24248 baseEnd_24248 := by
    simpa [prefixWord, tailWord_24248, baseEnd_24248] using wordTrace_append hprefix tailTrace_24248
  have hstable : (prefixWord ++ tailWord_24248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24248).length < 2 ^ (prefixWord ++ tailWord_24248).sum := by decide
  have hdescent : baseEnd_24248 < baseStart_24248 := by decide
  rcases family_descends (prefixWord ++ tailWord_24248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24326 : List Nat := [6, 2, 2, 1, 1, 1, 1, 6]
def baseStart_24326 : Nat := 118140960795 + 24326 * 2 ^ 59
def prefixEnd_24326 : Nat := 4983230072969 + 3 ^ 40 * 24326 * 2
def baseEnd_24326 : Nat := 3701016415222832033521

theorem tailTrace_24326 : CollatzResearch.WordTrace tailWord_24326 prefixEnd_24326 3701016415222832033521 := by
  unfold tailWord_24326
  simp only [CollatzResearch.WordTrace]
  refine ⟨27726315933704106098401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 591494739919020930099221 27726315933704106098401)
  ·
    refine ⟨20794736950278079573801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27726315933704106098401 20794736950278079573801)
    ·
      refine ⟨15596052712708559680351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20794736950278079573801 15596052712708559680351)
      ·
        refine ⟨23394079069062839520527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15596052712708559680351 23394079069062839520527)
        ·
          refine ⟨35091118603594259280791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23394079069062839520527 35091118603594259280791)
          ·
            refine ⟨52636677905391388921187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35091118603594259280791 52636677905391388921187)
            ·
              refine ⟨78955016858087083381781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52636677905391388921187 78955016858087083381781)
              ·
                refine ⟨3701016415222832033521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78955016858087083381781 3701016415222832033521)
                ·
                  rfl

theorem cell20_24326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_24326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24326 prefixEnd_24326 := by exact prefixLift 24326
  have htrace : WordTrace (prefixWord ++ tailWord_24326) baseStart_24326 baseEnd_24326 := by
    simpa [prefixWord, tailWord_24326, baseEnd_24326] using wordTrace_append hprefix tailTrace_24326
  have hstable : (prefixWord ++ tailWord_24326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24326).length < 2 ^ (prefixWord ++ tailWord_24326).sum := by decide
  have hdescent : baseEnd_24326 < baseStart_24326 := by decide
  rcases family_descends (prefixWord ++ tailWord_24326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24334 : List Nat := [4, 1, 1, 2, 1, 1, 6, 4]
def baseStart_24334 : Nat := 118140960795 + 24334 * 2 ^ 59
def prefixEnd_24334 : Nat := 4983230072969 + 3 ^ 40 * 24334 * 2
def baseEnd_24334 : Nat := 3702233554552007944621

theorem tailTrace_24334 : CollatzResearch.WordTrace tailWord_24334 prefixEnd_24334 3702233554552007944621 := by
  unfold tailWord_24334
  simp only [CollatzResearch.WordTrace]
  refine ⟨110941736731193595180007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 591689262566365840960037 110941736731193595180007)
  ·
    refine ⟨166412605096790392770011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110941736731193595180007 166412605096790392770011)
    ·
      refine ⟨249618907645185589155017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166412605096790392770011 249618907645185589155017)
      ·
        refine ⟨187214180733889191866263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249618907645185589155017 187214180733889191866263)
        ·
          refine ⟨280821271100833787799395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187214180733889191866263 280821271100833787799395)
          ·
            refine ⟨421231906651250681699093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280821271100833787799395 421231906651250681699093)
            ·
              refine ⟨19745245624277375704645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 421231906651250681699093 19745245624277375704645)
              ·
                refine ⟨3702233554552007944621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19745245624277375704645 3702233554552007944621)
                ·
                  rfl

theorem cell20_24334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_24334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24334 prefixEnd_24334 := by exact prefixLift 24334
  have htrace : WordTrace (prefixWord ++ tailWord_24334) baseStart_24334 baseEnd_24334 := by
    simpa [prefixWord, tailWord_24334, baseEnd_24334] using wordTrace_append hprefix tailTrace_24334
  have hstable : (prefixWord ++ tailWord_24334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24334).length < 2 ^ (prefixWord ++ tailWord_24334).sum := by decide
  have hdescent : baseEnd_24334 < baseStart_24334 := by decide
  rcases family_descends (prefixWord ++ tailWord_24334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24372 : List Nat := [2, 5, 1, 1, 2, 1, 1, 7]
def baseStart_24372 : Nat := 118140960795 + 24372 * 2 ^ 59
def prefixEnd_24372 : Nat := 4983230072969 + 3 ^ 40 * 24372 * 2
def baseEnd_24372 : Nat := 3708014966365593522347

theorem tailTrace_24372 : CollatzResearch.WordTrace tailWord_24372 prefixEnd_24372 3708014966365593522347 := by
  unfold tailWord_24372
  simp only [CollatzResearch.WordTrace]
  refine ⟨444459933855940625661685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 592613245141254167548913 444459933855940625661685)
  ·
    refine ⟨41668118798994433655783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 444459933855940625661685 41668118798994433655783)
    ·
      refine ⟨62502178198491650483675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41668118798994433655783 62502178198491650483675)
      ·
        refine ⟨93753267297737475725513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62502178198491650483675 93753267297737475725513)
        ·
          refine ⟨70314950473303106794135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93753267297737475725513 70314950473303106794135)
          ·
            refine ⟨105472425709954660191203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70314950473303106794135 105472425709954660191203)
            ·
              refine ⟨158208638564931990286805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105472425709954660191203 158208638564931990286805)
              ·
                refine ⟨3708014966365593522347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 158208638564931990286805 3708014966365593522347)
                ·
                  rfl

theorem cell20_24372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_24372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24372 prefixEnd_24372 := by exact prefixLift 24372
  have htrace : WordTrace (prefixWord ++ tailWord_24372) baseStart_24372 baseEnd_24372 := by
    simpa [prefixWord, tailWord_24372, baseEnd_24372] using wordTrace_append hprefix tailTrace_24372
  have hstable : (prefixWord ++ tailWord_24372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24372).length < 2 ^ (prefixWord ++ tailWord_24372).sum := by decide
  have hdescent : baseEnd_24372 < baseStart_24372 := by decide
  rcases family_descends (prefixWord ++ tailWord_24372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24417 : List Nat := [1, 2, 3, 1, 1, 1, 6, 2, 3]
def baseStart_24417 : Nat := 118140960795 + 24417 * 2 ^ 59
def prefixEnd_24417 : Nat := 4983230072969 + 3 ^ 40 * 24417 * 2
def baseEnd_24417 : Nat := 11144584125276624066857

theorem tailTrace_24417 : CollatzResearch.WordTrace tailWord_24417 prefixEnd_24417 11144584125276624066857 := by
  unfold tailWord_24417
  simp only [CollatzResearch.WordTrace]
  refine ⟨890561152548853936711505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 593707435032569291141003 890561152548853936711505)
  ·
    refine ⟨667920864411640452533629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 890561152548853936711505 667920864411640452533629)
    ·
      refine ⟨250470324154365169700111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 667920864411640452533629 250470324154365169700111)
      ·
        refine ⟨375705486231547754550167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250470324154365169700111 375705486231547754550167)
        ·
          refine ⟨563558229347321631825251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375705486231547754550167 563558229347321631825251)
          ·
            refine ⟨845337344020982447737877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563558229347321631825251 845337344020982447737877)
            ·
              refine ⟨39625188000983552237713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 845337344020982447737877 39625188000983552237713)
              ·
                refine ⟨29718891000737664178285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39625188000983552237713 29718891000737664178285)
                ·
                  refine ⟨11144584125276624066857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29718891000737664178285 11144584125276624066857)
                  ·
                    rfl

theorem cell20_24417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 3].length) (baseStart_24417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24417 prefixEnd_24417 := by exact prefixLift 24417
  have htrace : WordTrace (prefixWord ++ tailWord_24417) baseStart_24417 baseEnd_24417 := by
    simpa [prefixWord, tailWord_24417, baseEnd_24417] using wordTrace_append hprefix tailTrace_24417
  have hstable : (prefixWord ++ tailWord_24417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24417).length < 2 ^ (prefixWord ++ tailWord_24417).sum := by decide
  have hdescent : baseEnd_24417 < baseStart_24417 := by decide
  rcases family_descends (prefixWord ++ tailWord_24417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24420 : List Nat := [2, 3, 1, 1, 5, 1, 1, 4, 2]
def baseStart_24420 : Nat := 118140960795 + 24420 * 2 ^ 59
def prefixEnd_24420 : Nat := 4983230072969 + 3 ^ 40 * 24420 * 2
def baseEnd_24420 : Nat := 11145953407021946966845

theorem tailTrace_24420 : CollatzResearch.WordTrace tailWord_24420 prefixEnd_24420 11145953407021946966845 := by
  unfold tailWord_24420
  simp only [CollatzResearch.WordTrace]
  refine ⟨445335285768992724535357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 593780381025323632713809 445335285768992724535357)
  ·
    refine ⟨167000732163372271700759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 445335285768992724535357 167000732163372271700759)
    ·
      refine ⟨250501098245058407551139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167000732163372271700759 250501098245058407551139)
      ·
        refine ⟨375751647367587611326709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250501098245058407551139 375751647367587611326709)
        ·
          refine ⟨35226716940711338561879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 375751647367587611326709 35226716940711338561879)
          ·
            refine ⟨52840075411067007842819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35226716940711338561879 52840075411067007842819)
            ·
              refine ⟨79260113116600511764229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52840075411067007842819 79260113116600511764229)
              ·
                refine ⟨14861271209362595955793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79260113116600511764229 14861271209362595955793)
                ·
                  refine ⟨11145953407021946966845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14861271209362595955793 11145953407021946966845)
                  ·
                    rfl

theorem cell20_24420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_24420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24420 prefixEnd_24420 := by exact prefixLift 24420
  have htrace : WordTrace (prefixWord ++ tailWord_24420) baseStart_24420 baseEnd_24420 := by
    simpa [prefixWord, tailWord_24420, baseEnd_24420] using wordTrace_append hprefix tailTrace_24420
  have hstable : (prefixWord ++ tailWord_24420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24420).length < 2 ^ (prefixWord ++ tailWord_24420).sum := by decide
  have hdescent : baseEnd_24420 < baseStart_24420 := by decide
  rcases family_descends (prefixWord ++ tailWord_24420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24424 : List Nat := [2, 1, 4, 2, 1, 1, 2, 3, 4]
def baseStart_24424 : Nat := 118140960795 + 24424 * 2 ^ 59
def prefixEnd_24424 : Nat := 4983230072969 + 3 ^ 40 * 24424 * 2
def baseEnd_24424 : Nat := 11147779116015710833495

theorem tailTrace_24424 : CollatzResearch.WordTrace tailWord_24424 prefixEnd_24424 11147779116015710833495 := by
  unfold tailWord_24424
  simp only [CollatzResearch.WordTrace]
  refine ⟨445408231761747066108163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 593877642348996088144217 445408231761747066108163)
  ·
    refine ⟨668112347642620599162245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 445408231761747066108163 668112347642620599162245)
    ·
      refine ⟨125271065182991362342921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 668112347642620599162245 125271065182991362342921)
      ·
        refine ⟨93953298887243521757191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125271065182991362342921 93953298887243521757191)
        ·
          refine ⟨140929948330865282635787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93953298887243521757191 140929948330865282635787)
          ·
            refine ⟨211394922496297923953681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140929948330865282635787 211394922496297923953681)
            ·
              refine ⟨158546191872223442965261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211394922496297923953681 158546191872223442965261)
              ·
                refine ⟨59454821952083791111973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158546191872223442965261 59454821952083791111973)
                ·
                  refine ⟨11147779116015710833495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59454821952083791111973 11147779116015710833495)
                  ·
                    rfl

theorem cell20_24424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_24424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24424 prefixEnd_24424 := by exact prefixLift 24424
  have htrace : WordTrace (prefixWord ++ tailWord_24424) baseStart_24424 baseEnd_24424 := by
    simpa [prefixWord, tailWord_24424, baseEnd_24424] using wordTrace_append hprefix tailTrace_24424
  have hstable : (prefixWord ++ tailWord_24424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24424).length < 2 ^ (prefixWord ++ tailWord_24424).sum := by decide
  have hdescent : baseEnd_24424 < baseStart_24424 := by decide
  rcases family_descends (prefixWord ++ tailWord_24424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24472 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 5]
def baseStart_24472 : Nat := 118140960795 + 24472 * 2 ^ 59
def prefixEnd_24472 : Nat := 4983230072969 + 3 ^ 40 * 24472 * 2
def baseEnd_24472 : Nat := 11169687623940877233299

theorem tailTrace_24472 : CollatzResearch.WordTrace tailWord_24472 prefixEnd_24472 11169687623940877233299 := by
  unfold tailWord_24472
  simp only [CollatzResearch.WordTrace]
  refine ⟨446283583674799164981835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 595044778233065553309113 446283583674799164981835)
  ·
    refine ⟨669425375512198747472753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 446283583674799164981835 669425375512198747472753)
    ·
      refine ⟨502069031634149060604565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 669425375512198747472753 502069031634149060604565)
      ·
        refine ⟨23534485857850737215839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 502069031634149060604565 23534485857850737215839)
        ·
          refine ⟨35301728786776105823759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23534485857850737215839 35301728786776105823759)
          ·
            refine ⟨52952593180164158735639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35301728786776105823759 52952593180164158735639)
            ·
              refine ⟨79428889770246238103459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52952593180164158735639 79428889770246238103459)
              ·
                refine ⟨119143334655369357155189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79428889770246238103459 119143334655369357155189)
                ·
                  refine ⟨11169687623940877233299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119143334655369357155189 11169687623940877233299)
                  ·
                    rfl

theorem cell20_24472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 5].length) (baseStart_24472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24472 prefixEnd_24472 := by exact prefixLift 24472
  have htrace : WordTrace (prefixWord ++ tailWord_24472) baseStart_24472 baseEnd_24472 := by
    simpa [prefixWord, tailWord_24472, baseEnd_24472] using wordTrace_append hprefix tailTrace_24472
  have hstable : (prefixWord ++ tailWord_24472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24472).length < 2 ^ (prefixWord ++ tailWord_24472).sum := by decide
  have hdescent : baseEnd_24472 < baseStart_24472 := by decide
  rcases family_descends (prefixWord ++ tailWord_24472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24479 : List Nat := [1, 1, 2, 5, 3, 1, 2, 1, 4]
def baseStart_24479 : Nat := 118140960795 + 24479 * 2 ^ 59
def prefixEnd_24479 : Nat := 4983230072969 + 3 ^ 40 * 24479 * 2
def baseEnd_24479 : Nat := 11172882614679963999937

theorem tailTrace_24479 : CollatzResearch.WordTrace tailWord_24479 prefixEnd_24479 11172882614679963999937 := by
  unfold tailWord_24479
  simp only [CollatzResearch.WordTrace]
  refine ⟨892822478324238525468491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 595214985549492350312327 892822478324238525468491)
  ·
    refine ⟨1339233717486357788202737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 892822478324238525468491 1339233717486357788202737)
    ·
      refine ⟨1004425288114768341152053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1339233717486357788202737 1004425288114768341152053)
      ·
        refine ⟨94164870760759531983005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1004425288114768341152053 94164870760759531983005)
        ·
          refine ⟨35311826535284824493627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94164870760759531983005 35311826535284824493627)
          ·
            refine ⟨52967739802927236740441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35311826535284824493627 52967739802927236740441)
            ·
              refine ⟨39725804852195427555331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52967739802927236740441 39725804852195427555331)
              ·
                refine ⟨59588707278293141332997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39725804852195427555331 59588707278293141332997)
                ·
                  refine ⟨11172882614679963999937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59588707278293141332997 11172882614679963999937)
                  ·
                    rfl

theorem cell20_24479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 4].length) (baseStart_24479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24479 prefixEnd_24479 := by exact prefixLift 24479
  have htrace : WordTrace (prefixWord ++ tailWord_24479) baseStart_24479 baseEnd_24479 := by
    simpa [prefixWord, tailWord_24479, baseEnd_24479] using wordTrace_append hprefix tailTrace_24479
  have hstable : (prefixWord ++ tailWord_24479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24479).length < 2 ^ (prefixWord ++ tailWord_24479).sum := by decide
  have hdescent : baseEnd_24479 < baseStart_24479 := by decide
  rcases family_descends (prefixWord ++ tailWord_24479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24528 : List Nat := [2, 1, 1, 1, 1, 2, 12]
def baseStart_24528 : Nat := 118140960795 + 24528 * 2 ^ 59
def prefixEnd_24528 : Nat := 4983230072969 + 3 ^ 40 * 24528 * 2
def baseEnd_24528 : Nat := 1243916394428174596267

theorem tailTrace_24528 : CollatzResearch.WordTrace tailWord_24528 prefixEnd_24528 1243916394428174596267 := by
  unfold tailWord_24528
  simp only [CollatzResearch.WordTrace]
  refine ⟨447304827573359947001119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 596406436764479929334825 447304827573359947001119)
  ·
    refine ⟨670957241360039920501679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 447304827573359947001119 670957241360039920501679)
    ·
      refine ⟨1006435862040059880752519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 670957241360039920501679 1006435862040059880752519)
      ·
        refine ⟨1509653793060089821128779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1006435862040059880752519 1509653793060089821128779)
        ·
          refine ⟨2264480689590134731693169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1509653793060089821128779 2264480689590134731693169)
          ·
            refine ⟨1698360517192601048769877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2264480689590134731693169 1698360517192601048769877)
            ·
              refine ⟨1243916394428174596267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 1698360517192601048769877 1243916394428174596267)
              ·
                rfl

theorem cell20_24528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 12].length) (baseStart_24528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24528 prefixEnd_24528 := by exact prefixLift 24528
  have htrace : WordTrace (prefixWord ++ tailWord_24528) baseStart_24528 baseEnd_24528 := by
    simpa [prefixWord, tailWord_24528, baseEnd_24528] using wordTrace_append hprefix tailTrace_24528
  have hstable : (prefixWord ++ tailWord_24528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24528).length < 2 ^ (prefixWord ++ tailWord_24528).sum := by decide
  have hdescent : baseEnd_24528 < baseStart_24528 := by decide
  rcases family_descends (prefixWord ++ tailWord_24528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24540 : List Nat := [2, 2, 6, 1, 2, 1, 2, 1, 3]
def baseStart_24540 : Nat := 118140960795 + 24540 * 2 ^ 59
def prefixEnd_24540 : Nat := 4983230072969 + 3 ^ 40 * 24540 * 2
def baseEnd_24540 : Nat := 11200724676834862966355

theorem tailTrace_24540 : CollatzResearch.WordTrace tailWord_24540 prefixEnd_24540 11200724676834862966355 := by
  unfold tailWord_24540
  simp only [CollatzResearch.WordTrace]
  refine ⟨447523665551622971719537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 596698220735497295626049 447523665551622971719537)
  ·
    refine ⟨335642749163717228789653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 447523665551622971719537 335642749163717228789653)
    ·
      refine ⟨15733253867049245099515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 335642749163717228789653 15733253867049245099515)
      ·
        refine ⟨23599880800573867649273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15733253867049245099515 23599880800573867649273)
        ·
          refine ⟨17699910600430400736955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23599880800573867649273 17699910600430400736955)
          ·
            refine ⟨26549865900645601105433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17699910600430400736955 26549865900645601105433)
            ·
              refine ⟨19912399425484200829075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26549865900645601105433 19912399425484200829075)
              ·
                refine ⟨29868599138226301243613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19912399425484200829075 29868599138226301243613)
                ·
                  refine ⟨11200724676834862966355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29868599138226301243613 11200724676834862966355)
                  ·
                    rfl

theorem cell20_24540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 3].length) (baseStart_24540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24540 prefixEnd_24540 := by exact prefixLift 24540
  have htrace : WordTrace (prefixWord ++ tailWord_24540) baseStart_24540 baseEnd_24540 := by
    simpa [prefixWord, tailWord_24540, baseEnd_24540] using wordTrace_append hprefix tailTrace_24540
  have hstable : (prefixWord ++ tailWord_24540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24540).length < 2 ^ (prefixWord ++ tailWord_24540).sum := by decide
  have hdescent : baseEnd_24540 < baseStart_24540 := by decide
  rcases family_descends (prefixWord ++ tailWord_24540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24559 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 6]
def baseStart_24559 : Nat := 118140960795 + 24559 * 2 ^ 59
def prefixEnd_24559 : Nat := 4983230072969 + 3 ^ 40 * 24559 * 2
def baseEnd_24559 : Nat := 11209396794555241332943

theorem tailTrace_24559 : CollatzResearch.WordTrace tailWord_24559 prefixEnd_24559 11209396794555241332943 := by
  unfold tailWord_24559
  simp only [CollatzResearch.WordTrace]
  refine ⟨895740318034412188380731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 597160212022941458920487 895740318034412188380731)
  ·
    refine ⟨1343610477051618282571097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 895740318034412188380731 1343610477051618282571097)
    ·
      refine ⟨1007707857788713711928323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1343610477051618282571097 1007707857788713711928323)
      ·
        refine ⟨1511561786683070567892485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1007707857788713711928323 1511561786683070567892485)
        ·
          refine ⟨283417835003075731479841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1511561786683070567892485 283417835003075731479841)
          ·
            refine ⟨212563376252306798609881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283417835003075731479841 212563376252306798609881)
            ·
              refine ⟨159422532189230098957411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212563376252306798609881 159422532189230098957411)
              ·
                refine ⟨239133798283845148436117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159422532189230098957411 239133798283845148436117)
                ·
                  refine ⟨11209396794555241332943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 239133798283845148436117 11209396794555241332943)
                  ·
                    rfl

theorem cell20_24559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_24559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24559 prefixEnd_24559 := by exact prefixLift 24559
  have htrace : WordTrace (prefixWord ++ tailWord_24559) baseStart_24559 baseEnd_24559 := by
    simpa [prefixWord, tailWord_24559, baseEnd_24559] using wordTrace_append hprefix tailTrace_24559
  have hstable : (prefixWord ++ tailWord_24559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24559).length < 2 ^ (prefixWord ++ tailWord_24559).sum := by decide
  have hdescent : baseEnd_24559 < baseStart_24559 := by decide
  rcases family_descends (prefixWord ++ tailWord_24559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24586 : List Nat := [3, 1, 2, 2, 4, 1, 2, 2, 3]
def baseStart_24586 : Nat := 118140960795 + 24586 * 2 ^ 59
def prefixEnd_24586 : Nat := 4983230072969 + 3 ^ 40 * 24586 * 2
def baseEnd_24586 : Nat := 11221720330263147432833

theorem tailTrace_24586 : CollatzResearch.WordTrace tailWord_24586 prefixEnd_24586 11221720330263147432833 := by
  unfold tailWord_24586
  simp only [CollatzResearch.WordTrace]
  refine ⟨224181272234148949903403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 597816725957730533075741 224181272234148949903403)
  ·
    refine ⟨336271908351223424855105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224181272234148949903403 336271908351223424855105)
    ·
      refine ⟨252203931263417568641329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336271908351223424855105 252203931263417568641329)
      ·
        refine ⟨189152948447563176480997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252203931263417568641329 189152948447563176480997)
        ·
          refine ⟨35466177833918095590187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189152948447563176480997 35466177833918095590187)
          ·
            refine ⟨53199266750877143385281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35466177833918095590187 53199266750877143385281)
            ·
              refine ⟨39899450063157857538961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53199266750877143385281 39899450063157857538961)
              ·
                refine ⟨29924587547368393154221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39899450063157857538961 29924587547368393154221)
                ·
                  refine ⟨11221720330263147432833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29924587547368393154221 11221720330263147432833)
                  ·
                    rfl

theorem cell20_24586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_24586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24586 prefixEnd_24586 := by exact prefixLift 24586
  have htrace : WordTrace (prefixWord ++ tailWord_24586) baseStart_24586 baseEnd_24586 := by
    simpa [prefixWord, tailWord_24586, baseEnd_24586] using wordTrace_append hprefix tailTrace_24586
  have hstable : (prefixWord ++ tailWord_24586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24586).length < 2 ^ (prefixWord ++ tailWord_24586).sum := by decide
  have hdescent : baseEnd_24586 < baseStart_24586 := by decide
  rcases family_descends (prefixWord ++ tailWord_24586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24596 : List Nat := [2, 4, 3, 2, 1, 2, 1, 5]
def baseStart_24596 : Nat := 118140960795 + 24596 * 2 ^ 59
def prefixEnd_24596 : Nat := 4983230072969 + 3 ^ 40 * 24596 * 2
def baseEnd_24596 : Nat := 3742094867582519033153

theorem tailTrace_24596 : CollatzResearch.WordTrace tailWord_24596 prefixEnd_24596 3742094867582519033153 := by
  unfold tailWord_24596
  simp only [CollatzResearch.WordTrace]
  refine ⟨448544909450183753738821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 598059879266911671651761 448544909450183753738821)
  ·
    refine ⟨84102170521909453826029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 448544909450183753738821 84102170521909453826029)
    ·
      refine ⟨31538313945716045184761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84102170521909453826029 31538313945716045184761)
      ·
        refine ⟨23653735459287033888571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31538313945716045184761 23653735459287033888571)
        ·
          refine ⟨35480603188930550832857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23653735459287033888571 35480603188930550832857)
          ·
            refine ⟨26610452391697913124643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35480603188930550832857 26610452391697913124643)
            ·
              refine ⟨39915678587546869686965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26610452391697913124643 39915678587546869686965)
              ·
                refine ⟨3742094867582519033153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39915678587546869686965 3742094867582519033153)
                ·
                  rfl

theorem cell20_24596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 5].length) (baseStart_24596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24596 prefixEnd_24596 := by exact prefixLift 24596
  have htrace : WordTrace (prefixWord ++ tailWord_24596) baseStart_24596 baseEnd_24596 := by
    simpa [prefixWord, tailWord_24596, baseEnd_24596] using wordTrace_append hprefix tailTrace_24596
  have hstable : (prefixWord ++ tailWord_24596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24596).length < 2 ^ (prefixWord ++ tailWord_24596).sum := by decide
  have hdescent : baseEnd_24596 < baseStart_24596 := by decide
  rcases family_descends (prefixWord ++ tailWord_24596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24638 : List Nat := [4, 2, 1, 3, 2, 1, 7]
def baseStart_24638 : Nat := 118140960795 + 24638 * 2 ^ 59
def prefixEnd_24638 : Nat := 4983230072969 + 3 ^ 40 * 24638 * 2
def baseEnd_24638 : Nat := 1249494949686897522143

theorem tailTrace_24638 : CollatzResearch.WordTrace tailWord_24638 prefixEnd_24638 1249494949686897522143 := by
  unfold tailWord_24638
  simp only [CollatzResearch.WordTrace]
  refine ⟨112327710593526085063321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 599081123165472453671045 112327710593526085063321)
  ·
    refine ⟨84245782945144563797491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112327710593526085063321 84245782945144563797491)
    ·
      refine ⟨126368674417716845696237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84245782945144563797491 126368674417716845696237)
      ·
        refine ⟨47388252906643817136089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126368674417716845696237 47388252906643817136089)
        ·
          refine ⟨35541189679982862852067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47388252906643817136089 35541189679982862852067)
          ·
            refine ⟨53311784519974294278101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35541189679982862852067 53311784519974294278101)
            ·
              refine ⟨1249494949686897522143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 53311784519974294278101 1249494949686897522143)
              ·
                rfl

theorem cell20_24638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 7].length) (baseStart_24638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24638 prefixEnd_24638 := by exact prefixLift 24638
  have htrace : WordTrace (prefixWord ++ tailWord_24638) baseStart_24638 baseEnd_24638 := by
    simpa [prefixWord, tailWord_24638, baseEnd_24638] using wordTrace_append hprefix tailTrace_24638
  have hstable : (prefixWord ++ tailWord_24638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24638).length < 2 ^ (prefixWord ++ tailWord_24638).sum := by decide
  have hdescent : baseEnd_24638 < baseStart_24638 := by decide
  rcases family_descends (prefixWord ++ tailWord_24638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24669 : List Nat := [1, 4, 4, 1, 1, 1, 2, 2, 4]
def baseStart_24669 : Nat := 118140960795 + 24669 * 2 ^ 59
def prefixEnd_24669 : Nat := 4983230072969 + 3 ^ 40 * 24669 * 2
def baseEnd_24669 : Nat := 11259603791883747665827

theorem tailTrace_24669 : CollatzResearch.WordTrace tailWord_24669 prefixEnd_24669 11259603791883747665827 := by
  unfold tailWord_24669
  simp only [CollatzResearch.WordTrace]
  refine ⟨899752347635900974885061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 599834898423933983256707 899752347635900974885061)
  ·
    refine ⟨168703565181731432790949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 899752347635900974885061 168703565181731432790949)
    ·
      refine ⟨31631918471574643648303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168703565181731432790949 31631918471574643648303)
      ·
        refine ⟨47447877707361965472455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31631918471574643648303 47447877707361965472455)
        ·
          refine ⟨71171816561042948208683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47447877707361965472455 71171816561042948208683)
          ·
            refine ⟨106757724841564422313025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71171816561042948208683 106757724841564422313025)
            ·
              refine ⟨80068293631173316734769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106757724841564422313025 80068293631173316734769)
              ·
                refine ⟨60051220223379987551077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80068293631173316734769 60051220223379987551077)
                ·
                  refine ⟨11259603791883747665827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60051220223379987551077 11259603791883747665827)
                  ·
                    rfl

theorem cell20_24669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_24669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24669 prefixEnd_24669 := by exact prefixLift 24669
  have htrace : WordTrace (prefixWord ++ tailWord_24669) baseStart_24669 baseEnd_24669 := by
    simpa [prefixWord, tailWord_24669, baseEnd_24669] using wordTrace_append hprefix tailTrace_24669
  have hstable : (prefixWord ++ tailWord_24669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24669).length < 2 ^ (prefixWord ++ tailWord_24669).sum := by decide
  have hdescent : baseEnd_24669 < baseStart_24669 := by decide
  rcases family_descends (prefixWord ++ tailWord_24669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24697 : List Nat := [1, 2, 1, 3, 4, 3, 6]
def baseStart_24697 : Nat := 118140960795 + 24697 * 2 ^ 59
def prefixEnd_24697 : Nat := 4983230072969 + 3 ^ 40 * 24697 * 2
def baseEnd_24697 : Nat := 1252487083871121636931

theorem tailTrace_24697 : CollatzResearch.WordTrace tailWord_24697 prefixEnd_24697 1252487083871121636931 := by
  unfold tailWord_24697
  simp only [CollatzResearch.WordTrace]
  refine ⟨900773591534461756904345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 600515727689641171269563 900773591534461756904345)
  ·
    refine ⟨675580193650846317678259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 900773591534461756904345 675580193650846317678259)
    ·
      refine ⟨1013370290476269476517389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 675580193650846317678259 1013370290476269476517389)
      ·
        refine ⟨380013858928601053694021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1013370290476269476517389 380013858928601053694021)
        ·
          refine ⟨71252598549112697567629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 380013858928601053694021 71252598549112697567629)
          ·
            refine ⟨26719724455917261587861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71252598549112697567629 26719724455917261587861)
            ·
              refine ⟨1252487083871121636931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26719724455917261587861 1252487083871121636931)
              ·
                rfl

theorem cell20_24697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 6].length) (baseStart_24697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24697 prefixEnd_24697 := by exact prefixLift 24697
  have htrace : WordTrace (prefixWord ++ tailWord_24697) baseStart_24697 baseEnd_24697 := by
    simpa [prefixWord, tailWord_24697, baseEnd_24697] using wordTrace_append hprefix tailTrace_24697
  have hstable : (prefixWord ++ tailWord_24697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24697).length < 2 ^ (prefixWord ++ tailWord_24697).sum := by decide
  have hdescent : baseEnd_24697 < baseStart_24697 := by decide
  rcases family_descends (prefixWord ++ tailWord_24697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24704 : List Nat := [2, 1, 1, 2, 1, 3, 1, 6, 3]
def baseStart_24704 : Nat := 118140960795 + 24704 * 2 ^ 59
def prefixEnd_24704 : Nat := 4983230072969 + 3 ^ 40 * 24704 * 2
def baseEnd_24704 : Nat := 11275578745579181499017

theorem tailTrace_24704 : CollatzResearch.WordTrace tailWord_24704 prefixEnd_24704 11275578745579181499017 := by
  unfold tailWord_24704
  simp only [CollatzResearch.WordTrace]
  refine ⟨450514451254550976204583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 600685935006067968272777 450514451254550976204583)
  ·
    refine ⟨675771676881826464306875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 450514451254550976204583 675771676881826464306875)
    ·
      refine ⟨1013657515322739696460313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 675771676881826464306875 1013657515322739696460313)
      ·
        refine ⟨760243136492054772345235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1013657515322739696460313 760243136492054772345235)
        ·
          refine ⟨1140364704738082158517853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 760243136492054772345235 1140364704738082158517853)
          ·
            refine ⟨427636764276780809444195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1140364704738082158517853 427636764276780809444195)
            ·
              refine ⟨641455146415171214166293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427636764276780809444195 641455146415171214166293)
              ·
                refine ⟨30068209988211150664045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 641455146415171214166293 30068209988211150664045)
                ·
                  refine ⟨11275578745579181499017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30068209988211150664045 11275578745579181499017)
                  ·
                    rfl

theorem cell20_24704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 3].length) (baseStart_24704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24704 prefixEnd_24704 := by exact prefixLift 24704
  have htrace : WordTrace (prefixWord ++ tailWord_24704) baseStart_24704 baseEnd_24704 := by
    simpa [prefixWord, tailWord_24704, baseEnd_24704] using wordTrace_append hprefix tailTrace_24704
  have hstable : (prefixWord ++ tailWord_24704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24704).length < 2 ^ (prefixWord ++ tailWord_24704).sum := by decide
  have hdescent : baseEnd_24704 < baseStart_24704 := by decide
  rcases family_descends (prefixWord ++ tailWord_24704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24735 : List Nat := [1, 1, 2, 6, 1, 1, 2, 6]
def baseStart_24735 : Nat := 118140960795 + 24735 * 2 ^ 59
def prefixEnd_24735 : Nat := 4983230072969 + 3 ^ 40 * 24735 * 2
def baseEnd_24735 : Nat := 3763242663426950488519

theorem tailTrace_24735 : CollatzResearch.WordTrace tailWord_24735 prefixEnd_24735 3763242663426950488519 := by
  unfold tailWord_24735
  simp only [CollatzResearch.WordTrace]
  refine ⟨902159565396794246787659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 601439710264529497858439 902159565396794246787659)
  ·
    refine ⟨1353239348095191370181489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 902159565396794246787659 1353239348095191370181489)
    ·
      refine ⟨1014929511071393527636117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1353239348095191370181489 1014929511071393527636117)
      ·
        refine ⟨47574820831471571607943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1014929511071393527636117 47574820831471571607943)
        ·
          refine ⟨71362231247207357411915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47574820831471571607943 71362231247207357411915)
          ·
            refine ⟨107043346870811036117873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71362231247207357411915 107043346870811036117873)
            ·
              refine ⟨80282510153108277088405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107043346870811036117873 80282510153108277088405)
              ·
                refine ⟨3763242663426950488519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80282510153108277088405 3763242663426950488519)
                ·
                  rfl

theorem cell20_24735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 6].length) (baseStart_24735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24735 prefixEnd_24735 := by exact prefixLift 24735
  have htrace : WordTrace (prefixWord ++ tailWord_24735) baseStart_24735 baseEnd_24735 := by
    simpa [prefixWord, tailWord_24735, baseEnd_24735] using wordTrace_append hprefix tailTrace_24735
  have hstable : (prefixWord ++ tailWord_24735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24735).length < 2 ^ (prefixWord ++ tailWord_24735).sum := by decide
  have hdescent : baseEnd_24735 < baseStart_24735 := by decide
  rcases family_descends (prefixWord ++ tailWord_24735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24759 : List Nat := [1, 1, 3, 1, 4, 3, 2, 2, 3]
def baseStart_24759 : Nat := 118140960795 + 24759 * 2 ^ 59
def prefixEnd_24759 : Nat := 4983230072969 + 3 ^ 40 * 24759 * 2
def baseEnd_24759 : Nat := 11300682244243434665459

theorem tailTrace_24759 : CollatzResearch.WordTrace tailWord_24759 prefixEnd_24759 11300682244243434665459 := by
  unfold tailWord_24759
  simp only [CollatzResearch.WordTrace]
  refine ⟨903034917309846345661331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 602023278206564230440887 903034917309846345661331)
  ·
    refine ⟨1354552375964769518491997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 903034917309846345661331 1354552375964769518491997)
    ·
      refine ⟨507957140986788569434499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1354552375964769518491997 507957140986788569434499)
      ·
        refine ⟨761935711480182854151749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507957140986788569434499 761935711480182854151749)
        ·
          refine ⟨142862945902534285153453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 761935711480182854151749 142862945902534285153453)
          ·
            refine ⟨53573604713450356932545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142862945902534285153453 53573604713450356932545)
            ·
              refine ⟨40180203535087767699409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53573604713450356932545 40180203535087767699409)
              ·
                refine ⟨30135152651315825774557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40180203535087767699409 30135152651315825774557)
                ·
                  refine ⟨11300682244243434665459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30135152651315825774557 11300682244243434665459)
                  ·
                    rfl

theorem cell20_24759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 3].length) (baseStart_24759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24759 prefixEnd_24759 := by exact prefixLift 24759
  have htrace : WordTrace (prefixWord ++ tailWord_24759) baseStart_24759 baseEnd_24759 := by
    simpa [prefixWord, tailWord_24759, baseEnd_24759] using wordTrace_append hprefix tailTrace_24759
  have hstable : (prefixWord ++ tailWord_24759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24759).length < 2 ^ (prefixWord ++ tailWord_24759).sum := by decide
  have hdescent : baseEnd_24759 < baseStart_24759 := by decide
  rcases family_descends (prefixWord ++ tailWord_24759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24769 : List Nat := [1, 2, 6, 1, 2, 2, 1, 5]
def baseStart_24769 : Nat := 118140960795 + 24769 * 2 ^ 59
def prefixEnd_24769 : Nat := 4983230072969 + 3 ^ 40 * 24769 * 2
def baseEnd_24769 : Nat := 3768415505575948110695

theorem tailTrace_24769 : CollatzResearch.WordTrace tailWord_24769 prefixEnd_24769 3768415505575948110695 := by
  unfold tailWord_24769
  simp only [CollatzResearch.WordTrace]
  refine ⟨903399647273618053525361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 602266431515745369016907 903399647273618053525361)
  ·
    refine ⟨677549735455213540144021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 903399647273618053525361 677549735455213540144021)
    ·
      refine ⟨31760143849463134694251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 677549735455213540144021 31760143849463134694251)
      ·
        refine ⟨47640215774194702041377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31760143849463134694251 47640215774194702041377)
        ·
          refine ⟨35730161830646026531033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47640215774194702041377 35730161830646026531033)
          ·
            refine ⟨26797621372984519898275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35730161830646026531033 26797621372984519898275)
            ·
              refine ⟨40196432059476779847413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26797621372984519898275 40196432059476779847413)
              ·
                refine ⟨3768415505575948110695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40196432059476779847413 3768415505575948110695)
                ·
                  rfl

theorem cell20_24769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 5].length) (baseStart_24769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24769 prefixEnd_24769 := by exact prefixLift 24769
  have htrace : WordTrace (prefixWord ++ tailWord_24769) baseStart_24769 baseEnd_24769 := by
    simpa [prefixWord, tailWord_24769, baseEnd_24769] using wordTrace_append hprefix tailTrace_24769
  have hstable : (prefixWord ++ tailWord_24769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24769).length < 2 ^ (prefixWord ++ tailWord_24769).sum := by decide
  have hdescent : baseEnd_24769 < baseStart_24769 := by decide
  rcases family_descends (prefixWord ++ tailWord_24769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24794 : List Nat := [3, 1, 1, 2, 2, 1, 2, 8]
def baseStart_24794 : Nat := 118140960795 + 24794 * 2 ^ 59
def prefixEnd_24794 : Nat := 4983230072969 + 3 ^ 40 * 24794 * 2
def baseEnd_24794 : Nat := 3772219065979622832883

theorem tailTrace_24794 : CollatzResearch.WordTrace tailWord_24794 prefixEnd_24794 3772219065979622832883 := by
  unfold tailWord_24794
  simp only [CollatzResearch.WordTrace]
  refine ⟨226077868045761830796359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 602874314788698215456957 226077868045761830796359)
  ·
    refine ⟨339116802068642746194539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226077868045761830796359 339116802068642746194539)
    ·
      refine ⟨508675203102964119291809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339116802068642746194539 508675203102964119291809)
      ·
        refine ⟨381506402327223089468857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 508675203102964119291809 381506402327223089468857)
        ·
          refine ⟨286129801745417317101643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381506402327223089468857 286129801745417317101643)
          ·
            refine ⟨429194702618125975652465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286129801745417317101643 429194702618125975652465)
            ·
              refine ⟨321896026963594481739349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429194702618125975652465 321896026963594481739349)
              ·
                refine ⟨3772219065979622832883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 321896026963594481739349 3772219065979622832883)
                ·
                  rfl

theorem cell20_24794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_24794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24794 prefixEnd_24794 := by exact prefixLift 24794
  have htrace : WordTrace (prefixWord ++ tailWord_24794) baseStart_24794 baseEnd_24794 := by
    simpa [prefixWord, tailWord_24794, baseEnd_24794] using wordTrace_append hprefix tailTrace_24794
  have hstable : (prefixWord ++ tailWord_24794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24794).length < 2 ^ (prefixWord ++ tailWord_24794).sum := by decide
  have hdescent : baseEnd_24794 < baseStart_24794 := by decide
  rcases family_descends (prefixWord ++ tailWord_24794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24835 : List Nat := [1, 1, 1, 3, 2, 3, 5, 1, 3]
def baseStart_24835 : Nat := 118140960795 + 24835 * 2 ^ 59
def prefixEnd_24835 : Nat := 4983230072969 + 3 ^ 40 * 24835 * 2
def baseEnd_24835 : Nat := 11335370715124948131815

theorem tailTrace_24835 : CollatzResearch.WordTrace tailWord_24835 prefixEnd_24835 11335370715124948131815 := by
  unfold tailWord_24835
  simp only [CollatzResearch.WordTrace]
  refine ⟨905806865034511325427959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 603871243356340883618639 905806865034511325427959)
  ·
    refine ⟨1358710297551766988141939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 905806865034511325427959 1358710297551766988141939)
    ·
      refine ⟨2038065446327650482212909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1358710297551766988141939 2038065446327650482212909)
      ·
        refine ⟨764274542372868930829841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2038065446327650482212909 764274542372868930829841)
        ·
          refine ⟨573205906779651698122381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 764274542372868930829841 573205906779651698122381)
          ·
            refine ⟨214952215042369386795893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 573205906779651698122381 214952215042369386795893)
            ·
              refine ⟨20151770160222130012115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 214952215042369386795893 20151770160222130012115)
              ·
                refine ⟨30227655240333195018173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20151770160222130012115 30227655240333195018173)
                ·
                  refine ⟨11335370715124948131815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30227655240333195018173 11335370715124948131815)
                  ·
                    rfl

theorem cell20_24835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 3].length) (baseStart_24835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24835 prefixEnd_24835 := by exact prefixLift 24835
  have htrace : WordTrace (prefixWord ++ tailWord_24835) baseStart_24835 baseEnd_24835 := by
    simpa [prefixWord, tailWord_24835, baseEnd_24835] using wordTrace_append hprefix tailTrace_24835
  have hstable : (prefixWord ++ tailWord_24835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24835).length < 2 ^ (prefixWord ++ tailWord_24835).sum := by decide
  have hdescent : baseEnd_24835 < baseStart_24835 := by decide
  rcases family_descends (prefixWord ++ tailWord_24835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24849 : List Nat := [1, 2, 2, 1, 1, 5, 4, 4]
def baseStart_24849 : Nat := 118140960795 + 24849 * 2 ^ 59
def prefixEnd_24849 : Nat := 4983230072969 + 3 ^ 40 * 24849 * 2
def baseEnd_24849 : Nat := 3780586898867707221697

theorem tailTrace_24849 : CollatzResearch.WordTrace tailWord_24849 prefixEnd_24849 3780586898867707221697 := by
  unfold tailWord_24849
  simp only [CollatzResearch.WordTrace]
  refine ⟨906317486983791716437601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 604211657989194477625067 906317486983791716437601)
  ·
    refine ⟨679738115237843787328201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 906317486983791716437601 679738115237843787328201)
    ·
      refine ⟨509803586428382840496151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 679738115237843787328201 509803586428382840496151)
      ·
        refine ⟨764705379642574260744227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509803586428382840496151 764705379642574260744227)
        ·
          refine ⟨1147058069463861391116341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 764705379642574260744227 1147058069463861391116341)
          ·
            refine ⟨107536694012237005417157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1147058069463861391116341 107536694012237005417157)
            ·
              refine ⟨20163130127294438515717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107536694012237005417157 20163130127294438515717)
              ·
                refine ⟨3780586898867707221697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20163130127294438515717 3780586898867707221697)
                ·
                  rfl

theorem cell20_24849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 4].length) (baseStart_24849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24849 prefixEnd_24849 := by exact prefixLift 24849
  have htrace : WordTrace (prefixWord ++ tailWord_24849) baseStart_24849 baseEnd_24849 := by
    simpa [prefixWord, tailWord_24849, baseEnd_24849] using wordTrace_append hprefix tailTrace_24849
  have hstable : (prefixWord ++ tailWord_24849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24849).length < 2 ^ (prefixWord ++ tailWord_24849).sum := by decide
  have hdescent : baseEnd_24849 < baseStart_24849 := by decide
  rcases family_descends (prefixWord ++ tailWord_24849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24890 : List Nat := [3, 1, 1, 1, 4, 4, 2, 1, 3]
def baseStart_24890 : Nat := 118140960795 + 24890 * 2 ^ 59
def prefixEnd_24890 : Nat := 4983230072969 + 3 ^ 40 * 24890 * 2
def baseEnd_24890 : Nat := 11360474213789201298257

theorem tailTrace_24890 : CollatzResearch.WordTrace tailWord_24890 prefixEnd_24890 11360474213789201298257 := by
  unfold tailWord_24890
  simp only [CollatzResearch.WordTrace]
  refine ⟨226953219958813929670031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 605208586556837145786749 226953219958813929670031)
  ·
    refine ⟨340429829938220894505047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226953219958813929670031 340429829938220894505047)
    ·
      refine ⟨510644744907331341757571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340429829938220894505047 510644744907331341757571)
      ·
        refine ⟨765967117360997012636357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510644744907331341757571 765967117360997012636357)
        ·
          refine ⟨143618834505186939869317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 765967117360997012636357 143618834505186939869317)
          ·
            refine ⟨26928531469722551225497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143618834505186939869317 26928531469722551225497)
            ·
              refine ⟨20196398602291913419123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26928531469722551225497 20196398602291913419123)
              ·
                refine ⟨30294597903437870128685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20196398602291913419123 30294597903437870128685)
                ·
                  refine ⟨11360474213789201298257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30294597903437870128685 11360474213789201298257)
                  ·
                    rfl

theorem cell20_24890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_24890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24890 prefixEnd_24890 := by exact prefixLift 24890
  have htrace : WordTrace (prefixWord ++ tailWord_24890) baseStart_24890 baseEnd_24890 := by
    simpa [prefixWord, tailWord_24890, baseEnd_24890] using wordTrace_append hprefix tailTrace_24890
  have hstable : (prefixWord ++ tailWord_24890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24890).length < 2 ^ (prefixWord ++ tailWord_24890).sum := by decide
  have hdescent : baseEnd_24890 < baseStart_24890 := by decide
  rcases family_descends (prefixWord ++ tailWord_24890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24908 : List Nat := [2, 2, 1, 3, 2, 1, 1, 8]
def baseStart_24908 : Nat := 118140960795 + 24908 * 2 ^ 59
def prefixEnd_24908 : Nat := 4983230072969 + 3 ^ 40 * 24908 * 2
def baseEnd_24908 : Nat := 3789563301420379566061

theorem tailTrace_24908 : CollatzResearch.WordTrace tailWord_24908 prefixEnd_24908 3789563301420379566061 := by
  unfold tailWord_24908
  simp only [CollatzResearch.WordTrace]
  refine ⟨454234696885022396417689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 605646262513363195223585 454234696885022396417689)
  ·
    refine ⟨340676022663766797313267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 454234696885022396417689 340676022663766797313267)
    ·
      refine ⟨511014033995650195969901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340676022663766797313267 511014033995650195969901)
      ·
        refine ⟨191630262748368823488713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 511014033995650195969901 191630262748368823488713)
        ·
          refine ⟨143722697061276617616535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191630262748368823488713 143722697061276617616535)
          ·
            refine ⟨215584045591914926424803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143722697061276617616535 215584045591914926424803)
            ·
              refine ⟨323376068387872389637205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215584045591914926424803 323376068387872389637205)
              ·
                refine ⟨3789563301420379566061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 323376068387872389637205 3789563301420379566061)
                ·
                  rfl

theorem cell20_24908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_24908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24908 prefixEnd_24908 := by exact prefixLift 24908
  have htrace : WordTrace (prefixWord ++ tailWord_24908) baseStart_24908 baseEnd_24908 := by
    simpa [prefixWord, tailWord_24908, baseEnd_24908] using wordTrace_append hprefix tailTrace_24908
  have hstable : (prefixWord ++ tailWord_24908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24908).length < 2 ^ (prefixWord ++ tailWord_24908).sum := by decide
  have hdescent : baseEnd_24908 < baseStart_24908 := by decide
  rcases family_descends (prefixWord ++ tailWord_24908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24915 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 5]
def baseStart_24915 : Nat := 118140960795 + 24915 * 2 ^ 59
def prefixEnd_24915 : Nat := 4983230072969 + 3 ^ 40 * 24915 * 2
def baseEnd_24915 : Nat := 11371884895000225464821

theorem tailTrace_24915 : CollatzResearch.WordTrace tailWord_24915 prefixEnd_24915 11371884895000225464821 := by
  unfold tailWord_24915
  simp only [CollatzResearch.WordTrace]
  refine ⟨908724704744684988340199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 605816469829789992226799 908724704744684988340199)
  ·
    refine ⟨1363087057117027482510299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 908724704744684988340199 1363087057117027482510299)
    ·
      refine ⟨2044630585675541223765449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1363087057117027482510299 2044630585675541223765449)
      ·
        refine ⟨1533472939256655917824087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2044630585675541223765449 1533472939256655917824087)
        ·
          refine ⟨2300209408884983876736131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1533472939256655917824087 2300209408884983876736131)
          ·
            refine ⟨3450314113327475815104197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2300209408884983876736131 3450314113327475815104197)
            ·
              refine ⟨646933896248901715332037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3450314113327475815104197 646933896248901715332037)
              ·
                refine ⟨121300105546669071624757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 646933896248901715332037 121300105546669071624757)
                ·
                  refine ⟨11371884895000225464821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121300105546669071624757 11371884895000225464821)
                  ·
                    rfl

theorem cell20_24915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_24915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24915 prefixEnd_24915 := by exact prefixLift 24915
  have htrace : WordTrace (prefixWord ++ tailWord_24915) baseStart_24915 baseEnd_24915 := by
    simpa [prefixWord, tailWord_24915, baseEnd_24915] using wordTrace_append hprefix tailTrace_24915
  have hstable : (prefixWord ++ tailWord_24915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24915).length < 2 ^ (prefixWord ++ tailWord_24915).sum := by decide
  have hdescent : baseEnd_24915 < baseStart_24915 := by decide
  rcases family_descends (prefixWord ++ tailWord_24915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24925 : List Nat := [1, 4, 5, 10]
def baseStart_24925 : Nat := 118140960795 + 24925 * 2 ^ 59
def prefixEnd_24925 : Nat := 4983230072969 + 3 ^ 40 * 24925 * 2
def baseEnd_24925 : Nat := 46816663240677510829

theorem tailTrace_24925 : CollatzResearch.WordTrace tailWord_24925 prefixEnd_24925 46816663240677510829 := by
  unfold tailWord_24925
  simp only [CollatzResearch.WordTrace]
  refine ⟨909089434708456696204229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 606059623138971130802819 909089434708456696204229)
  ·
    refine ⟨170454269007835630538293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 909089434708456696204229 170454269007835630538293)
    ·
      refine ⟨15980087719484590362965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170454269007835630538293 15980087719484590362965)
      ·
        refine ⟨46816663240677510829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 15980087719484590362965 46816663240677510829)
        ·
          rfl

theorem cell20_24925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 10].length) (baseStart_24925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24925 prefixEnd_24925 := by exact prefixLift 24925
  have htrace : WordTrace (prefixWord ++ tailWord_24925) baseStart_24925 baseEnd_24925 := by
    simpa [prefixWord, tailWord_24925, baseEnd_24925] using wordTrace_append hprefix tailTrace_24925
  have hstable : (prefixWord ++ tailWord_24925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24925).length < 2 ^ (prefixWord ++ tailWord_24925).sum := by decide
  have hdescent : baseEnd_24925 < baseStart_24925 := by decide
  rcases family_descends (prefixWord ++ tailWord_24925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24935 : List Nat := [1, 1, 5, 1, 3, 2, 1, 4, 2]
def baseStart_24935 : Nat := 118140960795 + 24935 * 2 ^ 59
def prefixEnd_24935 : Nat := 4983230072969 + 3 ^ 40 * 24935 * 2
def baseEnd_24935 : Nat := 11381013439969044798073

theorem tailTrace_24935 : CollatzResearch.WordTrace tailWord_24935 prefixEnd_24935 11381013439969044798073 := by
  unfold tailWord_24935
  simp only [CollatzResearch.WordTrace]
  refine ⟨909454164672228404068259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 606302776448152269378839 909454164672228404068259)
  ·
    refine ⟨1364181247008342606102389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 909454164672228404068259 1364181247008342606102389)
    ·
      refine ⟨127891991907032119322099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1364181247008342606102389 127891991907032119322099)
      ·
        refine ⟨191837987860548178983149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127891991907032119322099 191837987860548178983149)
        ·
          refine ⟨71939245447705567118681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191837987860548178983149 71939245447705567118681)
          ·
            refine ⟨53954434085779175339011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71939245447705567118681 53954434085779175339011)
            ·
              refine ⟨80931651128668763008517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53954434085779175339011 80931651128668763008517)
              ·
                refine ⟨15174684586625393064097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80931651128668763008517 15174684586625393064097)
                ·
                  refine ⟨11381013439969044798073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15174684586625393064097 11381013439969044798073)
                  ·
                    rfl

theorem cell20_24935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 2].length) (baseStart_24935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24935 prefixEnd_24935 := by exact prefixLift 24935
  have htrace : WordTrace (prefixWord ++ tailWord_24935) baseStart_24935 baseEnd_24935 := by
    simpa [prefixWord, tailWord_24935, baseEnd_24935] using wordTrace_append hprefix tailTrace_24935
  have hstable : (prefixWord ++ tailWord_24935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24935).length < 2 ^ (prefixWord ++ tailWord_24935).sum := by decide
  have hdescent : baseEnd_24935 < baseStart_24935 := by decide
  rcases family_descends (prefixWord ++ tailWord_24935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24949 : List Nat := [1, 3, 4, 1, 2, 1, 2, 3, 3]
def baseStart_24949 : Nat := 118140960795 + 24949 * 2 ^ 59
def prefixEnd_24949 : Nat := 4983230072969 + 3 ^ 40 * 24949 * 2
def baseEnd_24949 : Nat := 11387403421447218331349

theorem tailTrace_24949 : CollatzResearch.WordTrace tailWord_24949 prefixEnd_24949 11387403421447218331349 := by
  unfold tailWord_24949
  simp only [CollatzResearch.WordTrace]
  refine ⟨909964786621508795077901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 606643191081005863385267 909964786621508795077901)
  ·
    refine ⟨341236794983065798154213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 909964786621508795077901 341236794983065798154213)
    ·
      refine ⟨63981899059324837153915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 341236794983065798154213 63981899059324837153915)
      ·
        refine ⟨95972848588987255730873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63981899059324837153915 95972848588987255730873)
        ·
          refine ⟨71979636441740441798155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95972848588987255730873 71979636441740441798155)
          ·
            refine ⟨107969454662610662697233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71979636441740441798155 107969454662610662697233)
            ·
              refine ⟨80977090996957997022925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107969454662610662697233 80977090996957997022925)
              ·
                refine ⟨30366409123859248883597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80977090996957997022925 30366409123859248883597)
                ·
                  refine ⟨11387403421447218331349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30366409123859248883597 11387403421447218331349)
                  ·
                    rfl

theorem cell20_24949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_24949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24949 prefixEnd_24949 := by exact prefixLift 24949
  have htrace : WordTrace (prefixWord ++ tailWord_24949) baseStart_24949 baseEnd_24949 := by
    simpa [prefixWord, tailWord_24949, baseEnd_24949] using wordTrace_append hprefix tailTrace_24949
  have hstable : (prefixWord ++ tailWord_24949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24949).length < 2 ^ (prefixWord ++ tailWord_24949).sum := by decide
  have hdescent : baseEnd_24949 < baseStart_24949 := by decide
  rcases family_descends (prefixWord ++ tailWord_24949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24953 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 7]
def baseStart_24953 : Nat := 118140960795 + 24953 * 2 ^ 59
def prefixEnd_24953 : Nat := 4983230072969 + 3 ^ 40 * 24953 * 2
def baseEnd_24953 : Nat := 11389229130440982197999

theorem tailTrace_24953 : CollatzResearch.WordTrace tailWord_24953 prefixEnd_24953 11389229130440982197999 := by
  unfold tailWord_24953
  simp only [CollatzResearch.WordTrace]
  refine ⟨910110678607017478223513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 606740452404678318815675 910110678607017478223513)
  ·
    refine ⟨682583008955263108667635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 910110678607017478223513 682583008955263108667635)
    ·
      refine ⟨1023874513432894663001453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 682583008955263108667635 1023874513432894663001453)
      ·
        refine ⟨383952942537335498625545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1023874513432894663001453 383952942537335498625545)
        ·
          refine ⟨287964706903001623969159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383952942537335498625545 287964706903001623969159)
          ·
            refine ⟨431947060354502435953739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287964706903001623969159 431947060354502435953739)
            ·
              refine ⟨647920590531753653930609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431947060354502435953739 647920590531753653930609)
              ·
                refine ⟨485940442898815240447957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 647920590531753653930609 485940442898815240447957)
                ·
                  refine ⟨11389229130440982197999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 485940442898815240447957 11389229130440982197999)
                  ·
                    rfl

theorem cell20_24953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_24953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24953 prefixEnd_24953 := by exact prefixLift 24953
  have htrace : WordTrace (prefixWord ++ tailWord_24953) baseStart_24953 baseEnd_24953 := by
    simpa [prefixWord, tailWord_24953, baseEnd_24953] using wordTrace_append hprefix tailTrace_24953
  have hstable : (prefixWord ++ tailWord_24953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24953).length < 2 ^ (prefixWord ++ tailWord_24953).sum := by decide
  have hdescent : baseEnd_24953 < baseStart_24953 := by decide
  rcases family_descends (prefixWord ++ tailWord_24953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24990 : List Nat := [4, 3, 1, 2, 1, 1, 2, 4, 2]
def baseStart_24990 : Nat := 118140960795 + 24990 * 2 ^ 59
def prefixEnd_24990 : Nat := 4983230072969 + 3 ^ 40 * 24990 * 2
def baseEnd_24990 : Nat := 11406116938633297964515

theorem tailTrace_24990 : CollatzResearch.WordTrace tailWord_24990 prefixEnd_24990 11406116938633297964515 := by
  unfold tailWord_24990
  simp only [CollatzResearch.WordTrace]
  refine ⟨113932522434121599665053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 607640119648648531546949 113932522434121599665053)
  ·
    refine ⟨42724695912795599874395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113932522434121599665053 42724695912795599874395)
    ·
      refine ⟨64087043869193399811593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42724695912795599874395 64087043869193399811593)
      ·
        refine ⟨48065282901895049858695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64087043869193399811593 48065282901895049858695)
        ·
          refine ⟨72097924352842574788043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48065282901895049858695 72097924352842574788043)
          ·
            refine ⟨108146886529263862182065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72097924352842574788043 108146886529263862182065)
            ·
              refine ⟨81110164896947896636549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108146886529263862182065 81110164896947896636549)
              ·
                refine ⟨15208155918177730619353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81110164896947896636549 15208155918177730619353)
                ·
                  refine ⟨11406116938633297964515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15208155918177730619353 11406116938633297964515)
                  ·
                    rfl

theorem cell20_24990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_24990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24990 prefixEnd_24990 := by exact prefixLift 24990
  have htrace : WordTrace (prefixWord ++ tailWord_24990) baseStart_24990 baseEnd_24990 := by
    simpa [prefixWord, tailWord_24990, baseEnd_24990] using wordTrace_append hprefix tailTrace_24990
  have hstable : (prefixWord ++ tailWord_24990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24990).length < 2 ^ (prefixWord ++ tailWord_24990).sum := by decide
  have hdescent : baseEnd_24990 < baseStart_24990 := by decide
  rcases family_descends (prefixWord ++ tailWord_24990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24994 : List Nat := [3, 3, 1, 2, 1, 1, 4, 1, 4]
def baseStart_24994 : Nat := 118140960795 + 24994 * 2 ^ 59
def prefixEnd_24994 : Nat := 4983230072969 + 3 ^ 40 * 24994 * 2
def baseEnd_24994 : Nat := 11407942647627061831165

theorem tailTrace_24994 : CollatzResearch.WordTrace tailWord_24994 prefixEnd_24994 11407942647627061831165 := by
  unfold tailWord_24994
  simp only [CollatzResearch.WordTrace]
  refine ⟨227901517864620370116509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 607737380972320986977357 227901517864620370116509)
  ·
    refine ⟨85463069199232638793691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227901517864620370116509 85463069199232638793691)
    ·
      refine ⟨128194603798848958190537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85463069199232638793691 128194603798848958190537)
      ·
        refine ⟨96145952849136718642903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128194603798848958190537 96145952849136718642903)
        ·
          refine ⟨144218929273705077964355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96145952849136718642903 144218929273705077964355)
          ·
            refine ⟨216328393910557616946533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144218929273705077964355 216328393910557616946533)
            ·
              refine ⟨40561573858229553177475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216328393910557616946533 40561573858229553177475)
              ·
                refine ⟨60842360787344329766213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40561573858229553177475 60842360787344329766213)
                ·
                  refine ⟨11407942647627061831165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60842360787344329766213 11407942647627061831165)
                  ·
                    rfl

theorem cell20_24994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_24994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_24994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_24994 prefixEnd_24994 := by exact prefixLift 24994
  have htrace : WordTrace (prefixWord ++ tailWord_24994) baseStart_24994 baseEnd_24994 := by
    simpa [prefixWord, tailWord_24994, baseEnd_24994] using wordTrace_append hprefix tailTrace_24994
  have hstable : (prefixWord ++ tailWord_24994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24994).length < 2 ^ (prefixWord ++ tailWord_24994).sum := by decide
  have hdescent : baseEnd_24994 < baseStart_24994 := by decide
  rcases family_descends (prefixWord ++ tailWord_24994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25015 : List Nat := [1, 1, 3, 1, 3, 3, 2, 2, 4]
def baseStart_25015 : Nat := 118140960795 + 25015 * 2 ^ 59
def prefixEnd_25015 : Nat := 4983230072969 + 3 ^ 40 * 25015 * 2
def baseEnd_25015 : Nat := 11417527619844322131079

theorem tailTrace_25015 : CollatzResearch.WordTrace tailWord_25015 prefixEnd_25015 11417527619844322131079 := by
  unfold tailWord_25015
  simp only [CollatzResearch.WordTrace]
  refine ⟨912372004382402066980499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 608248002921601377986999 912372004382402066980499)
  ·
    refine ⟨1368558006573603100470749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 912372004382402066980499 1368558006573603100470749)
    ·
      refine ⟨513209252465101162676531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1368558006573603100470749 513209252465101162676531)
      ·
        refine ⟨769813878697651744014797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513209252465101162676531 769813878697651744014797)
        ·
          refine ⟨288680204511619404005549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 769813878697651744014797 288680204511619404005549)
          ·
            refine ⟨108255076691857276502081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288680204511619404005549 108255076691857276502081)
            ·
              refine ⟨81191307518892957376561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108255076691857276502081 81191307518892957376561)
              ·
                refine ⟨60893480639169718032421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81191307518892957376561 60893480639169718032421)
                ·
                  refine ⟨11417527619844322131079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60893480639169718032421 11417527619844322131079)
                  ·
                    rfl

theorem cell20_25015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 4].length) (baseStart_25015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25015 prefixEnd_25015 := by exact prefixLift 25015
  have htrace : WordTrace (prefixWord ++ tailWord_25015) baseStart_25015 baseEnd_25015 := by
    simpa [prefixWord, tailWord_25015, baseEnd_25015] using wordTrace_append hprefix tailTrace_25015
  have hstable : (prefixWord ++ tailWord_25015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25015).length < 2 ^ (prefixWord ++ tailWord_25015).sum := by decide
  have hdescent : baseEnd_25015 < baseStart_25015 := by decide
  rcases family_descends (prefixWord ++ tailWord_25015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25049 : List Nat := [1, 2, 1, 2, 4, 1, 5, 2, 2]
def baseStart_25049 : Nat := 118140960795 + 25049 * 2 ^ 59
def prefixEnd_25049 : Nat := 4983230072969 + 3 ^ 40 * 25049 * 2
def baseEnd_25049 : Nat := 11433046146291314997607

theorem tailTrace_25049 : CollatzResearch.WordTrace tailWord_25049 prefixEnd_25049 11433046146291314997607 := by
  unfold tailWord_25049
  simp only [CollatzResearch.WordTrace]
  refine ⟨913612086259225873718201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 609074724172817249145467 913612086259225873718201)
  ·
    refine ⟨685209064694419405288651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 913612086259225873718201 685209064694419405288651)
    ·
      refine ⟨1027813597041629107932977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 685209064694419405288651 1027813597041629107932977)
      ·
        refine ⟨770860197781221830949733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1027813597041629107932977 770860197781221830949733)
        ·
          refine ⟨144536287083979093303075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 770860197781221830949733 144536287083979093303075)
          ·
            refine ⟨216804430625968639954613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144536287083979093303075 216804430625968639954613)
            ·
              refine ⟨20325415371184559995745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 216804430625968639954613 20325415371184559995745)
              ·
                refine ⟨15244061528388419996809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20325415371184559995745 15244061528388419996809)
                ·
                  refine ⟨11433046146291314997607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15244061528388419996809 11433046146291314997607)
                  ·
                    rfl

theorem cell20_25049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 2].length) (baseStart_25049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25049 prefixEnd_25049 := by exact prefixLift 25049
  have htrace : WordTrace (prefixWord ++ tailWord_25049) baseStart_25049 baseEnd_25049 := by
    simpa [prefixWord, tailWord_25049, baseEnd_25049] using wordTrace_append hprefix tailTrace_25049
  have hstable : (prefixWord ++ tailWord_25049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25049).length < 2 ^ (prefixWord ++ tailWord_25049).sum := by decide
  have hdescent : baseEnd_25049 < baseStart_25049 := by decide
  rcases family_descends (prefixWord ++ tailWord_25049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25059 : List Nat := [1, 1, 1, 6, 4, 1, 2, 1, 3]
def baseStart_25059 : Nat := 118140960795 + 25059 * 2 ^ 59
def prefixEnd_25059 : Nat := 4983230072969 + 3 ^ 40 * 25059 * 2
def baseEnd_25059 : Nat := 11437610418775724664233

theorem tailTrace_25059 : CollatzResearch.WordTrace tailWord_25059 prefixEnd_25059 11437610418775724664233 := by
  unfold tailWord_25059
  simp only [CollatzResearch.WordTrace]
  refine ⟨913976816222997581582231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 609317877481998387721487 913976816222997581582231)
  ·
    refine ⟨1370965224334496372373347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 913976816222997581582231 1370965224334496372373347)
    ·
      refine ⟨2056447836501744558560021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1370965224334496372373347 2056447836501744558560021)
      ·
        refine ⟨96395992336019276182501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2056447836501744558560021 96395992336019276182501)
        ·
          refine ⟨18074248563003614284219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96395992336019276182501 18074248563003614284219)
          ·
            refine ⟨27111372844505421426329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18074248563003614284219 27111372844505421426329)
            ·
              refine ⟨20333529633379066069747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27111372844505421426329 20333529633379066069747)
              ·
                refine ⟨30500294450068599104621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20333529633379066069747 30500294450068599104621)
                ·
                  refine ⟨11437610418775724664233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30500294450068599104621 11437610418775724664233)
                  ·
                    rfl

theorem cell20_25059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 3].length) (baseStart_25059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25059 prefixEnd_25059 := by exact prefixLift 25059
  have htrace : WordTrace (prefixWord ++ tailWord_25059) baseStart_25059 baseEnd_25059 := by
    simpa [prefixWord, tailWord_25059, baseEnd_25059] using wordTrace_append hprefix tailTrace_25059
  have hstable : (prefixWord ++ tailWord_25059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25059).length < 2 ^ (prefixWord ++ tailWord_25059).sum := by decide
  have hdescent : baseEnd_25059 < baseStart_25059 := by decide
  rcases family_descends (prefixWord ++ tailWord_25059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25111 : List Nat := [1, 1, 3, 6, 2, 1, 1, 5]
def baseStart_25111 : Nat := 118140960795 + 25111 * 2 ^ 59
def prefixEnd_25111 : Nat := 4983230072969 + 3 ^ 40 * 25111 * 2
def baseEnd_25111 : Nat := 3820448211898218310229

theorem tailTrace_25111 : CollatzResearch.WordTrace tailWord_25111 prefixEnd_25111 3820448211898218310229 := by
  unfold tailWord_25111
  simp only [CollatzResearch.WordTrace]
  refine ⟨915873412034610462475187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 610582274689740308316791 915873412034610462475187)
  ·
    refine ⟨1373810118051915693712781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 915873412034610462475187 1373810118051915693712781)
    ·
      refine ⟨515178794269468385142293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1373810118051915693712781 515178794269468385142293)
      ·
        refine ⟨24149005981381330553545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 515178794269468385142293 24149005981381330553545)
        ·
          refine ⟨18111754486035997915159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24149005981381330553545 18111754486035997915159)
          ·
            refine ⟨27167631729053996872739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18111754486035997915159 27167631729053996872739)
            ·
              refine ⟨40751447593580995309109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27167631729053996872739 40751447593580995309109)
              ·
                refine ⟨3820448211898218310229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40751447593580995309109 3820448211898218310229)
                ·
                  rfl

theorem cell20_25111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 5].length) (baseStart_25111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25111 prefixEnd_25111 := by exact prefixLift 25111
  have htrace : WordTrace (prefixWord ++ tailWord_25111) baseStart_25111 baseEnd_25111 := by
    simpa [prefixWord, tailWord_25111, baseEnd_25111] using wordTrace_append hprefix tailTrace_25111
  have hstable : (prefixWord ++ tailWord_25111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25111).length < 2 ^ (prefixWord ++ tailWord_25111).sum := by decide
  have hdescent : baseEnd_25111 < baseStart_25111 := by decide
  rcases family_descends (prefixWord ++ tailWord_25111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25142 : List Nat := [5, 1, 2, 1, 2, 2, 2, 3, 2]
def baseStart_25142 : Nat := 118140960795 + 25142 * 2 ^ 59
def prefixEnd_25142 : Nat := 4983230072969 + 3 ^ 40 * 25142 * 2
def baseEnd_25142 : Nat := 11475493880396324897227

theorem tailTrace_25142 : CollatzResearch.WordTrace tailWord_25142 prefixEnd_25142 11475493880396324897227 := by
  unfold tailWord_25142
  simp only [CollatzResearch.WordTrace]
  refine ⟨57312754682643922303355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 611336049948201837902453 57312754682643922303355)
  ·
    refine ⟨85969132023965883455033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57312754682643922303355 85969132023965883455033)
    ·
      refine ⟨64476849017974412591275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85969132023965883455033 64476849017974412591275)
      ·
        refine ⟨96715273526961618886913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64476849017974412591275 96715273526961618886913)
        ·
          refine ⟨72536455145221214165185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96715273526961618886913 72536455145221214165185)
          ·
            refine ⟨54402341358915910623889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72536455145221214165185 54402341358915910623889)
            ·
              refine ⟨40801756019186932967917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54402341358915910623889 40801756019186932967917)
              ·
                refine ⟨15300658507195099862969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40801756019186932967917 15300658507195099862969)
                ·
                  refine ⟨11475493880396324897227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15300658507195099862969 11475493880396324897227)
                  ·
                    rfl

theorem cell20_25142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_25142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25142 prefixEnd_25142 := by exact prefixLift 25142
  have htrace : WordTrace (prefixWord ++ tailWord_25142) baseStart_25142 baseEnd_25142 := by
    simpa [prefixWord, tailWord_25142, baseEnd_25142] using wordTrace_append hprefix tailTrace_25142
  have hstable : (prefixWord ++ tailWord_25142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25142).length < 2 ^ (prefixWord ++ tailWord_25142).sum := by decide
  have hdescent : baseEnd_25142 < baseStart_25142 := by decide
  rcases family_descends (prefixWord ++ tailWord_25142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25143 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 5]
def baseStart_25143 : Nat := 118140960795 + 25143 * 2 ^ 59
def prefixEnd_25143 : Nat := 4983230072969 + 3 ^ 40 * 25143 * 2
def baseEnd_25143 : Nat := 11475950307644765863889

theorem tailTrace_25143 : CollatzResearch.WordTrace tailWord_25143 prefixEnd_25143 11475950307644765863889 := by
  unfold tailWord_25143
  simp only [CollatzResearch.WordTrace]
  refine ⟨917040547918679927640083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 611360365279119951760055 917040547918679927640083)
  ·
    refine ⟨1375560821878019891460125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 917040547918679927640083 1375560821878019891460125)
    ·
      refine ⟨515835308204257459297547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1375560821878019891460125 515835308204257459297547)
      ·
        refine ⟨773752962306386188946321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515835308204257459297547 773752962306386188946321)
        ·
          refine ⟨580314721729789641709741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 773752962306386188946321 580314721729789641709741)
          ·
            refine ⟨217618020648671115641153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 580314721729789641709741 217618020648671115641153)
            ·
              refine ⟨163213515486503336730865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217618020648671115641153 163213515486503336730865)
              ·
                refine ⟨122410136614877502548149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163213515486503336730865 122410136614877502548149)
                ·
                  refine ⟨11475950307644765863889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122410136614877502548149 11475950307644765863889)
                  ·
                    rfl

theorem cell20_25143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_25143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25143 prefixEnd_25143 := by exact prefixLift 25143
  have htrace : WordTrace (prefixWord ++ tailWord_25143) baseStart_25143 baseEnd_25143 := by
    simpa [prefixWord, tailWord_25143, baseEnd_25143] using wordTrace_append hprefix tailTrace_25143
  have hstable : (prefixWord ++ tailWord_25143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25143).length < 2 ^ (prefixWord ++ tailWord_25143).sum := by decide
  have hdescent : baseEnd_25143 < baseStart_25143 := by decide
  rcases family_descends (prefixWord ++ tailWord_25143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25146 : List Nat := [3, 1, 1, 1, 3, 3, 1, 5, 2]
def baseStart_25146 : Nat := 118140960795 + 25146 * 2 ^ 59
def prefixEnd_25146 : Nat := 4983230072969 + 3 ^ 40 * 25146 * 2
def baseEnd_25146 : Nat := 11477319589390088763877

theorem tailTrace_25146 : CollatzResearch.WordTrace tailWord_25146 prefixEnd_25146 11477319589390088763877 := by
  unfold tailWord_25146
  simp only [CollatzResearch.WordTrace]
  refine ⟨229287491726952859999823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 611433311271874293332861 229287491726952859999823)
  ·
    refine ⟨343931237590429289999735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229287491726952859999823 343931237590429289999735)
    ·
      refine ⟨515896856385643934999603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343931237590429289999735 515896856385643934999603)
      ·
        refine ⟨773845284578465902499405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515896856385643934999603 773845284578465902499405)
        ·
          refine ⟨290191981716924713437277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 773845284578465902499405 290191981716924713437277)
          ·
            refine ⟨108821993143846767538979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 290191981716924713437277 108821993143846767538979)
            ·
              refine ⟨163232989715770151308469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108821993143846767538979 163232989715770151308469)
              ·
                refine ⟨15303092785853451685169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 163232989715770151308469 15303092785853451685169)
                ·
                  refine ⟨11477319589390088763877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15303092785853451685169 11477319589390088763877)
                  ·
                    rfl

theorem cell20_25146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 2].length) (baseStart_25146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25146 prefixEnd_25146 := by exact prefixLift 25146
  have htrace : WordTrace (prefixWord ++ tailWord_25146) baseStart_25146 baseEnd_25146 := by
    simpa [prefixWord, tailWord_25146, baseEnd_25146] using wordTrace_append hprefix tailTrace_25146
  have hstable : (prefixWord ++ tailWord_25146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25146).length < 2 ^ (prefixWord ++ tailWord_25146).sum := by decide
  have hdescent : baseEnd_25146 < baseStart_25146 := by decide
  rcases family_descends (prefixWord ++ tailWord_25146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25198 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_25198 : Nat := 118140960795 + 25198 * 2 ^ 59
def prefixEnd_25198 : Nat := 4983230072969 + 3 ^ 40 * 25198 * 2
def baseEnd_25198 : Nat := 11501053806309019030331

theorem tailTrace_25198 : CollatzResearch.WordTrace tailWord_25198 prefixEnd_25198 11501053806309019030331 := by
  unfold tailWord_25198
  simp only [CollatzResearch.WordTrace]
  refine ⟨114880820339928040111531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 612697708479616213928165 114880820339928040111531)
  ·
    refine ⟨172321230509892060167297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114880820339928040111531 172321230509892060167297)
    ·
      refine ⟨129240922882419045125473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172321230509892060167297 129240922882419045125473)
      ·
        refine ⟨96930692161814283844105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129240922882419045125473 96930692161814283844105)
        ·
          refine ⟨72698019121360712883079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96930692161814283844105 72698019121360712883079)
          ·
            refine ⟨109047028682041069324619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72698019121360712883079 109047028682041069324619)
            ·
              refine ⟨163570543023061603986929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109047028682041069324619 163570543023061603986929)
              ·
                refine ⟨122677907267296202990197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163570543023061603986929 122677907267296202990197)
                ·
                  refine ⟨11501053806309019030331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122677907267296202990197 11501053806309019030331)
                  ·
                    rfl

theorem cell20_25198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_25198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25198 prefixEnd_25198 := by exact prefixLift 25198
  have htrace : WordTrace (prefixWord ++ tailWord_25198) baseStart_25198 baseEnd_25198 := by
    simpa [prefixWord, tailWord_25198, baseEnd_25198] using wordTrace_append hprefix tailTrace_25198
  have hstable : (prefixWord ++ tailWord_25198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25198).length < 2 ^ (prefixWord ++ tailWord_25198).sum := by decide
  have hdescent : baseEnd_25198 < baseStart_25198 := by decide
  rcases family_descends (prefixWord ++ tailWord_25198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25219 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 5]
def baseStart_25219 : Nat := 118140960795 + 25219 * 2 ^ 59
def prefixEnd_25219 : Nat := 4983230072969 + 3 ^ 40 * 25219 * 2
def baseEnd_25219 : Nat := 11510638778526279330245

theorem tailTrace_25219 : CollatzResearch.WordTrace tailWord_25219 prefixEnd_25219 11510638778526279330245 := by
  unfold tailWord_25219
  simp only [CollatzResearch.WordTrace]
  refine ⟨919812495643344907406711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 613208330428896604937807 919812495643344907406711)
  ·
    refine ⟨1379718743465017361110067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 919812495643344907406711 1379718743465017361110067)
    ·
      refine ⟨2069578115197526041665101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1379718743465017361110067 2069578115197526041665101)
      ·
        refine ⟨776091793199072265624413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2069578115197526041665101 776091793199072265624413)
        ·
          refine ⟨291034422449652099609155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 776091793199072265624413 291034422449652099609155)
          ·
            refine ⟨436551633674478149413733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291034422449652099609155 436551633674478149413733)
            ·
              refine ⟨81853431313964653015075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 436551633674478149413733 81853431313964653015075)
              ·
                refine ⟨122780146970946979522613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81853431313964653015075 122780146970946979522613)
                ·
                  refine ⟨11510638778526279330245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122780146970946979522613 11510638778526279330245)
                  ·
                    rfl

theorem cell20_25219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 5].length) (baseStart_25219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25219 prefixEnd_25219 := by exact prefixLift 25219
  have htrace : WordTrace (prefixWord ++ tailWord_25219) baseStart_25219 baseEnd_25219 := by
    simpa [prefixWord, tailWord_25219, baseEnd_25219] using wordTrace_append hprefix tailTrace_25219
  have hstable : (prefixWord ++ tailWord_25219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25219).length < 2 ^ (prefixWord ++ tailWord_25219).sum := by decide
  have hdescent : baseEnd_25219 < baseStart_25219 := by decide
  rcases family_descends (prefixWord ++ tailWord_25219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25271 : List Nat := [1, 1, 3, 1, 14]
def baseStart_25271 : Nat := 118140960795 + 25271 * 2 ^ 59
def prefixEnd_25271 : Nat := 4983230072969 + 3 ^ 40 * 25271 * 2
def baseEnd_25271 : Nat := 142399666610434686379

theorem tailTrace_25271 : CollatzResearch.WordTrace tailWord_25271 prefixEnd_25271 142399666610434686379 := by
  unfold tailWord_25271
  simp only [CollatzResearch.WordTrace]
  refine ⟨921709091454957788299667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 614472727636638525533111 921709091454957788299667)
  ·
    refine ⟨1382563637182436682449501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 921709091454957788299667 1382563637182436682449501)
    ·
      refine ⟨518461363943413755918563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1382563637182436682449501 518461363943413755918563)
      ·
        refine ⟨777692045915120633877845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518461363943413755918563 777692045915120633877845)
        ·
          refine ⟨142399666610434686379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 777692045915120633877845 142399666610434686379)
          ·
            rfl

theorem cell20_25271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 14].length) (baseStart_25271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25271 prefixEnd_25271 := by exact prefixLift 25271
  have htrace : WordTrace (prefixWord ++ tailWord_25271) baseStart_25271 baseEnd_25271 := by
    simpa [prefixWord, tailWord_25271, baseEnd_25271] using wordTrace_append hprefix tailTrace_25271
  have hstable : (prefixWord ++ tailWord_25271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25271).length < 2 ^ (prefixWord ++ tailWord_25271).sum := by decide
  have hdescent : baseEnd_25271 < baseStart_25271 := by decide
  rcases family_descends (prefixWord ++ tailWord_25271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25274 : List Nat := [3, 1, 1, 1, 2, 3, 4, 2, 3]
def baseStart_25274 : Nat := 118140960795 + 25274 * 2 ^ 59
def prefixEnd_25274 : Nat := 4983230072969 + 3 ^ 40 * 25274 * 2
def baseEnd_25274 : Nat := 11535742277190532496687

theorem tailTrace_25274 : CollatzResearch.WordTrace tailWord_25274 prefixEnd_25274 11535742277190532496687 := by
  unfold tailWord_25274
  simp only [CollatzResearch.WordTrace]
  refine ⟨230454627611022325164719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 614545673629392867105917 230454627611022325164719)
  ·
    refine ⟨345681941416533487747079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230454627611022325164719 345681941416533487747079)
    ·
      refine ⟨518522912124800231620619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345681941416533487747079 518522912124800231620619)
      ·
        refine ⟨777784368187200347430929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518522912124800231620619 777784368187200347430929)
        ·
          refine ⟨583338276140400260573197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 777784368187200347430929 583338276140400260573197)
          ·
            refine ⟨218751853552650097714949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 583338276140400260573197 218751853552650097714949)
            ·
              refine ⟨41015972541121893321553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 218751853552650097714949 41015972541121893321553)
              ·
                refine ⟨30761979405841419991165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41015972541121893321553 30761979405841419991165)
                ·
                  refine ⟨11535742277190532496687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30761979405841419991165 11535742277190532496687)
                  ·
                    rfl

theorem cell20_25274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_25274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25274 prefixEnd_25274 := by exact prefixLift 25274
  have htrace : WordTrace (prefixWord ++ tailWord_25274) baseStart_25274 baseEnd_25274 := by
    simpa [prefixWord, tailWord_25274, baseEnd_25274] using wordTrace_append hprefix tailTrace_25274
  have hstable : (prefixWord ++ tailWord_25274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25274).length < 2 ^ (prefixWord ++ tailWord_25274).sum := by decide
  have hdescent : baseEnd_25274 < baseStart_25274 := by decide
  rcases family_descends (prefixWord ++ tailWord_25274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25277 : List Nat := [1, 4, 1, 2, 1, 3, 4, 2, 2]
def baseStart_25277 : Nat := 118140960795 + 25277 * 2 ^ 59
def prefixEnd_25277 : Nat := 4983230072969 + 3 ^ 40 * 25277 * 2
def baseEnd_25277 : Nat := 11537111558935855396675

theorem tailTrace_25277 : CollatzResearch.WordTrace tailWord_25277 prefixEnd_25277 11537111558935855396675 := by
  unfold tailWord_25277
  simp only [CollatzResearch.WordTrace]
  refine ⟨921927929433220813018085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 614618619622147208678723 921927929433220813018085)
  ·
    refine ⟨172861486768728902440891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 921927929433220813018085 172861486768728902440891)
    ·
      refine ⟨259292230153093353661337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172861486768728902440891 259292230153093353661337)
      ·
        refine ⟨194469172614820015246003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259292230153093353661337 194469172614820015246003)
        ·
          refine ⟨291703758922230022869005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194469172614820015246003 291703758922230022869005)
          ·
            refine ⟨109388909595836258575877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291703758922230022869005 109388909595836258575877)
            ·
              refine ⟨20510420549219298482977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109388909595836258575877 20510420549219298482977)
              ·
                refine ⟨15382815411914473862233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20510420549219298482977 15382815411914473862233)
                ·
                  refine ⟨11537111558935855396675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15382815411914473862233 11537111558935855396675)
                  ·
                    rfl

theorem cell20_25277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_25277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25277 prefixEnd_25277 := by exact prefixLift 25277
  have htrace : WordTrace (prefixWord ++ tailWord_25277) baseStart_25277 baseEnd_25277 := by
    simpa [prefixWord, tailWord_25277, baseEnd_25277] using wordTrace_append hprefix tailTrace_25277
  have hstable : (prefixWord ++ tailWord_25277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25277).length < 2 ^ (prefixWord ++ tailWord_25277).sum := by decide
  have hdescent : baseEnd_25277 < baseStart_25277 := by decide
  rcases family_descends (prefixWord ++ tailWord_25277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25288 : List Nat := [2, 1, 3, 1, 2, 3, 3, 5]
def baseStart_25288 : Nat := 118140960795 + 25288 * 2 ^ 59
def prefixEnd_25288 : Nat := 4983230072969 + 3 ^ 40 * 25288 * 2
def baseEnd_25288 : Nat := 3847377419556235343321

theorem tailTrace_25288 : CollatzResearch.WordTrace tailWord_25288 prefixEnd_25288 3847377419556235343321 := by
  unfold tailWord_25288
  simp only [CollatzResearch.WordTrace]
  refine ⟨461164566196684845834259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 614886088262246461112345 461164566196684845834259)
  ·
    refine ⟨691746849295027268751389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 461164566196684845834259 691746849295027268751389)
    ·
      refine ⟨259405068485635225781771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 691746849295027268751389 259405068485635225781771)
      ·
        refine ⟨389107602728452838672657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259405068485635225781771 389107602728452838672657)
        ·
          refine ⟨291830702046339629004493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389107602728452838672657 291830702046339629004493)
          ·
            refine ⟨109436513267377360876685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291830702046339629004493 109436513267377360876685)
            ·
              refine ⟨41038692475266510328757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109436513267377360876685 41038692475266510328757)
              ·
                refine ⟨3847377419556235343321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41038692475266510328757 3847377419556235343321)
                ·
                  rfl

theorem cell20_25288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_25288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25288 prefixEnd_25288 := by exact prefixLift 25288
  have htrace : WordTrace (prefixWord ++ tailWord_25288) baseStart_25288 baseEnd_25288 := by
    simpa [prefixWord, tailWord_25288, baseEnd_25288] using wordTrace_append hprefix tailTrace_25288
  have hstable : (prefixWord ++ tailWord_25288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25288).length < 2 ^ (prefixWord ++ tailWord_25288).sum := by decide
  have hdescent : baseEnd_25288 < baseStart_25288 := by decide
  rcases family_descends (prefixWord ++ tailWord_25288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25298 : List Nat := [3, 2, 2, 2, 3, 1, 1, 2, 4]
def baseStart_25298 : Nat := 118140960795 + 25298 * 2 ^ 59
def prefixEnd_25298 : Nat := 4983230072969 + 3 ^ 40 * 25298 * 2
def baseEnd_25298 : Nat := 11546696531153115696589

theorem tailTrace_25298 : CollatzResearch.WordTrace tailWord_25298 prefixEnd_25298 11546696531153115696589 := by
  unfold tailWord_25298
  simp only [CollatzResearch.WordTrace]
  refine ⟨230673465589285349883137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 615129241571427599688365 230673465589285349883137)
  ·
    refine ⟨173005099191964012412353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230673465589285349883137 173005099191964012412353)
    ·
      refine ⟨129753824393973009309265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173005099191964012412353 129753824393973009309265)
      ·
        refine ⟨97315368295479756981949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129753824393973009309265 97315368295479756981949)
        ·
          refine ⟨36493263110804908868231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97315368295479756981949 36493263110804908868231)
          ·
            refine ⟨54739894666207363302347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36493263110804908868231 54739894666207363302347)
            ·
              refine ⟨82109841999311044953521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54739894666207363302347 82109841999311044953521)
              ·
                refine ⟨61582381499483283715141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82109841999311044953521 61582381499483283715141)
                ·
                  refine ⟨11546696531153115696589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61582381499483283715141 11546696531153115696589)
                  ·
                    rfl

theorem cell20_25298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_25298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25298 prefixEnd_25298 := by exact prefixLift 25298
  have htrace : WordTrace (prefixWord ++ tailWord_25298) baseStart_25298 baseEnd_25298 := by
    simpa [prefixWord, tailWord_25298, baseEnd_25298] using wordTrace_append hprefix tailTrace_25298
  have hstable : (prefixWord ++ tailWord_25298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25298).length < 2 ^ (prefixWord ++ tailWord_25298).sum := by decide
  have hdescent : baseEnd_25298 < baseStart_25298 := by decide
  rcases family_descends (prefixWord ++ tailWord_25298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25315 : List Nat := [1, 1, 1, 7, 1, 2, 2, 3, 2]
def baseStart_25315 : Nat := 118140960795 + 25315 * 2 ^ 59
def prefixEnd_25315 : Nat := 4983230072969 + 3 ^ 40 * 25315 * 2
def baseEnd_25315 : Nat := 11554455794376612129853

theorem tailTrace_25315 : CollatzResearch.WordTrace tailWord_25315 prefixEnd_25315 11554455794376612129853 := by
  unfold tailWord_25315
  simp only [CollatzResearch.WordTrace]
  refine ⟨923313903295553302901399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 615542602197035535267599 923313903295553302901399)
  ·
    refine ⟨1384970854943329954352099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 923313903295553302901399 1384970854943329954352099)
    ·
      refine ⟨2077456282414994931528149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1384970854943329954352099 2077456282414994931528149)
      ·
        refine ⟨48690381619101443707691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 2077456282414994931528149 48690381619101443707691)
        ·
          refine ⟨73035572428652165561537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48690381619101443707691 73035572428652165561537)
          ·
            refine ⟨54776679321489124171153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73035572428652165561537 54776679321489124171153)
            ·
              refine ⟨41082509491116843128365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54776679321489124171153 41082509491116843128365)
              ·
                refine ⟨15405941059168816173137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41082509491116843128365 15405941059168816173137)
                ·
                  refine ⟨11554455794376612129853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15405941059168816173137 11554455794376612129853)
                  ·
                    rfl

theorem cell20_25315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 2].length) (baseStart_25315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25315 prefixEnd_25315 := by exact prefixLift 25315
  have htrace : WordTrace (prefixWord ++ tailWord_25315) baseStart_25315 baseEnd_25315 := by
    simpa [prefixWord, tailWord_25315, baseEnd_25315] using wordTrace_append hprefix tailTrace_25315
  have hstable : (prefixWord ++ tailWord_25315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25315).length < 2 ^ (prefixWord ++ tailWord_25315).sum := by decide
  have hdescent : baseEnd_25315 < baseStart_25315 := by decide
  rcases family_descends (prefixWord ++ tailWord_25315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25326 : List Nat := [4, 1, 2, 1, 1, 4, 7]
def baseStart_25326 : Nat := 118140960795 + 25326 * 2 ^ 59
def prefixEnd_25326 : Nat := 4983230072969 + 3 ^ 40 * 25326 * 2
def baseEnd_25326 : Nat := 1284386277123273640349

theorem tailTrace_25326 : CollatzResearch.WordTrace tailWord_25326 prefixEnd_25326 1284386277123273640349 := by
  unfold tailWord_25326
  simp only [CollatzResearch.WordTrace]
  refine ⟨115464388281962772693979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 615810070837134787701221 115464388281962772693979)
  ·
    refine ⟨173196582422944159040969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115464388281962772693979 173196582422944159040969)
    ·
      refine ⟨129897436817208119280727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173196582422944159040969 129897436817208119280727)
      ·
        refine ⟨194846155225812178921091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129897436817208119280727 194846155225812178921091)
        ·
          refine ⟨292269232838718268381637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194846155225812178921091 292269232838718268381637)
          ·
            refine ⟨54800481157259675321557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 292269232838718268381637 54800481157259675321557)
            ·
              refine ⟨1284386277123273640349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 54800481157259675321557 1284386277123273640349)
              ·
                rfl

theorem cell20_25326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 7].length) (baseStart_25326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25326 prefixEnd_25326 := by exact prefixLift 25326
  have htrace : WordTrace (prefixWord ++ tailWord_25326) baseStart_25326 baseEnd_25326 := by
    simpa [prefixWord, tailWord_25326, baseEnd_25326] using wordTrace_append hprefix tailTrace_25326
  have hstable : (prefixWord ++ tailWord_25326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25326).length < 2 ^ (prefixWord ++ tailWord_25326).sum := by decide
  have hdescent : baseEnd_25326 < baseStart_25326 := by decide
  rcases family_descends (prefixWord ++ tailWord_25326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25332 : List Nat := [2, 6, 1, 1, 2, 1, 2, 1, 4]
def baseStart_25332 : Nat := 118140960795 + 25332 * 2 ^ 59
def prefixEnd_25332 : Nat := 4983230072969 + 3 ^ 40 * 25332 * 2
def baseEnd_25332 : Nat := 11562215057600108563117

theorem tailTrace_25332 : CollatzResearch.WordTrace tailWord_25332 prefixEnd_25332 11562215057600108563117 := by
  unfold tailWord_25332
  simp only [CollatzResearch.WordTrace]
  refine ⟨461966972116982603135125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 615955962822643470846833 461966972116982603135125)
  ·
    refine ⟨21654701817983559521959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 461966972116982603135125 21654701817983559521959)
    ·
      refine ⟨32482052726975339282939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21654701817983559521959 32482052726975339282939)
      ·
        refine ⟨48723079090463008924409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32482052726975339282939 48723079090463008924409)
        ·
          refine ⟨36542309317847256693307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48723079090463008924409 36542309317847256693307)
          ·
            refine ⟨54813463976770885039961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36542309317847256693307 54813463976770885039961)
            ·
              refine ⟨41110097982578163779971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54813463976770885039961 41110097982578163779971)
              ·
                refine ⟨61665146973867245669957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41110097982578163779971 61665146973867245669957)
                ·
                  refine ⟨11562215057600108563117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61665146973867245669957 11562215057600108563117)
                  ·
                    rfl

theorem cell20_25332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_25332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25332 prefixEnd_25332 := by exact prefixLift 25332
  have htrace : WordTrace (prefixWord ++ tailWord_25332) baseStart_25332 baseEnd_25332 := by
    simpa [prefixWord, tailWord_25332, baseEnd_25332] using wordTrace_append hprefix tailTrace_25332
  have hstable : (prefixWord ++ tailWord_25332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25332).length < 2 ^ (prefixWord ++ tailWord_25332).sum := by decide
  have hdescent : baseEnd_25332 < baseStart_25332 := by decide
  rcases family_descends (prefixWord ++ tailWord_25332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25346 : List Nat := [3, 4, 1, 1, 1, 3, 3, 1, 3]
def baseStart_25346 : Nat := 118140960795 + 25346 * 2 ^ 59
def prefixEnd_25346 : Nat := 4983230072969 + 3 ^ 40 * 25346 * 2
def baseEnd_25346 : Nat := 11568605039078282096393

theorem tailTrace_25346 : CollatzResearch.WordTrace tailWord_25346 prefixEnd_25346 11568605039078282096393 := by
  unfold tailWord_25346
  simp only [CollatzResearch.WordTrace]
  refine ⟨231111141545811399319973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 616296377455497064853261 231111141545811399319973)
  ·
    refine ⟨43333339039839637372495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231111141545811399319973 43333339039839637372495)
    ·
      refine ⟨65000008559759456058743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43333339039839637372495 65000008559759456058743)
      ·
        refine ⟨97500012839639184088115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65000008559759456058743 97500012839639184088115)
        ·
          refine ⟨146250019259458776132173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97500012839639184088115 146250019259458776132173)
          ·
            refine ⟨54843757222297041049565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146250019259458776132173 54843757222297041049565)
            ·
              refine ⟨20566408958361390393587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54843757222297041049565 20566408958361390393587)
              ·
                refine ⟨30849613437542085590381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20566408958361390393587 30849613437542085590381)
                ·
                  refine ⟨11568605039078282096393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30849613437542085590381 11568605039078282096393)
                  ·
                    rfl

theorem cell20_25346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_25346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25346 prefixEnd_25346 := by exact prefixLift 25346
  have htrace : WordTrace (prefixWord ++ tailWord_25346) baseStart_25346 baseEnd_25346 := by
    simpa [prefixWord, tailWord_25346, baseEnd_25346] using wordTrace_append hprefix tailTrace_25346
  have hstable : (prefixWord ++ tailWord_25346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25346).length < 2 ^ (prefixWord ++ tailWord_25346).sum := by decide
  have hdescent : baseEnd_25346 < baseStart_25346 := by decide
  rcases family_descends (prefixWord ++ tailWord_25346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25347 : List Nat := [1, 1, 1, 3, 2, 2, 1, 9]
def baseStart_25347 : Nat := 118140960795 + 25347 * 2 ^ 59
def prefixEnd_25347 : Nat := 4983230072969 + 3 ^ 40 * 25347 * 2
def baseEnd_25347 : Nat := 3856353822108907687685

theorem tailTrace_25347 : CollatzResearch.WordTrace tailWord_25347 prefixEnd_25347 3856353822108907687685 := by
  unfold tailWord_25347
  simp only [CollatzResearch.WordTrace]
  refine ⟨924481039179622768066295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 616320692786415178710863 924481039179622768066295)
  ·
    refine ⟨1386721558769434152099443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 924481039179622768066295 1386721558769434152099443)
    ·
      refine ⟨2080082338154151228149165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1386721558769434152099443 2080082338154151228149165)
      ·
        refine ⟨780030876807806710555937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2080082338154151228149165 780030876807806710555937)
        ·
          refine ⟨585023157605855032916953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 780030876807806710555937 585023157605855032916953)
          ·
            refine ⟨438767368204391274687715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 585023157605855032916953 438767368204391274687715)
            ·
              refine ⟨658151052306586912031573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438767368204391274687715 658151052306586912031573)
              ·
                refine ⟨3856353822108907687685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 658151052306586912031573 3856353822108907687685)
                ·
                  rfl

theorem cell20_25347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 9].length) (baseStart_25347 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25347 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25347 prefixEnd_25347 := by exact prefixLift 25347
  have htrace : WordTrace (prefixWord ++ tailWord_25347) baseStart_25347 baseEnd_25347 := by
    simpa [prefixWord, tailWord_25347, baseEnd_25347] using wordTrace_append hprefix tailTrace_25347
  have hstable : (prefixWord ++ tailWord_25347).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25347).length < 2 ^ (prefixWord ++ tailWord_25347).sum := by decide
  have hdescent : baseEnd_25347 < baseStart_25347 := by decide
  rcases family_descends (prefixWord ++ tailWord_25347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25395 : List Nat := [1, 1, 1, 2, 6, 1, 3, 1, 4]
def baseStart_25395 : Nat := 118140960795 + 25395 * 2 ^ 59
def prefixEnd_25395 : Nat := 4983230072969 + 3 ^ 40 * 25395 * 2
def baseEnd_25395 : Nat := 11590969974251889462859

theorem tailTrace_25395 : CollatzResearch.WordTrace tailWord_25395 prefixEnd_25395 11590969974251889462859 := by
  unfold tailWord_25395
  simp only [CollatzResearch.WordTrace]
  refine ⟨926231743005726965813639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 617487828670484643875759 926231743005726965813639)
  ·
    refine ⟨1389347614508590448720459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 926231743005726965813639 1389347614508590448720459)
    ·
      refine ⟨2084021421762885673080689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1389347614508590448720459 2084021421762885673080689)
      ·
        refine ⟨1563016066322164254810517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2084021421762885673080689 1563016066322164254810517)
        ·
          refine ⟨73266378108851449444243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1563016066322164254810517 73266378108851449444243)
          ·
            refine ⟨109899567163277174166365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73266378108851449444243 109899567163277174166365)
            ·
              refine ⟨41212337686228940312387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109899567163277174166365 41212337686228940312387)
              ·
                refine ⟨61818506529343410468581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41212337686228940312387 61818506529343410468581)
                ·
                  refine ⟨11590969974251889462859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61818506529343410468581 11590969974251889462859)
                  ·
                    rfl

theorem cell20_25395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 4].length) (baseStart_25395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25395 prefixEnd_25395 := by exact prefixLift 25395
  have htrace : WordTrace (prefixWord ++ tailWord_25395) baseStart_25395 baseEnd_25395 := by
    simpa [prefixWord, tailWord_25395, baseEnd_25395] using wordTrace_append hprefix tailTrace_25395
  have hstable : (prefixWord ++ tailWord_25395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25395).length < 2 ^ (prefixWord ++ tailWord_25395).sum := by decide
  have hdescent : baseEnd_25395 < baseStart_25395 := by decide
  rcases family_descends (prefixWord ++ tailWord_25395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25398 : List Nat := [5, 1, 2, 2, 2, 1, 2, 5]
def baseStart_25398 : Nat := 118140960795 + 25398 * 2 ^ 59
def prefixEnd_25398 : Nat := 4983230072969 + 3 ^ 40 * 25398 * 2
def baseEnd_25398 : Nat := 3864113085332404120949

theorem tailTrace_25398 : CollatzResearch.WordTrace tailWord_25398 prefixEnd_25398 3864113085332404120949 := by
  unfold tailWord_25398
  simp only [CollatzResearch.WordTrace]
  refine ⟨57896322624678654885803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 617560774663238985448565 57896322624678654885803)
  ·
    refine ⟨86844483937017982328705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57896322624678654885803 86844483937017982328705)
    ·
      refine ⟨65133362952763486746529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86844483937017982328705 65133362952763486746529)
      ·
        refine ⟨48850022214572615059897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65133362952763486746529 48850022214572615059897)
        ·
          refine ⟨36637516660929461294923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48850022214572615059897 36637516660929461294923)
          ·
            refine ⟨54956274991394191942385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36637516660929461294923 54956274991394191942385)
            ·
              refine ⟨41217206243545643956789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54956274991394191942385 41217206243545643956789)
              ·
                refine ⟨3864113085332404120949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41217206243545643956789 3864113085332404120949)
                ·
                  rfl

theorem cell20_25398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_25398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25398 prefixEnd_25398 := by exact prefixLift 25398
  have htrace : WordTrace (prefixWord ++ tailWord_25398) baseStart_25398 baseEnd_25398 := by
    simpa [prefixWord, tailWord_25398, baseEnd_25398] using wordTrace_append hprefix tailTrace_25398
  have hstable : (prefixWord ++ tailWord_25398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25398).length < 2 ^ (prefixWord ++ tailWord_25398).sum := by decide
  have hdescent : baseEnd_25398 < baseStart_25398 := by decide
  rcases family_descends (prefixWord ++ tailWord_25398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25405 : List Nat := [1, 4, 1, 4, 2, 1, 1, 3, 3]
def baseStart_25405 : Nat := 118140960795 + 25405 * 2 ^ 59
def prefixEnd_25405 : Nat := 4983230072969 + 3 ^ 40 * 25405 * 2
def baseEnd_25405 : Nat := 11595534246736299129485

theorem tailTrace_25405 : CollatzResearch.WordTrace tailWord_25405 prefixEnd_25405 11595534246736299129485 := by
  unfold tailWord_25405
  simp only [CollatzResearch.WordTrace]
  refine ⟨926596472969498673677669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 617730981979665782451779 926596472969498673677669)
  ·
    refine ⟨173736838681781001314563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 926596472969498673677669 173736838681781001314563)
    ·
      refine ⟨260605258022671501971845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173736838681781001314563 260605258022671501971845)
      ·
        refine ⟨48863485879250906619721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260605258022671501971845 48863485879250906619721)
        ·
          refine ⟨36647614409438179964791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48863485879250906619721 36647614409438179964791)
          ·
            refine ⟨54971421614157269947187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36647614409438179964791 54971421614157269947187)
            ·
              refine ⟨82457132421235904920781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54971421614157269947187 82457132421235904920781)
              ·
                refine ⟨30921424657963464345293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82457132421235904920781 30921424657963464345293)
                ·
                  refine ⟨11595534246736299129485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30921424657963464345293 11595534246736299129485)
                  ·
                    rfl

theorem cell20_25405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_25405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25405 prefixEnd_25405 := by exact prefixLift 25405
  have htrace : WordTrace (prefixWord ++ tailWord_25405) baseStart_25405 baseEnd_25405 := by
    simpa [prefixWord, tailWord_25405, baseEnd_25405] using wordTrace_append hprefix tailTrace_25405
  have hstable : (prefixWord ++ tailWord_25405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25405).length < 2 ^ (prefixWord ++ tailWord_25405).sum := by decide
  have hdescent : baseEnd_25405 < baseStart_25405 := by decide
  rcases family_descends (prefixWord ++ tailWord_25405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25416 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 6]
def baseStart_25416 : Nat := 118140960795 + 25416 * 2 ^ 59
def prefixEnd_25416 : Nat := 4983230072969 + 3 ^ 40 * 25416 * 2
def baseEnd_25416 : Nat := 11600554946469149762773

theorem tailTrace_25416 : CollatzResearch.WordTrace tailWord_25416 prefixEnd_25416 11600554946469149762773 := by
  unfold tailWord_25416
  simp only [CollatzResearch.WordTrace]
  refine ⟨463498837964823776164051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 617998450619765034885401 463498837964823776164051)
  ·
    refine ⟨695248256947235664246077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 463498837964823776164051 695248256947235664246077)
    ·
      refine ⟨260718096355213374092279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 695248256947235664246077 260718096355213374092279)
      ·
        refine ⟨391077144532820061138419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260718096355213374092279 391077144532820061138419)
        ·
          refine ⟨586615716799230091707629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391077144532820061138419 586615716799230091707629)
          ·
            refine ⟨219980893799711284390361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 586615716799230091707629 219980893799711284390361)
            ·
              refine ⟨164985670349783463292771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219980893799711284390361 164985670349783463292771)
              ·
                refine ⟨247478505524675194939157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164985670349783463292771 247478505524675194939157)
                ·
                  refine ⟨11600554946469149762773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 247478505524675194939157 11600554946469149762773)
                  ·
                    rfl

theorem cell20_25416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_25416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25416 prefixEnd_25416 := by exact prefixLift 25416
  have htrace : WordTrace (prefixWord ++ tailWord_25416) baseStart_25416 baseEnd_25416 := by
    simpa [prefixWord, tailWord_25416, baseEnd_25416] using wordTrace_append hprefix tailTrace_25416
  have hstable : (prefixWord ++ tailWord_25416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25416).length < 2 ^ (prefixWord ++ tailWord_25416).sum := by decide
  have hdescent : baseEnd_25416 < baseStart_25416 := by decide
  rcases family_descends (prefixWord ++ tailWord_25416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25498 : List Nat := [3, 1, 1, 4, 4, 1, 1, 2, 3]
def baseStart_25498 : Nat := 118140960795 + 25498 * 2 ^ 59
def prefixEnd_25498 : Nat := 4983230072969 + 3 ^ 40 * 25498 * 2
def baseEnd_25498 : Nat := 11637981980841309029105

theorem tailTrace_25498 : CollatzResearch.WordTrace tailWord_25498 prefixEnd_25498 11637981980841309029105 := by
  unfold tailWord_25498
  simp only [CollatzResearch.WordTrace]
  refine ⟨232497115408143889203287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 619992307755050371208765 232497115408143889203287)
  ·
    refine ⟨348745673112215833804931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232497115408143889203287 348745673112215833804931)
    ·
      refine ⟨523118509668323750707397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348745673112215833804931 523118509668323750707397)
      ·
        refine ⟨98084720562810703257637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 523118509668323750707397 98084720562810703257637)
        ·
          refine ⟨18390885105527006860807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98084720562810703257637 18390885105527006860807)
          ·
            refine ⟨27586327658290510291211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18390885105527006860807 27586327658290510291211)
            ·
              refine ⟨41379491487435765436817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27586327658290510291211 41379491487435765436817)
              ·
                refine ⟨31034618615576824077613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41379491487435765436817 31034618615576824077613)
                ·
                  refine ⟨11637981980841309029105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31034618615576824077613 11637981980841309029105)
                  ·
                    rfl

theorem cell20_25498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 3].length) (baseStart_25498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25498 prefixEnd_25498 := by exact prefixLift 25498
  have htrace : WordTrace (prefixWord ++ tailWord_25498) baseStart_25498 baseEnd_25498 := by
    simpa [prefixWord, tailWord_25498, baseEnd_25498] using wordTrace_append hprefix tailTrace_25498
  have hstable : (prefixWord ++ tailWord_25498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25498).length < 2 ^ (prefixWord ++ tailWord_25498).sum := by decide
  have hdescent : baseEnd_25498 < baseStart_25498 := by decide
  rcases family_descends (prefixWord ++ tailWord_25498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25530 : List Nat := [3, 1, 1, 1, 2, 1, 3, 4, 4]
def baseStart_25530 : Nat := 118140960795 + 25530 * 2 ^ 59
def prefixEnd_25530 : Nat := 4983230072969 + 3 ^ 40 * 25530 * 2
def baseEnd_25530 : Nat := 11652587652791419962307

theorem tailTrace_25530 : CollatzResearch.WordTrace tailWord_25530 prefixEnd_25530 11652587652791419962307 := by
  unfold tailWord_25530
  simp only [CollatzResearch.WordTrace]
  refine ⟨232788899379161255494511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 620770398344430014652029 232788899379161255494511)
  ·
    refine ⟨349183349068741883241767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232788899379161255494511 349183349068741883241767)
    ·
      refine ⟨523775023603112824862651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349183349068741883241767 523775023603112824862651)
      ·
        refine ⟨785662535404669237293977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523775023603112824862651 785662535404669237293977)
        ·
          refine ⟨589246901553501927970483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 785662535404669237293977 589246901553501927970483)
          ·
            refine ⟨883870352330252891955725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589246901553501927970483 883870352330252891955725)
            ·
              refine ⟨331451382123844834483397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 883870352330252891955725 331451382123844834483397)
              ·
                refine ⟨62147134148220906465637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 331451382123844834483397 62147134148220906465637)
                ·
                  refine ⟨11652587652791419962307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62147134148220906465637 11652587652791419962307)
                  ·
                    rfl

theorem cell20_25530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_25530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25530 prefixEnd_25530 := by exact prefixLift 25530
  have htrace : WordTrace (prefixWord ++ tailWord_25530) baseStart_25530 baseEnd_25530 := by
    simpa [prefixWord, tailWord_25530, baseEnd_25530] using wordTrace_append hprefix tailTrace_25530
  have hstable : (prefixWord ++ tailWord_25530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25530).length < 2 ^ (prefixWord ++ tailWord_25530).sum := by decide
  have hdescent : baseEnd_25530 < baseStart_25530 := by decide
  rcases family_descends (prefixWord ++ tailWord_25530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25554 : List Nat := [3, 2, 2, 3, 1, 1, 8]
def baseStart_25554 : Nat := 118140960795 + 25554 * 2 ^ 59
def prefixEnd_25554 : Nat := 4983230072969 + 3 ^ 40 * 25554 * 2
def baseEnd_25554 : Nat := 1295949100750444795801

theorem tailTrace_25554 : CollatzResearch.WordTrace tailWord_25554 prefixEnd_25554 1295949100750444795801 := by
  unfold tailWord_25554
  simp only [CollatzResearch.WordTrace]
  refine ⟨233007737357424280212929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 621353966286464747234477 233007737357424280212929)
  ·
    refine ⟨174755803018068210159697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233007737357424280212929 174755803018068210159697)
    ·
      refine ⟨131066852263551157619773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174755803018068210159697 131066852263551157619773)
      ·
        refine ⟨49150069598831684107415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131066852263551157619773 49150069598831684107415)
        ·
          refine ⟨73725104398247526161123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49150069598831684107415 73725104398247526161123)
          ·
            refine ⟨110587656597371289241685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73725104398247526161123 110587656597371289241685)
            ·
              refine ⟨1295949100750444795801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 110587656597371289241685 1295949100750444795801)
              ·
                rfl

theorem cell20_25554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 8].length) (baseStart_25554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25554 prefixEnd_25554 := by exact prefixLift 25554
  have htrace : WordTrace (prefixWord ++ tailWord_25554) baseStart_25554 baseEnd_25554 := by
    simpa [prefixWord, tailWord_25554, baseEnd_25554] using wordTrace_append hprefix tailTrace_25554
  have hstable : (prefixWord ++ tailWord_25554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25554).length < 2 ^ (prefixWord ++ tailWord_25554).sum := by decide
  have hdescent : baseEnd_25554 < baseStart_25554 := by decide
  rcases family_descends (prefixWord ++ tailWord_25554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25561 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 5]
def baseStart_25561 : Nat := 118140960795 + 25561 * 2 ^ 59
def prefixEnd_25561 : Nat := 4983230072969 + 3 ^ 40 * 25561 * 2
def baseEnd_25561 : Nat := 11666736897493089928847

theorem tailTrace_25561 : CollatzResearch.WordTrace tailWord_25561 prefixEnd_25561 11666736897493089928847 := by
  unfold tailWord_25561
  simp only [CollatzResearch.WordTrace]
  refine ⟨932286260404337316356537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 621524173602891544237691 932286260404337316356537)
  ·
    refine ⟨699214695303252987267403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 932286260404337316356537 699214695303252987267403)
    ·
      refine ⟨1048822042954879480901105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 699214695303252987267403 1048822042954879480901105)
      ·
        refine ⟨786616532216159610675829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1048822042954879480901105 786616532216159610675829)
        ·
          refine ⟨73745299895264963500859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 786616532216159610675829 73745299895264963500859)
          ·
            refine ⟨110617949842897445251289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73745299895264963500859 110617949842897445251289)
            ·
              refine ⟨82963462382173083938467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110617949842897445251289 82963462382173083938467)
              ·
                refine ⟨124445193573259625907701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82963462382173083938467 124445193573259625907701)
                ·
                  refine ⟨11666736897493089928847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124445193573259625907701 11666736897493089928847)
                  ·
                    rfl

theorem cell20_25561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_25561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25561 prefixEnd_25561 := by exact prefixLift 25561
  have htrace : WordTrace (prefixWord ++ tailWord_25561) baseStart_25561 baseEnd_25561 := by
    simpa [prefixWord, tailWord_25561, baseEnd_25561] using wordTrace_append hprefix tailTrace_25561
  have hstable : (prefixWord ++ tailWord_25561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25561).length < 2 ^ (prefixWord ++ tailWord_25561).sum := by decide
  have hdescent : baseEnd_25561 < baseStart_25561 := by decide
  rcases family_descends (prefixWord ++ tailWord_25561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25578 : List Nat := [3, 1, 3, 1, 2, 3, 1, 3, 3]
def baseStart_25578 : Nat := 118140960795 + 25578 * 2 ^ 59
def prefixEnd_25578 : Nat := 4983230072969 + 3 ^ 40 * 25578 * 2
def baseEnd_25578 : Nat := 11674496160716586362111

theorem tailTrace_25578 : CollatzResearch.WordTrace tailWord_25578 prefixEnd_25578 11674496160716586362111 := by
  unfold tailWord_25578
  simp only [CollatzResearch.WordTrace]
  refine ⟨233226575335687304931347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 621937534228499479816925 233226575335687304931347)
  ·
    refine ⟨349839863003530957397021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233226575335687304931347 349839863003530957397021)
    ·
      refine ⟨131189948626324109023883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349839863003530957397021 131189948626324109023883)
      ·
        refine ⟨196784922939486163535825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131189948626324109023883 196784922939486163535825)
        ·
          refine ⟨147588692204614622651869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196784922939486163535825 147588692204614622651869)
          ·
            refine ⟨55345759576730483494451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147588692204614622651869 55345759576730483494451)
            ·
              refine ⟨83018639365095725241677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55345759576730483494451 83018639365095725241677)
              ·
                refine ⟨31131989761910896965629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83018639365095725241677 31131989761910896965629)
                ·
                  refine ⟨11674496160716586362111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31131989761910896965629 11674496160716586362111)
                  ·
                    rfl

theorem cell20_25578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_25578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25578 prefixEnd_25578 := by exact prefixLift 25578
  have htrace : WordTrace (prefixWord ++ tailWord_25578) baseStart_25578 baseEnd_25578 := by
    simpa [prefixWord, tailWord_25578, baseEnd_25578] using wordTrace_append hprefix tailTrace_25578
  have hstable : (prefixWord ++ tailWord_25578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25578).length < 2 ^ (prefixWord ++ tailWord_25578).sum := by decide
  have hdescent : baseEnd_25578 < baseStart_25578 := by decide
  rcases family_descends (prefixWord ++ tailWord_25578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25637 : List Nat := [1, 3, 1, 2, 2, 2, 1, 5, 3]
def baseStart_25637 : Nat := 118140960795 + 25637 * 2 ^ 59
def prefixEnd_25637 : Nat := 4983230072969 + 3 ^ 40 * 25637 * 2
def baseEnd_25637 : Nat := 11701425368374603395203

theorem tailTrace_25637 : CollatzResearch.WordTrace tailWord_25637 prefixEnd_25637 11701425368374603395203 := by
  unfold tailWord_25637
  simp only [CollatzResearch.WordTrace]
  refine ⟨935058208129002296123165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 623372138752668197415443 935058208129002296123165)
  ·
    refine ⟨350646828048375861046187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 935058208129002296123165 350646828048375861046187)
    ·
      refine ⟨525970242072563791569281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350646828048375861046187 525970242072563791569281)
      ·
        refine ⟨394477681554422843676961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 525970242072563791569281 394477681554422843676961)
        ·
          refine ⟨295858261165817132757721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394477681554422843676961 295858261165817132757721)
          ·
            refine ⟨221893695874362849568291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295858261165817132757721 221893695874362849568291)
            ·
              refine ⟨332840543811544274352437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221893695874362849568291 332840543811544274352437)
              ·
                refine ⟨31203800982332275720541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 332840543811544274352437 31203800982332275720541)
                ·
                  refine ⟨11701425368374603395203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31203800982332275720541 11701425368374603395203)
                  ·
                    rfl

theorem cell20_25637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_25637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25637 prefixEnd_25637 := by exact prefixLift 25637
  have htrace : WordTrace (prefixWord ++ tailWord_25637) baseStart_25637 baseEnd_25637 := by
    simpa [prefixWord, tailWord_25637, baseEnd_25637] using wordTrace_append hprefix tailTrace_25637
  have hstable : (prefixWord ++ tailWord_25637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25637).length < 2 ^ (prefixWord ++ tailWord_25637).sum := by decide
  have hdescent : baseEnd_25637 < baseStart_25637 := by decide
  rcases family_descends (prefixWord ++ tailWord_25637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25644 : List Nat := [2, 2, 1, 1, 1, 2, 5, 2, 4]
def baseStart_25644 : Nat := 118140960795 + 25644 * 2 ^ 59
def prefixEnd_25644 : Nat := 4983230072969 + 3 ^ 40 * 25644 * 2
def baseEnd_25644 : Nat := 11704620359113690161841

theorem tailTrace_25644 : CollatzResearch.WordTrace tailWord_25644 prefixEnd_25644 11704620359113690161841 := by
  unfold tailWord_25644
  simp only [CollatzResearch.WordTrace]
  refine ⟨467656759551821245813993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 623542346069094994418657 467656759551821245813993)
  ·
    refine ⟨350742569663865934360495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 467656759551821245813993 350742569663865934360495)
    ·
      refine ⟨526113854495798901540743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350742569663865934360495 526113854495798901540743)
      ·
        refine ⟨789170781743698352311115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526113854495798901540743 789170781743698352311115)
        ·
          refine ⟨1183756172615547528466673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789170781743698352311115 1183756172615547528466673)
          ·
            refine ⟨887817129461660646350005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1183756172615547528466673 887817129461660646350005)
            ·
              refine ⟨83232855887030685595313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 887817129461660646350005 83232855887030685595313)
              ·
                refine ⟨62424641915273014196485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83232855887030685595313 62424641915273014196485)
                ·
                  refine ⟨11704620359113690161841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62424641915273014196485 11704620359113690161841)
                  ·
                    rfl

theorem cell20_25644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_25644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25644 prefixEnd_25644 := by exact prefixLift 25644
  have htrace : WordTrace (prefixWord ++ tailWord_25644) baseStart_25644 baseEnd_25644 := by
    simpa [prefixWord, tailWord_25644, baseEnd_25644] using wordTrace_append hprefix tailTrace_25644
  have hstable : (prefixWord ++ tailWord_25644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25644).length < 2 ^ (prefixWord ++ tailWord_25644).sum := by decide
  have hdescent : baseEnd_25644 < baseStart_25644 := by decide
  rcases family_descends (prefixWord ++ tailWord_25644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25706 : List Nat := [3, 1, 3, 2, 2, 2, 1, 6]
def baseStart_25706 : Nat := 118140960795 + 25706 * 2 ^ 59
def prefixEnd_25706 : Nat := 4983230072969 + 3 ^ 40 * 25706 * 2
def baseEnd_25706 : Nat := 3910972949505676698307

theorem tailTrace_25706 : CollatzResearch.WordTrace tailWord_25706 prefixEnd_25706 3910972949505676698307 := by
  unfold tailWord_25706
  simp only [CollatzResearch.WordTrace]
  refine ⟨234393711219756770096243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 625049896586018053589981 234393711219756770096243)
  ·
    refine ⟨351590566829635155144365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234393711219756770096243 351590566829635155144365)
    ·
      refine ⟨131846462561113183179137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351590566829635155144365 131846462561113183179137)
      ·
        refine ⟨98884846920834887384353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131846462561113183179137 98884846920834887384353)
        ·
          refine ⟨74163635190626165538265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98884846920834887384353 74163635190626165538265)
          ·
            refine ⟨55622726392969624153699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74163635190626165538265 55622726392969624153699)
            ·
              refine ⟨83434089589454436230549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55622726392969624153699 83434089589454436230549)
              ·
                refine ⟨3910972949505676698307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83434089589454436230549 3910972949505676698307)
                ·
                  rfl

theorem cell20_25706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_25706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25706 prefixEnd_25706 := by exact prefixLift 25706
  have htrace : WordTrace (prefixWord ++ tailWord_25706) baseStart_25706 baseEnd_25706 := by
    simpa [prefixWord, tailWord_25706, baseEnd_25706] using wordTrace_append hprefix tailTrace_25706
  have hstable : (prefixWord ++ tailWord_25706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25706).length < 2 ^ (prefixWord ++ tailWord_25706).sum := by decide
  have hdescent : baseEnd_25706 < baseStart_25706 := by decide
  rcases family_descends (prefixWord ++ tailWord_25706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25733 : List Nat := [1, 3, 1, 1, 6, 1, 3, 2, 2]
def baseStart_25733 : Nat := 118140960795 + 25733 * 2 ^ 59
def prefixEnd_25733 : Nat := 4983230072969 + 3 ^ 40 * 25733 * 2
def baseEnd_25733 : Nat := 11745242384224936194811

theorem tailTrace_25733 : CollatzResearch.WordTrace tailWord_25733 prefixEnd_25733 11745242384224936194811 := by
  unfold tailWord_25733
  simp only [CollatzResearch.WordTrace]
  refine ⟨938559615781210691617853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 625706410520807127745235 938559615781210691617853)
  ·
    refine ⟨351959855917954009356695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 938559615781210691617853 351959855917954009356695)
    ·
      refine ⟨527939783876931014035043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351959855917954009356695 527939783876931014035043)
      ·
        refine ⟨791909675815396521052565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527939783876931014035043 791909675815396521052565)
        ·
          refine ⟨37120766053846711924339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 791909675815396521052565 37120766053846711924339)
          ·
            refine ⟨55681149080770067886509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37120766053846711924339 55681149080770067886509)
            ·
              refine ⟨20880430905288775457441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55681149080770067886509 20880430905288775457441)
              ·
                refine ⟨15660323178966581593081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20880430905288775457441 15660323178966581593081)
                ·
                  refine ⟨11745242384224936194811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15660323178966581593081 11745242384224936194811)
                  ·
                    rfl

theorem cell20_25733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 2].length) (baseStart_25733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25733 prefixEnd_25733 := by exact prefixLift 25733
  have htrace : WordTrace (prefixWord ++ tailWord_25733) baseStart_25733 baseEnd_25733 := by
    simpa [prefixWord, tailWord_25733, baseEnd_25733] using wordTrace_append hprefix tailTrace_25733
  have hstable : (prefixWord ++ tailWord_25733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25733).length < 2 ^ (prefixWord ++ tailWord_25733).sum := by decide
  have hdescent : baseEnd_25733 < baseStart_25733 := by decide
  rcases family_descends (prefixWord ++ tailWord_25733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25737 : List Nat := [1, 2, 1, 1, 4, 5, 1, 1, 4]
def baseStart_25737 : Nat := 118140960795 + 25737 * 2 ^ 59
def prefixEnd_25737 : Nat := 4983230072969 + 3 ^ 40 * 25737 * 2
def baseEnd_25737 : Nat := 11747068093218700061461

theorem tailTrace_25737 : CollatzResearch.WordTrace tailWord_25737 prefixEnd_25737 11747068093218700061461 := by
  unfold tailWord_25737
  simp only [CollatzResearch.WordTrace]
  refine ⟨938705507766719374763465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 625803671844479583175643 938705507766719374763465)
  ·
    refine ⟨704029130825039531072599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 938705507766719374763465 704029130825039531072599)
    ·
      refine ⟨1056043696237559296608899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 704029130825039531072599 1056043696237559296608899)
      ·
        refine ⟨1584065544356338944913349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1056043696237559296608899 1584065544356338944913349)
        ·
          refine ⟨297012289566813552171253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1584065544356338944913349 297012289566813552171253)
          ·
            refine ⟨27844902146888770516055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 297012289566813552171253 27844902146888770516055)
            ·
              refine ⟨41767353220333155774083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27844902146888770516055 41767353220333155774083)
              ·
                refine ⟨62651029830499733661125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41767353220333155774083 62651029830499733661125)
                ·
                  refine ⟨11747068093218700061461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62651029830499733661125 11747068093218700061461)
                  ·
                    rfl

theorem cell20_25737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 4].length) (baseStart_25737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25737 prefixEnd_25737 := by exact prefixLift 25737
  have htrace : WordTrace (prefixWord ++ tailWord_25737) baseStart_25737 baseEnd_25737 := by
    simpa [prefixWord, tailWord_25737, baseEnd_25737] using wordTrace_append hprefix tailTrace_25737
  have hstable : (prefixWord ++ tailWord_25737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25737).length < 2 ^ (prefixWord ++ tailWord_25737).sum := by decide
  have hdescent : baseEnd_25737 < baseStart_25737 := by decide
  rcases family_descends (prefixWord ++ tailWord_25737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25765 : List Nat := [1, 3, 1, 2, 1, 4, 2, 6]
def baseStart_25765 : Nat := 118140960795 + 25765 * 2 ^ 59
def prefixEnd_25765 : Nat := 4983230072969 + 3 ^ 40 * 25765 * 2
def baseEnd_25765 : Nat := 3919949352058349042671

theorem tailTrace_25765 : CollatzResearch.WordTrace tailWord_25765 prefixEnd_25765 3919949352058349042671 := by
  unfold tailWord_25765
  simp only [CollatzResearch.WordTrace]
  refine ⟨939726751665280156782749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 626484501110186771188499 939726751665280156782749)
  ·
    refine ⟨352397531874480058793531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 939726751665280156782749 352397531874480058793531)
    ·
      refine ⟨528596297811720088190297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352397531874480058793531 528596297811720088190297)
      ·
        refine ⟨396447223358790066142723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 528596297811720088190297 396447223358790066142723)
        ·
          refine ⟨594670835038185099214085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396447223358790066142723 594670835038185099214085)
          ·
            refine ⟨111500781569659706102641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 594670835038185099214085 111500781569659706102641)
            ·
              refine ⟨83625586177244779576981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111500781569659706102641 83625586177244779576981)
              ·
                refine ⟨3919949352058349042671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83625586177244779576981 3919949352058349042671)
                ·
                  rfl

theorem cell20_25765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 6].length) (baseStart_25765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25765 prefixEnd_25765 := by exact prefixLift 25765
  have htrace : WordTrace (prefixWord ++ tailWord_25765) baseStart_25765 baseEnd_25765 := by
    simpa [prefixWord, tailWord_25765, baseEnd_25765] using wordTrace_append hprefix tailTrace_25765
  have hstable : (prefixWord ++ tailWord_25765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25765).length < 2 ^ (prefixWord ++ tailWord_25765).sum := by decide
  have hdescent : baseEnd_25765 < baseStart_25765 := by decide
  rcases family_descends (prefixWord ++ tailWord_25765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25772 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 5]
def baseStart_25772 : Nat := 118140960795 + 25772 * 2 ^ 59
def prefixEnd_25772 : Nat := 4983230072969 + 3 ^ 40 * 25772 * 2
def baseEnd_25772 : Nat := 11763043046914133894651

theorem tailTrace_25772 : CollatzResearch.WordTrace tailWord_25772 prefixEnd_25772 11763043046914133894651 := by
  unfold tailWord_25772
  simp only [CollatzResearch.WordTrace]
  refine ⟨469991031319960176143785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 626654708426613568191713 469991031319960176143785)
  ·
    refine ⟨352493273489970132107839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 469991031319960176143785 352493273489970132107839)
    ·
      refine ⟨528739910234955198161759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352493273489970132107839 528739910234955198161759)
      ·
        refine ⟨793109865352432797242639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528739910234955198161759 793109865352432797242639)
        ·
          refine ⟨1189664798028649195863959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793109865352432797242639 1189664798028649195863959)
          ·
            refine ⟨1784497197042973793795939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189664798028649195863959 1784497197042973793795939)
            ·
              refine ⟨2676745795564460690693909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1784497197042973793795939 2676745795564460690693909)
              ·
                refine ⟨125472459167084094876277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2676745795564460690693909 125472459167084094876277)
                ·
                  refine ⟨11763043046914133894651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125472459167084094876277 11763043046914133894651)
                  ·
                    rfl

theorem cell20_25772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_25772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25772 prefixEnd_25772 := by exact prefixLift 25772
  have htrace : WordTrace (prefixWord ++ tailWord_25772) baseStart_25772 baseEnd_25772 := by
    simpa [prefixWord, tailWord_25772, baseEnd_25772] using wordTrace_append hprefix tailTrace_25772
  have hstable : (prefixWord ++ tailWord_25772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25772).length < 2 ^ (prefixWord ++ tailWord_25772).sum := by decide
  have hdescent : baseEnd_25772 < baseStart_25772 := by decide
  rcases family_descends (prefixWord ++ tailWord_25772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25789 : List Nat := [1, 4, 1, 2, 1, 1, 3, 4, 3]
def baseStart_25789 : Nat := 118140960795 + 25789 * 2 ^ 59
def prefixEnd_25789 : Nat := 4983230072969 + 3 ^ 40 * 25789 * 2
def baseEnd_25789 : Nat := 11770802310137630327915

theorem tailTrace_25789 : CollatzResearch.WordTrace tailWord_25789 prefixEnd_25789 11770802310137630327915 := by
  unfold tailWord_25789
  simp only [CollatzResearch.WordTrace]
  refine ⟨940602103578332255656421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 627068069052221503770947 940602103578332255656421)
  ·
    refine ⟨176362894420937297935579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 940602103578332255656421 176362894420937297935579)
    ·
      refine ⟨264544341631405946903369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176362894420937297935579 264544341631405946903369)
      ·
        refine ⟨198408256223554460177527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264544341631405946903369 198408256223554460177527)
        ·
          refine ⟨297612384335331690266291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198408256223554460177527 297612384335331690266291)
          ·
            refine ⟨446418576502997535399437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297612384335331690266291 446418576502997535399437)
            ·
              refine ⟨167406966188624075774789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 446418576502997535399437 167406966188624075774789)
              ·
                refine ⟨31388806160367014207773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167406966188624075774789 31388806160367014207773)
                ·
                  refine ⟨11770802310137630327915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31388806160367014207773 11770802310137630327915)
                  ·
                    rfl

theorem cell20_25789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_25789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25789 prefixEnd_25789 := by exact prefixLift 25789
  have htrace : WordTrace (prefixWord ++ tailWord_25789) baseStart_25789 baseEnd_25789 := by
    simpa [prefixWord, tailWord_25789, baseEnd_25789] using wordTrace_append hprefix tailTrace_25789
  have hstable : (prefixWord ++ tailWord_25789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25789).length < 2 ^ (prefixWord ++ tailWord_25789).sum := by decide
  have hdescent : baseEnd_25789 < baseStart_25789 := by decide
  rcases family_descends (prefixWord ++ tailWord_25789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25792 : List Nat := [2, 1, 1, 2, 6, 1, 1, 4, 2]
def baseStart_25792 : Nat := 118140960795 + 25792 * 2 ^ 59
def prefixEnd_25792 : Nat := 4983230072969 + 3 ^ 40 * 25792 * 2
def baseEnd_25792 : Nat := 11772171591882953227903

theorem tailTrace_25792 : CollatzResearch.WordTrace tailWord_25792 prefixEnd_25792 11772171591882953227903 := by
  unfold tailWord_25792
  simp only [CollatzResearch.WordTrace]
  refine ⟨470355761283731884007815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 627141015044975845343753 470355761283731884007815)
  ·
    refine ⟨705533641925597826011723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 470355761283731884007815 705533641925597826011723)
    ·
      refine ⟨1058300462888396739017585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 705533641925597826011723 1058300462888396739017585)
      ·
        refine ⟨793725347166297554263189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1058300462888396739017585 793725347166297554263189)
        ·
          refine ⟨37205875648420197856087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 793725347166297554263189 37205875648420197856087)
          ·
            refine ⟨55808813472630296784131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37205875648420197856087 55808813472630296784131)
            ·
              refine ⟨83713220208945445176197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55808813472630296784131 83713220208945445176197)
              ·
                refine ⟨15696228789177270970537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83713220208945445176197 15696228789177270970537)
                ·
                  refine ⟨11772171591882953227903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15696228789177270970537 11772171591882953227903)
                  ·
                    rfl

theorem cell20_25792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 2].length) (baseStart_25792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25792 prefixEnd_25792 := by exact prefixLift 25792
  have htrace : WordTrace (prefixWord ++ tailWord_25792) baseStart_25792 baseEnd_25792 := by
    simpa [prefixWord, tailWord_25792, baseEnd_25792] using wordTrace_append hprefix tailTrace_25792
  have hstable : (prefixWord ++ tailWord_25792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25792).length < 2 ^ (prefixWord ++ tailWord_25792).sum := by decide
  have hdescent : baseEnd_25792 < baseStart_25792 := by decide
  rcases family_descends (prefixWord ++ tailWord_25792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25813 : List Nat := [1, 3, 2, 4, 1, 2, 1, 2, 4]
def baseStart_25813 : Nat := 118140960795 + 25813 * 2 ^ 59
def prefixEnd_25813 : Nat := 4983230072969 + 3 ^ 40 * 25813 * 2
def baseEnd_25813 : Nat := 11781756564100213527817

theorem tailTrace_25813 : CollatzResearch.WordTrace tailWord_25813 prefixEnd_25813 11781756564100213527817 := by
  unfold tailWord_25813
  simp only [CollatzResearch.WordTrace]
  refine ⟨941477455491384354530093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 627651636994256236353395 941477455491384354530093)
  ·
    refine ⟨353054045809269132948785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 941477455491384354530093 353054045809269132948785)
    ·
      refine ⟨264790534356951849711589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353054045809269132948785 264790534356951849711589)
      ·
        refine ⟨49648225191928471820923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264790534356951849711589 49648225191928471820923)
        ·
          refine ⟨74472337787892707731385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49648225191928471820923 74472337787892707731385)
          ·
            refine ⟨55854253340919530798539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74472337787892707731385 55854253340919530798539)
            ·
              refine ⟨83781380011379296197809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55854253340919530798539 83781380011379296197809)
              ·
                refine ⟨62836035008534472148357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83781380011379296197809 62836035008534472148357)
                ·
                  refine ⟨11781756564100213527817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62836035008534472148357 11781756564100213527817)
                  ·
                    rfl

theorem cell20_25813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_25813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25813 prefixEnd_25813 := by exact prefixLift 25813
  have htrace : WordTrace (prefixWord ++ tailWord_25813) baseStart_25813 baseEnd_25813 := by
    simpa [prefixWord, tailWord_25813, baseEnd_25813] using wordTrace_append hprefix tailTrace_25813
  have hstable : (prefixWord ++ tailWord_25813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25813).length < 2 ^ (prefixWord ++ tailWord_25813).sum := by decide
  have hdescent : baseEnd_25813 < baseStart_25813 := by decide
  rcases family_descends (prefixWord ++ tailWord_25813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25879 : List Nat := [1, 1, 3, 4, 1, 1, 3, 6]
def baseStart_25879 : Nat := 118140960795 + 25879 * 2 ^ 59
def prefixEnd_25879 : Nat := 4983230072969 + 3 ^ 40 * 25879 * 2
def baseEnd_25879 : Nat := 3937293587499105775849

theorem tailTrace_25879 : CollatzResearch.WordTrace tailWord_25879 prefixEnd_25879 3937293587499105775849 := by
  unfold tailWord_25879
  simp only [CollatzResearch.WordTrace]
  refine ⟨943884673252277626432691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 629256448834851750955127 943884673252277626432691)
  ·
    refine ⟨1415827009878416439649037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 943884673252277626432691 1415827009878416439649037)
    ·
      refine ⟨530935128704406164868389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1415827009878416439649037 530935128704406164868389)
      ·
        refine ⟨99550336632076155912823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 530935128704406164868389 99550336632076155912823)
        ·
          refine ⟨149325504948114233869235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99550336632076155912823 149325504948114233869235)
          ·
            refine ⟨223988257422171350803853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149325504948114233869235 223988257422171350803853)
            ·
              refine ⟨83995596533314256551445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223988257422171350803853 83995596533314256551445)
              ·
                refine ⟨3937293587499105775849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83995596533314256551445 3937293587499105775849)
                ·
                  rfl

theorem cell20_25879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 6].length) (baseStart_25879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25879 prefixEnd_25879 := by exact prefixLift 25879
  have htrace : WordTrace (prefixWord ++ tailWord_25879) baseStart_25879 baseEnd_25879 := by
    simpa [prefixWord, tailWord_25879, baseEnd_25879] using wordTrace_append hprefix tailTrace_25879
  have hstable : (prefixWord ++ tailWord_25879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25879).length < 2 ^ (prefixWord ++ tailWord_25879).sum := by decide
  have hdescent : baseEnd_25879 < baseStart_25879 := by decide
  rcases family_descends (prefixWord ++ tailWord_25879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25885 : List Nat := [1, 4, 2, 3, 1, 3, 1, 3, 2]
def baseStart_25885 : Nat := 118140960795 + 25885 * 2 ^ 59
def prefixEnd_25885 : Nat := 4983230072969 + 3 ^ 40 * 25885 * 2
def baseEnd_25885 : Nat := 11814619325987963127523

theorem tailTrace_25885 : CollatzResearch.WordTrace tailWord_25885 prefixEnd_25885 11814619325987963127523 := by
  unfold tailWord_25885
  simp only [CollatzResearch.WordTrace]
  refine ⟨944103511230540651151109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 629402340820360434100739 944103511230540651151109)
  ·
    refine ⟨177019408355726372090833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 944103511230540651151109 177019408355726372090833)
    ·
      refine ⟨132764556266794779068125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177019408355726372090833 132764556266794779068125)
      ·
        refine ⟨49786708600048042150547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132764556266794779068125 49786708600048042150547)
        ·
          refine ⟨74680062900072063225821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49786708600048042150547 74680062900072063225821)
          ·
            refine ⟨28005023587527023709683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74680062900072063225821 28005023587527023709683)
            ·
              refine ⟨42007535381290535564525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28005023587527023709683 42007535381290535564525)
              ·
                refine ⟨15752825767983950836697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42007535381290535564525 15752825767983950836697)
                ·
                  refine ⟨11814619325987963127523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15752825767983950836697 11814619325987963127523)
                  ·
                    rfl

theorem cell20_25885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_25885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25885 prefixEnd_25885 := by exact prefixLift 25885
  have htrace : WordTrace (prefixWord ++ tailWord_25885) baseStart_25885 baseEnd_25885 := by
    simpa [prefixWord, tailWord_25885, baseEnd_25885] using wordTrace_append hprefix tailTrace_25885
  have hstable : (prefixWord ++ tailWord_25885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25885).length < 2 ^ (prefixWord ++ tailWord_25885).sum := by decide
  have hdescent : baseEnd_25885 < baseStart_25885 := by decide
  rcases family_descends (prefixWord ++ tailWord_25885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25896 : List Nat := [2, 1, 5, 1, 2, 3, 6]
def baseStart_25896 : Nat := 118140960795 + 25896 * 2 ^ 59
def prefixEnd_25896 : Nat := 4983230072969 + 3 ^ 40 * 25896 * 2
def baseEnd_25896 : Nat := 1313293336191201528979

theorem tailTrace_25896 : CollatzResearch.WordTrace tailWord_25896 prefixEnd_25896 1313293336191201528979 := by
  unfold tailWord_25896
  simp only [CollatzResearch.WordTrace]
  refine ⟨472252357095344764900771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 629669809460459686534361 472252357095344764900771)
  ·
    refine ⟨708378535643017147351157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 472252357095344764900771 708378535643017147351157)
    ·
      refine ⟨66410487716532857564171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 708378535643017147351157 66410487716532857564171)
      ·
        refine ⟨99615731574799286346257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66410487716532857564171 99615731574799286346257)
        ·
          refine ⟨74711798681099464759693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99615731574799286346257 74711798681099464759693)
          ·
            refine ⟨28016924505412299284885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74711798681099464759693 28016924505412299284885)
            ·
              refine ⟨1313293336191201528979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28016924505412299284885 1313293336191201528979)
              ·
                rfl

theorem cell20_25896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 6].length) (baseStart_25896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_25896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_25896 prefixEnd_25896 := by exact prefixLift 25896
  have htrace : WordTrace (prefixWord ++ tailWord_25896) baseStart_25896 baseEnd_25896 := by
    simpa [prefixWord, tailWord_25896, baseEnd_25896] using wordTrace_append hprefix tailTrace_25896
  have hstable : (prefixWord ++ tailWord_25896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25896).length < 2 ^ (prefixWord ++ tailWord_25896).sum := by decide
  have hdescent : baseEnd_25896 < baseStart_25896 := by decide
  rcases family_descends (prefixWord ++ tailWord_25896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26007 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 8]
def baseStart_26007 : Nat := 118140960795 + 26007 * 2 ^ 59
def prefixEnd_26007 : Nat := 4983230072969 + 3 ^ 40 * 26007 * 2
def baseEnd_26007 : Nat := 11870303450297761060357

theorem tailTrace_26007 : CollatzResearch.WordTrace tailWord_26007 prefixEnd_26007 11870303450297761060357 := by
  unfold tailWord_26007
  simp only [CollatzResearch.WordTrace]
  refine ⟨948553216788555487092275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 632368811192370324728183 948553216788555487092275)
  ·
    refine ⟨1422829825182833230638413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 948553216788555487092275 1422829825182833230638413)
    ·
      refine ⟨533561184443562461489405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1422829825182833230638413 533561184443562461489405)
      ·
        refine ⟨200085444166335923058527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 533561184443562461489405 200085444166335923058527)
        ·
          refine ⟨300128166249503884587791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200085444166335923058527 300128166249503884587791)
          ·
            refine ⟨450192249374255826881687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300128166249503884587791 450192249374255826881687)
            ·
              refine ⟨675288374061383740322531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450192249374255826881687 675288374061383740322531)
              ·
                refine ⟨1012932561092075610483797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675288374061383740322531 1012932561092075610483797)
                ·
                  refine ⟨11870303450297761060357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1012932561092075610483797 11870303450297761060357)
                  ·
                    rfl

theorem cell20_26007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_26007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26007 prefixEnd_26007 := by exact prefixLift 26007
  have htrace : WordTrace (prefixWord ++ tailWord_26007) baseStart_26007 baseEnd_26007 := by
    simpa [prefixWord, tailWord_26007, baseEnd_26007] using wordTrace_append hprefix tailTrace_26007
  have hstable : (prefixWord ++ tailWord_26007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26007).length < 2 ^ (prefixWord ++ tailWord_26007).sum := by decide
  have hdescent : baseEnd_26007 < baseStart_26007 := by decide
  rcases family_descends (prefixWord ++ tailWord_26007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26044 : List Nat := [2, 2, 2, 4, 3, 1, 2, 4]
def baseStart_26044 : Nat := 118140960795 + 26044 * 2 ^ 59
def prefixEnd_26044 : Nat := 4983230072969 + 3 ^ 40 * 26044 * 2
def baseEnd_26044 : Nat := 3962397086163358942291

theorem tailTrace_26044 : CollatzResearch.WordTrace tailWord_26044 prefixEnd_26044 3962397086163358942291 := by
  unfold tailWord_26044
  simp only [CollatzResearch.WordTrace]
  refine ⟨474951358827255403094593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 633268478436340537459457 474951358827255403094593)
  ·
    refine ⟨356213519120441552320945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 474951358827255403094593 356213519120441552320945)
    ·
      refine ⟨267160139340331164240709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356213519120441552320945 267160139340331164240709)
      ·
        refine ⟨50092526126312093295133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 267160139340331164240709 50092526126312093295133)
        ·
          refine ⟨18784697297367034985675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50092526126312093295133 18784697297367034985675)
          ·
            refine ⟨28177045946050552478513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18784697297367034985675 28177045946050552478513)
            ·
              refine ⟨21132784459537914358885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28177045946050552478513 21132784459537914358885)
              ·
                refine ⟨3962397086163358942291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21132784459537914358885 3962397086163358942291)
                ·
                  rfl

theorem cell20_26044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 4].length) (baseStart_26044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26044 prefixEnd_26044 := by exact prefixLift 26044
  have htrace : WordTrace (prefixWord ++ tailWord_26044) baseStart_26044 baseEnd_26044 := by
    simpa [prefixWord, tailWord_26044, baseEnd_26044] using wordTrace_append hprefix tailTrace_26044
  have hstable : (prefixWord ++ tailWord_26044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26044).length < 2 ^ (prefixWord ++ tailWord_26044).sum := by decide
  have hdescent : baseEnd_26044 < baseStart_26044 := by decide
  rcases family_descends (prefixWord ++ tailWord_26044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26050 : List Nat := [3, 5, 2, 1, 1, 2, 1, 3, 2]
def baseStart_26050 : Nat := 118140960795 + 26050 * 2 ^ 59
def prefixEnd_26050 : Nat := 4983230072969 + 3 ^ 40 * 26050 * 2
def baseEnd_26050 : Nat := 11889929821980722626849

theorem tailTrace_26050 : CollatzResearch.WordTrace tailWord_26050 prefixEnd_26050 11889929821980722626849 := by
  unfold tailWord_26050
  simp only [CollatzResearch.WordTrace]
  refine ⟨237530388908193457726901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 633414370421849220605069 237530388908193457726901)
  ·
    refine ⟨22268473960143136661897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 237530388908193457726901 22268473960143136661897)
    ·
      refine ⟨16701355470107352496423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22268473960143136661897 16701355470107352496423)
      ·
        refine ⟨25052033205161028744635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16701355470107352496423 25052033205161028744635)
        ·
          refine ⟨37578049807741543116953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25052033205161028744635 37578049807741543116953)
          ·
            refine ⟨28183537355806157337715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37578049807741543116953 28183537355806157337715)
            ·
              refine ⟨42275306033709236006573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28183537355806157337715 42275306033709236006573)
              ·
                refine ⟨15853239762640963502465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42275306033709236006573 15853239762640963502465)
                ·
                  refine ⟨11889929821980722626849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15853239762640963502465 11889929821980722626849)
                  ·
                    rfl

theorem cell20_26050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_26050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26050 prefixEnd_26050 := by exact prefixLift 26050
  have htrace : WordTrace (prefixWord ++ tailWord_26050) baseStart_26050 baseEnd_26050 := by
    simpa [prefixWord, tailWord_26050, baseEnd_26050] using wordTrace_append hprefix tailTrace_26050
  have hstable : (prefixWord ++ tailWord_26050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26050).length < 2 ^ (prefixWord ++ tailWord_26050).sum := by decide
  have hdescent : baseEnd_26050 < baseStart_26050 := by decide
  rcases family_descends (prefixWord ++ tailWord_26050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26058 : List Nat := [3, 1, 2, 1, 2, 5, 1, 3, 2]
def baseStart_26058 : Nat := 118140960795 + 26058 * 2 ^ 59
def prefixEnd_26058 : Nat := 4983230072969 + 3 ^ 40 * 26058 * 2
def baseEnd_26058 : Nat := 11893581239968250360149

theorem tailTrace_26058 : CollatzResearch.WordTrace tailWord_26058 prefixEnd_26058 11893581239968250360149 := by
  unfold tailWord_26058
  simp only [CollatzResearch.WordTrace]
  refine ⟨237603334900947799299707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 633608893069194131465885 237603334900947799299707)
  ·
    refine ⟨356405002351421698949561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237603334900947799299707 356405002351421698949561)
    ·
      refine ⟨267303751763566274212171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356405002351421698949561 267303751763566274212171)
      ·
        refine ⟨400955627645349411318257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267303751763566274212171 400955627645349411318257)
        ·
          refine ⟨300716720734012058488693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400955627645349411318257 300716720734012058488693)
          ·
            refine ⟨28192192568813630483315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 300716720734012058488693 28192192568813630483315)
            ·
              refine ⟨42288288853220445724973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28192192568813630483315 42288288853220445724973)
              ·
                refine ⟨15858108319957667146865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42288288853220445724973 15858108319957667146865)
                ·
                  refine ⟨11893581239968250360149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15858108319957667146865 11893581239968250360149)
                  ·
                    rfl

theorem cell20_26058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 2].length) (baseStart_26058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26058 prefixEnd_26058 := by exact prefixLift 26058
  have htrace : WordTrace (prefixWord ++ tailWord_26058) baseStart_26058 baseEnd_26058 := by
    simpa [prefixWord, tailWord_26058, baseEnd_26058] using wordTrace_append hprefix tailTrace_26058
  have hstable : (prefixWord ++ tailWord_26058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26058).length < 2 ^ (prefixWord ++ tailWord_26058).sum := by decide
  have hdescent : baseEnd_26058 < baseStart_26058 := by decide
  rcases family_descends (prefixWord ++ tailWord_26058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26131 : List Nat := [1, 1, 1, 2, 1, 7, 2, 2, 3]
def baseStart_26131 : Nat := 118140960795 + 26131 * 2 ^ 59
def prefixEnd_26131 : Nat := 4983230072969 + 3 ^ 40 * 26131 * 2
def baseEnd_26131 : Nat := 11926900429104440926517

theorem tailTrace_26131 : CollatzResearch.WordTrace tailWord_26131 prefixEnd_26131 11926900429104440926517 := by
  unfold tailWord_26131
  simp only [CollatzResearch.WordTrace]
  refine ⟨953075868339324664606247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 635383912226216443070831 953075868339324664606247)
  ·
    refine ⟨1429613802508986996909371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 953075868339324664606247 1429613802508986996909371)
    ·
      refine ⟨2144420703763480495364057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1429613802508986996909371 2144420703763480495364057)
      ·
        refine ⟨1608315527822610371523043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2144420703763480495364057 1608315527822610371523043)
        ·
          refine ⟨2412473291733915557284565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1608315527822610371523043 2412473291733915557284565)
          ·
            refine ⟨56542342775013645873857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 2412473291733915557284565 56542342775013645873857)
            ·
              refine ⟨42406757081260234405393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56542342775013645873857 42406757081260234405393)
              ·
                refine ⟨31805067810945175804045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42406757081260234405393 31805067810945175804045)
                ·
                  refine ⟨11926900429104440926517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31805067810945175804045 11926900429104440926517)
                  ·
                    rfl

theorem cell20_26131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 3].length) (baseStart_26131 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26131 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26131 prefixEnd_26131 := by exact prefixLift 26131
  have htrace : WordTrace (prefixWord ++ tailWord_26131) baseStart_26131 baseEnd_26131 := by
    simpa [prefixWord, tailWord_26131, baseEnd_26131] using wordTrace_append hprefix tailTrace_26131
  have hstable : (prefixWord ++ tailWord_26131).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26131).length < 2 ^ (prefixWord ++ tailWord_26131).sum := by decide
  have hdescent : baseEnd_26131 < baseStart_26131 := by decide
  rcases family_descends (prefixWord ++ tailWord_26131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26145 : List Nat := [1, 2, 3, 2, 2, 2, 3, 5]
def baseStart_26145 : Nat := 118140960795 + 26145 * 2 ^ 59
def prefixEnd_26145 : Nat := 4983230072969 + 3 ^ 40 * 26145 * 2
def baseEnd_26145 : Nat := 3977763470194204819931

theorem tailTrace_26145 : CollatzResearch.WordTrace tailWord_26145 prefixEnd_26145 3977763470194204819931 := by
  unfold tailWord_26145
  simp only [CollatzResearch.WordTrace]
  refine ⟨953586490288605055615889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 635724326859070037077259 953586490288605055615889)
  ·
    refine ⟨715189867716453791711917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 953586490288605055615889 715189867716453791711917)
    ·
      refine ⟨268196200393670171891969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 715189867716453791711917 268196200393670171891969)
      ·
        refine ⟨201147150295252628918977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268196200393670171891969 201147150295252628918977)
        ·
          refine ⟨150860362721439471689233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201147150295252628918977 150860362721439471689233)
          ·
            refine ⟨113145272041079603766925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150860362721439471689233 113145272041079603766925)
            ·
              refine ⟨42429477015404851412597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113145272041079603766925 42429477015404851412597)
              ·
                refine ⟨3977763470194204819931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42429477015404851412597 3977763470194204819931)
                ·
                  rfl

theorem cell20_26145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 5].length) (baseStart_26145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26145 prefixEnd_26145 := by exact prefixLift 26145
  have htrace : WordTrace (prefixWord ++ tailWord_26145) baseStart_26145 baseEnd_26145 := by
    simpa [prefixWord, tailWord_26145, baseEnd_26145] using wordTrace_append hprefix tailTrace_26145
  have hstable : (prefixWord ++ tailWord_26145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26145).length < 2 ^ (prefixWord ++ tailWord_26145).sum := by decide
  have hdescent : baseEnd_26145 < baseStart_26145 := by decide
  rcases family_descends (prefixWord ++ tailWord_26145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26172 : List Nat := [2, 2, 2, 2, 4, 1, 2, 3, 2]
def baseStart_26172 : Nat := 118140960795 + 26172 * 2 ^ 59
def prefixEnd_26172 : Nat := 4983230072969 + 3 ^ 40 * 26172 * 2
def baseEnd_26172 : Nat := 11945613946290520559683

theorem tailTrace_26172 : CollatzResearch.WordTrace tailWord_26172 prefixEnd_26172 11945613946290520559683 := by
  unfold tailWord_26172
  simp only [CollatzResearch.WordTrace]
  refine ⟨477285630595394333424385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 636380840793859111232513 477285630595394333424385)
  ·
    refine ⟨357964222946545750068289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 477285630595394333424385 357964222946545750068289)
    ·
      refine ⟨268473167209909312551217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357964222946545750068289 268473167209909312551217)
      ·
        refine ⟨201354875407431984413413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268473167209909312551217 201354875407431984413413)
        ·
          refine ⟨37754039138893497077515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201354875407431984413413 37754039138893497077515)
          ·
            refine ⟨56631058708340245616273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37754039138893497077515 56631058708340245616273)
            ·
              refine ⟨42473294031255184212205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56631058708340245616273 42473294031255184212205)
              ·
                refine ⟨15927485261720694079577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42473294031255184212205 15927485261720694079577)
                ·
                  refine ⟨11945613946290520559683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15927485261720694079577 11945613946290520559683)
                  ·
                    rfl

theorem cell20_26172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 2].length) (baseStart_26172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26172 prefixEnd_26172 := by exact prefixLift 26172
  have htrace : WordTrace (prefixWord ++ tailWord_26172) baseStart_26172 baseEnd_26172 := by
    simpa [prefixWord, tailWord_26172, baseEnd_26172] using wordTrace_append hprefix tailTrace_26172
  have hstable : (prefixWord ++ tailWord_26172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26172).length < 2 ^ (prefixWord ++ tailWord_26172).sum := by decide
  have hdescent : baseEnd_26172 < baseStart_26172 := by decide
  rcases family_descends (prefixWord ++ tailWord_26172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26182 : List Nat := [6, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_26182 : Nat := 118140960795 + 26182 * 2 ^ 59
def prefixEnd_26182 : Nat := 4983230072969 + 3 ^ 40 * 26182 * 2
def baseEnd_26182 : Nat := 11950178218774930226309

theorem tailTrace_26182 : CollatzResearch.WordTrace tailWord_26182 prefixEnd_26182 11950178218774930226309 := by
  unfold tailWord_26182
  simp only [CollatzResearch.WordTrace]
  refine ⟨29841749723580011709775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 636623994103040249808533 29841749723580011709775)
  ·
    refine ⟨44762624585370017564663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29841749723580011709775 44762624585370017564663)
    ·
      refine ⟨67143936878055026346995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44762624585370017564663 67143936878055026346995)
      ·
        refine ⟨100715905317082539520493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67143936878055026346995 100715905317082539520493)
        ·
          refine ⟨37768464493905952320185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100715905317082539520493 37768464493905952320185)
          ·
            refine ⟨28326348370429464240139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37768464493905952320185 28326348370429464240139)
            ·
              refine ⟨42489522555644196360209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28326348370429464240139 42489522555644196360209)
              ·
                refine ⟨31867141916733147270157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42489522555644196360209 31867141916733147270157)
                ·
                  refine ⟨11950178218774930226309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31867141916733147270157 11950178218774930226309)
                  ·
                    rfl

theorem cell20_26182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_26182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26182 prefixEnd_26182 := by exact prefixLift 26182
  have htrace : WordTrace (prefixWord ++ tailWord_26182) baseStart_26182 baseEnd_26182 := by
    simpa [prefixWord, tailWord_26182, baseEnd_26182] using wordTrace_append hprefix tailTrace_26182
  have hstable : (prefixWord ++ tailWord_26182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26182).length < 2 ^ (prefixWord ++ tailWord_26182).sum := by decide
  have hdescent : baseEnd_26182 < baseStart_26182 := by decide
  rcases family_descends (prefixWord ++ tailWord_26182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26183 : List Nat := [1, 1, 4, 1, 5, 1, 7]
def baseStart_26183 : Nat := 118140960795 + 26183 * 2 ^ 59
def prefixEnd_26183 : Nat := 4983230072969 + 3 ^ 40 * 26183 * 2
def baseEnd_26183 : Nat := 1327848294002596799219

theorem tailTrace_26183 : CollatzResearch.WordTrace tailWord_26183 prefixEnd_26183 1327848294002596799219 := by
  unfold tailWord_26183
  simp only [CollatzResearch.WordTrace]
  refine ⟨954972464150937545499203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 636648309433958363666135 954972464150937545499203)
  ·
    refine ⟨1432458696226406318248805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 954972464150937545499203 1432458696226406318248805)
    ·
      refine ⟨268586005542451184671651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1432458696226406318248805 268586005542451184671651)
      ·
        refine ⟨402879008313676777007477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268586005542451184671651 402879008313676777007477)
        ·
          refine ⟨37769907029407197844451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 402879008313676777007477 37769907029407197844451)
          ·
            refine ⟨56654860544110796766677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37769907029407197844451 56654860544110796766677)
            ·
              refine ⟨1327848294002596799219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 56654860544110796766677 1327848294002596799219)
              ·
                rfl

theorem cell20_26183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 7].length) (baseStart_26183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26183 prefixEnd_26183 := by exact prefixLift 26183
  have htrace : WordTrace (prefixWord ++ tailWord_26183) baseStart_26183 baseEnd_26183 := by
    simpa [prefixWord, tailWord_26183, baseEnd_26183] using wordTrace_append hprefix tailTrace_26183
  have hstable : (prefixWord ++ tailWord_26183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26183).length < 2 ^ (prefixWord ++ tailWord_26183).sum := by decide
  have hdescent : baseEnd_26183 < baseStart_26183 := by decide
  rcases family_descends (prefixWord ++ tailWord_26183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26248 : List Nat := [2, 1, 3, 5, 1, 2, 1, 1, 4]
def baseStart_26248 : Nat := 118140960795 + 26248 * 2 ^ 59
def prefixEnd_26248 : Nat := 4983230072969 + 3 ^ 40 * 26248 * 2
def baseEnd_26248 : Nat := 11980302417172034026039

theorem tailTrace_26248 : CollatzResearch.WordTrace tailWord_26248 prefixEnd_26248 11980302417172034026039 := by
  unfold tailWord_26248
  simp only [CollatzResearch.WordTrace]
  refine ⟨478671604457726823307699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 638228805943635764410265 478671604457726823307699)
  ·
    refine ⟨718007406686590234961549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 478671604457726823307699 718007406686590234961549)
    ·
      refine ⟨269252777507471338110581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 718007406686590234961549 269252777507471338110581)
      ·
        refine ⟨25242447891325437947867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 269252777507471338110581 25242447891325437947867)
        ·
          refine ⟨37863671836988156921801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25242447891325437947867 37863671836988156921801)
          ·
            refine ⟨28397753877741117691351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37863671836988156921801 28397753877741117691351)
            ·
              refine ⟨42596630816611676537027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28397753877741117691351 42596630816611676537027)
              ·
                refine ⟨63894946224917514805541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42596630816611676537027 63894946224917514805541)
                ·
                  refine ⟨11980302417172034026039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63894946224917514805541 11980302417172034026039)
                  ·
                    rfl

theorem cell20_26248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 4].length) (baseStart_26248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26248 prefixEnd_26248 := by exact prefixLift 26248
  have htrace : WordTrace (prefixWord ++ tailWord_26248) baseStart_26248 baseEnd_26248 := by
    simpa [prefixWord, tailWord_26248, baseEnd_26248] using wordTrace_append hprefix tailTrace_26248
  have hstable : (prefixWord ++ tailWord_26248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26248).length < 2 ^ (prefixWord ++ tailWord_26248).sum := by decide
  have hdescent : baseEnd_26248 < baseStart_26248 := by decide
  rcases family_descends (prefixWord ++ tailWord_26248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26258 : List Nat := [3, 2, 3, 1, 4, 1, 2, 1, 3]
def baseStart_26258 : Nat := 118140960795 + 26258 * 2 ^ 59
def prefixEnd_26258 : Nat := 4983230072969 + 3 ^ 40 * 26258 * 2
def baseEnd_26258 : Nat := 11984866689656443692665

theorem tailTrace_26258 : CollatzResearch.WordTrace tailWord_26258 prefixEnd_26258 11984866689656443692665 := by
  unfold tailWord_26258
  simp only [CollatzResearch.WordTrace]
  refine ⟨239426984719806338619857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 638471959252816902986285 239426984719806338619857)
  ·
    refine ⟨179570238539854753964893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239426984719806338619857 179570238539854753964893)
    ·
      refine ⟨67338839452445532736835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179570238539854753964893 67338839452445532736835)
      ·
        refine ⟨101008259178668299105253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67338839452445532736835 101008259178668299105253)
        ·
          refine ⟨18939048596000306082235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101008259178668299105253 18939048596000306082235)
          ·
            refine ⟨28408572894000459123353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18939048596000306082235 28408572894000459123353)
            ·
              refine ⟨21306429670500344342515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28408572894000459123353 21306429670500344342515)
              ·
                refine ⟨31959644505750516513773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21306429670500344342515 31959644505750516513773)
                ·
                  refine ⟨11984866689656443692665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31959644505750516513773 11984866689656443692665)
                  ·
                    rfl

theorem cell20_26258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_26258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26258 prefixEnd_26258 := by exact prefixLift 26258
  have htrace : WordTrace (prefixWord ++ tailWord_26258) baseStart_26258 baseEnd_26258 := by
    simpa [prefixWord, tailWord_26258, baseEnd_26258] using wordTrace_append hprefix tailTrace_26258
  have hstable : (prefixWord ++ tailWord_26258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26258).length < 2 ^ (prefixWord ++ tailWord_26258).sum := by decide
  have hdescent : baseEnd_26258 < baseStart_26258 := by decide
  rcases family_descends (prefixWord ++ tailWord_26258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26310 : List Nat := [6, 1, 2, 1, 1, 3, 1, 5]
def baseStart_26310 : Nat := 118140960795 + 26310 * 2 ^ 59
def prefixEnd_26310 : Nat := 4983230072969 + 3 ^ 40 * 26310 * 2
def baseEnd_26310 : Nat := 4002866968858457986373

theorem tailTrace_26310 : CollatzResearch.WordTrace tailWord_26310 prefixEnd_26310 4002866968858457986373 := by
  unfold tailWord_26310
  simp only [CollatzResearch.WordTrace]
  refine ⟨29987641709088694855387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 639736356460558823581589 29987641709088694855387)
  ·
    refine ⟨44981462563633042283081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29987641709088694855387 44981462563633042283081)
    ·
      refine ⟨33736096922724781712311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44981462563633042283081 33736096922724781712311)
      ·
        refine ⟨50604145384087172568467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33736096922724781712311 50604145384087172568467)
        ·
          refine ⟨75906218076130758852701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50604145384087172568467 75906218076130758852701)
          ·
            refine ⟨28464831778549034569763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75906218076130758852701 28464831778549034569763)
            ·
              refine ⟨42697247667823551854645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28464831778549034569763 42697247667823551854645)
              ·
                refine ⟨4002866968858457986373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42697247667823551854645 4002866968858457986373)
                ·
                  rfl

theorem cell20_26310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_26310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26310 prefixEnd_26310 := by exact prefixLift 26310
  have htrace : WordTrace (prefixWord ++ tailWord_26310) baseStart_26310 baseEnd_26310 := by
    simpa [prefixWord, tailWord_26310, baseEnd_26310] using wordTrace_append hprefix tailTrace_26310
  have hstable : (prefixWord ++ tailWord_26310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26310).length < 2 ^ (prefixWord ++ tailWord_26310).sum := by decide
  have hdescent : baseEnd_26310 < baseStart_26310 := by decide
  rcases family_descends (prefixWord ++ tailWord_26310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26311 : List Nat := [1, 1, 4, 1, 1, 1, 4, 3, 4]
def baseStart_26311 : Nat := 118140960795 + 26311 * 2 ^ 59
def prefixEnd_26311 : Nat := 4983230072969 + 3 ^ 40 * 26311 * 2
def baseEnd_26311 : Nat := 12009057333823814925781

theorem tailTrace_26311 : CollatzResearch.WordTrace tailWord_26311 prefixEnd_26311 12009057333823814925781 := by
  unfold tailWord_26311
  simp only [CollatzResearch.WordTrace]
  refine ⟨959641007687215406158787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 639760671791476937439191 959641007687215406158787)
  ·
    refine ⟨1439461511530823109238181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 959641007687215406158787 1439461511530823109238181)
    ·
      refine ⟨269899033412029332982159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1439461511530823109238181 269899033412029332982159)
      ·
        refine ⟨404848550118043999473239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269899033412029332982159 404848550118043999473239)
        ·
          refine ⟨607272825177065999209859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404848550118043999473239 607272825177065999209859)
          ·
            refine ⟨910909237765598998814789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607272825177065999209859 910909237765598998814789)
            ·
              refine ⟨170795482081049812277773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 910909237765598998814789 170795482081049812277773)
              ·
                refine ⟨64048305780393679604165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170795482081049812277773 64048305780393679604165)
                ·
                  refine ⟨12009057333823814925781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64048305780393679604165 12009057333823814925781)
                  ·
                    rfl

theorem cell20_26311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 4].length) (baseStart_26311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26311 prefixEnd_26311 := by exact prefixLift 26311
  have htrace : WordTrace (prefixWord ++ tailWord_26311) baseStart_26311 baseEnd_26311 := by
    simpa [prefixWord, tailWord_26311, baseEnd_26311] using wordTrace_append hprefix tailTrace_26311
  have hstable : (prefixWord ++ tailWord_26311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26311).length < 2 ^ (prefixWord ++ tailWord_26311).sum := by decide
  have hdescent : baseEnd_26311 < baseStart_26311 := by decide
  rcases family_descends (prefixWord ++ tailWord_26311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26314 : List Nat := [3, 1, 2, 1, 5, 2, 1, 5]
def baseStart_26314 : Nat := 118140960795 + 26314 * 2 ^ 59
def prefixEnd_26314 : Nat := 4983230072969 + 3 ^ 40 * 26314 * 2
def baseEnd_26314 : Nat := 4003475538523045941923

theorem tailTrace_26314 : CollatzResearch.WordTrace tailWord_26314 prefixEnd_26314 4003475538523045941923 := by
  unfold tailWord_26314
  simp only [CollatzResearch.WordTrace]
  refine ⟨239937606669086729629499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 639833617784231279011997 239937606669086729629499)
  ·
    refine ⟨359906410003630094444249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239937606669086729629499 359906410003630094444249)
    ·
      refine ⟨269929807502722570833187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359906410003630094444249 269929807502722570833187)
      ·
        refine ⟨404894711254083856249781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269929807502722570833187 404894711254083856249781)
        ·
          refine ⟨37958879180070361523417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 404894711254083856249781 37958879180070361523417)
          ·
            refine ⟨28469159385052771142563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37958879180070361523417 28469159385052771142563)
            ·
              refine ⟨42703739077579156713845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28469159385052771142563 42703739077579156713845)
              ·
                refine ⟨4003475538523045941923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42703739077579156713845 4003475538523045941923)
                ·
                  rfl

theorem cell20_26314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_26314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26314 prefixEnd_26314 := by exact prefixLift 26314
  have htrace : WordTrace (prefixWord ++ tailWord_26314) baseStart_26314 baseEnd_26314 := by
    simpa [prefixWord, tailWord_26314, baseEnd_26314] using wordTrace_append hprefix tailTrace_26314
  have hstable : (prefixWord ++ tailWord_26314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26314).length < 2 ^ (prefixWord ++ tailWord_26314).sum := by decide
  have hdescent : baseEnd_26314 < baseStart_26314 := by decide
  rcases family_descends (prefixWord ++ tailWord_26314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26335 : List Nat := [1, 1, 2, 3, 2, 2, 5, 4]
def baseStart_26335 : Nat := 118140960795 + 26335 * 2 ^ 59
def prefixEnd_26335 : Nat := 4983230072969 + 3 ^ 40 * 26335 * 2
def baseEnd_26335 : Nat := 4006670529262132708561

theorem tailTrace_26335 : CollatzResearch.WordTrace tailWord_26335 prefixEnd_26335 4006670529262132708561 := by
  unfold tailWord_26335
  simp only [CollatzResearch.WordTrace]
  refine ⟨960516359600267505032459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 640344239733511670021639 960516359600267505032459)
  ·
    refine ⟨1440774539400401257548689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 960516359600267505032459 1440774539400401257548689)
    ·
      refine ⟨1080580904550300943161517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1440774539400401257548689 1080580904550300943161517)
      ·
        refine ⟨405217839206362853685569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1080580904550300943161517 405217839206362853685569)
        ·
          refine ⟨303913379404772140264177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405217839206362853685569 303913379404772140264177)
          ·
            refine ⟨227935034553579105198133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303913379404772140264177 227935034553579105198133)
            ·
              refine ⟨21368909489398041112325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 227935034553579105198133 21368909489398041112325)
              ·
                refine ⟨4006670529262132708561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21368909489398041112325 4006670529262132708561)
                ·
                  rfl

theorem cell20_26335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 4].length) (baseStart_26335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26335 prefixEnd_26335 := by exact prefixLift 26335
  have htrace : WordTrace (prefixWord ++ tailWord_26335) baseStart_26335 baseEnd_26335 := by
    simpa [prefixWord, tailWord_26335, baseEnd_26335] using wordTrace_append hprefix tailTrace_26335
  have hstable : (prefixWord ++ tailWord_26335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26335).length < 2 ^ (prefixWord ++ tailWord_26335).sum := by decide
  have hdescent : baseEnd_26335 < baseStart_26335 := by decide
  rcases family_descends (prefixWord ++ tailWord_26335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26380 : List Nat := [2, 2, 1, 2, 2, 1, 2, 5, 3]
def baseStart_26380 : Nat := 118140960795 + 26380 * 2 ^ 59
def prefixEnd_26380 : Nat := 4983230072969 + 3 ^ 40 * 26380 * 2
def baseEnd_26380 : Nat := 12040550813966241625499

theorem tailTrace_26380 : CollatzResearch.WordTrace tailWord_26380 prefixEnd_26380 12040550813966241625499 := by
  unfold tailWord_26380
  simp only [CollatzResearch.WordTrace]
  refine ⟨481078822218620095210297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 641438429624826793613729 481078822218620095210297)
  ·
    refine ⟨360809116663965071407723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 481078822218620095210297 360809116663965071407723)
    ·
      refine ⟨541213674995947607111585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360809116663965071407723 541213674995947607111585)
      ·
        refine ⟨405910256246960705333689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 541213674995947607111585 405910256246960705333689)
        ·
          refine ⟨304432692185220529000267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405910256246960705333689 304432692185220529000267)
          ·
            refine ⟨456649038277830793500401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304432692185220529000267 456649038277830793500401)
            ·
              refine ⟨342486778708373095125301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 456649038277830793500401 342486778708373095125301)
              ·
                refine ⟨32108135503909977667997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 342486778708373095125301 32108135503909977667997)
                ·
                  refine ⟨12040550813966241625499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32108135503909977667997 12040550813966241625499)
                  ·
                    rfl

theorem cell20_26380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_26380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26380 prefixEnd_26380 := by exact prefixLift 26380
  have htrace : WordTrace (prefixWord ++ tailWord_26380) baseStart_26380 baseEnd_26380 := by
    simpa [prefixWord, tailWord_26380, baseEnd_26380] using wordTrace_append hprefix tailTrace_26380
  have hstable : (prefixWord ++ tailWord_26380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26380).length < 2 ^ (prefixWord ++ tailWord_26380).sum := by decide
  have hdescent : baseEnd_26380 < baseStart_26380 := by decide
  rcases family_descends (prefixWord ++ tailWord_26380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26418 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 5]
def baseStart_26418 : Nat := 118140960795 + 26418 * 2 ^ 59
def prefixEnd_26418 : Nat := 4983230072969 + 3 ^ 40 * 26418 * 2
def baseEnd_26418 : Nat := 12057895049406998358677

theorem tailTrace_26418 : CollatzResearch.WordTrace tailWord_26418 prefixEnd_26418 12057895049406998358677 := by
  unfold tailWord_26418
  simp only [CollatzResearch.WordTrace]
  refine ⟨240885904574893170075977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 642362412199715120202605 240885904574893170075977)
  ·
    refine ⟨180664428431169877556983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240885904574893170075977 180664428431169877556983)
    ·
      refine ⟨270996642646754816335475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180664428431169877556983 270996642646754816335475)
      ·
        refine ⟨406494963970132224503213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270996642646754816335475 406494963970132224503213)
        ·
          refine ⟨152435611488799584188705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 406494963970132224503213 152435611488799584188705)
          ·
            refine ⟨114326708616599688141529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152435611488799584188705 114326708616599688141529)
            ·
              refine ⟨85745031462449766106147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114326708616599688141529 85745031462449766106147)
              ·
                refine ⟨128617547193674649159221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85745031462449766106147 128617547193674649159221)
                ·
                  refine ⟨12057895049406998358677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128617547193674649159221 12057895049406998358677)
                  ·
                    rfl

theorem cell20_26418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_26418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26418 prefixEnd_26418 := by exact prefixLift 26418
  have htrace : WordTrace (prefixWord ++ tailWord_26418) baseStart_26418 baseEnd_26418 := by
    simpa [prefixWord, tailWord_26418, baseEnd_26418] using wordTrace_append hprefix tailTrace_26418
  have hstable : (prefixWord ++ tailWord_26418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26418).length < 2 ^ (prefixWord ++ tailWord_26418).sum := by decide
  have hdescent : baseEnd_26418 < baseStart_26418 := by decide
  rcases family_descends (prefixWord ++ tailWord_26418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26421 : List Nat := [1, 3, 3, 1, 4, 2, 1, 1, 4]
def baseStart_26421 : Nat := 118140960795 + 26421 * 2 ^ 59
def prefixEnd_26421 : Nat := 4983230072969 + 3 ^ 40 * 26421 * 2
def baseEnd_26421 : Nat := 12059264331152321258665

theorem tailTrace_26421 : CollatzResearch.WordTrace tailWord_26421 prefixEnd_26421 12059264331152321258665 := by
  unfold tailWord_26421
  simp only [CollatzResearch.WordTrace]
  refine ⟨963653037288704192663117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 642435358192469461775411 963653037288704192663117)
  ·
    refine ⟨361369888983264072248669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 963653037288704192663117 361369888983264072248669)
    ·
      refine ⟨135513708368724027093251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361369888983264072248669 135513708368724027093251)
      ·
        refine ⟨203270562553086040639877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135513708368724027093251 203270562553086040639877)
        ·
          refine ⟨38113230478703632619977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203270562553086040639877 38113230478703632619977)
          ·
            refine ⟨28584922859027724464983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38113230478703632619977 28584922859027724464983)
            ·
              refine ⟨42877384288541586697475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28584922859027724464983 42877384288541586697475)
              ·
                refine ⟨64316076432812380046213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42877384288541586697475 64316076432812380046213)
                ·
                  refine ⟨12059264331152321258665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64316076432812380046213 12059264331152321258665)
                  ·
                    rfl

theorem cell20_26421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_26421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26421 prefixEnd_26421 := by exact prefixLift 26421
  have htrace : WordTrace (prefixWord ++ tailWord_26421) baseStart_26421 baseEnd_26421 := by
    simpa [prefixWord, tailWord_26421, baseEnd_26421] using wordTrace_append hprefix tailTrace_26421
  have hstable : (prefixWord ++ tailWord_26421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26421).length < 2 ^ (prefixWord ++ tailWord_26421).sum := by decide
  have hdescent : baseEnd_26421 < baseStart_26421 := by decide
  rcases family_descends (prefixWord ++ tailWord_26421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26431 : List Nat := [1, 1, 2, 2, 7, 1, 2, 1, 3]
def baseStart_26431 : Nat := 118140960795 + 26431 * 2 ^ 59
def prefixEnd_26431 : Nat := 4983230072969 + 3 ^ 40 * 26431 * 2
def baseEnd_26431 : Nat := 12063828603636730925291

theorem tailTrace_26431 : CollatzResearch.WordTrace tailWord_26431 prefixEnd_26431 12063828603636730925291 := by
  unfold tailWord_26431
  simp only [CollatzResearch.WordTrace]
  refine ⟨964017767252475900527147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 642678511501650600351431 964017767252475900527147)
  ·
    refine ⟨1446026650878713850790721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 964017767252475900527147 1446026650878713850790721)
    ·
      refine ⟨1084519988159035388093041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1446026650878713850790721 1084519988159035388093041)
      ·
        refine ⟨813389991119276541069781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1084519988159035388093041 813389991119276541069781)
        ·
          refine ⟨19063827916858043931323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 813389991119276541069781 19063827916858043931323)
          ·
            refine ⟨28595741875287065896985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19063827916858043931323 28595741875287065896985)
            ·
              refine ⟨21446806406465299422739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28595741875287065896985 21446806406465299422739)
              ·
                refine ⟨32170209609697949134109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21446806406465299422739 32170209609697949134109)
                ·
                  refine ⟨12063828603636730925291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32170209609697949134109 12063828603636730925291)
                  ·
                    rfl

theorem cell20_26431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 3].length) (baseStart_26431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26431 prefixEnd_26431 := by exact prefixLift 26431
  have htrace : WordTrace (prefixWord ++ tailWord_26431) baseStart_26431 baseEnd_26431 := by
    simpa [prefixWord, tailWord_26431, baseEnd_26431] using wordTrace_append hprefix tailTrace_26431
  have hstable : (prefixWord ++ tailWord_26431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26431).length < 2 ^ (prefixWord ++ tailWord_26431).sum := by decide
  have hdescent : baseEnd_26431 < baseStart_26431 := by decide
  rcases family_descends (prefixWord ++ tailWord_26431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26435 : List Nat := [1, 1, 1, 3, 1, 5, 4, 1, 3]
def baseStart_26435 : Nat := 118140960795 + 26435 * 2 ^ 59
def prefixEnd_26435 : Nat := 4983230072969 + 3 ^ 40 * 26435 * 2
def baseEnd_26435 : Nat := 12065654312630494791941

theorem tailTrace_26435 : CollatzResearch.WordTrace tailWord_26435 prefixEnd_26435 12065654312630494791941 := by
  unfold tailWord_26435
  simp only [CollatzResearch.WordTrace]
  refine ⟨964163659237984583672759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 642775772825323055781839 964163659237984583672759)
  ·
    refine ⟨1446245488856976875509139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 964163659237984583672759 1446245488856976875509139)
    ·
      refine ⟨2169368233285465313263709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1446245488856976875509139 2169368233285465313263709)
      ·
        refine ⟨813513087482049492473891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2169368233285465313263709 813513087482049492473891)
        ·
          refine ⟨1220269631223074238710837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813513087482049492473891 1220269631223074238710837)
          ·
            refine ⟨114400277927163209879141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1220269631223074238710837 114400277927163209879141)
            ·
              refine ⟨21450052111343101852339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114400277927163209879141 21450052111343101852339)
              ·
                refine ⟨32175078167014652778509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21450052111343101852339 32175078167014652778509)
                ·
                  refine ⟨12065654312630494791941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32175078167014652778509 12065654312630494791941)
                  ·
                    rfl

theorem cell20_26435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 3].length) (baseStart_26435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26435 prefixEnd_26435 := by exact prefixLift 26435
  have htrace : WordTrace (prefixWord ++ tailWord_26435) baseStart_26435 baseEnd_26435 := by
    simpa [prefixWord, tailWord_26435, baseEnd_26435] using wordTrace_append hprefix tailTrace_26435
  have hstable : (prefixWord ++ tailWord_26435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26435).length < 2 ^ (prefixWord ++ tailWord_26435).sum := by decide
  have hdescent : baseEnd_26435 < baseStart_26435 := by decide
  rcases family_descends (prefixWord ++ tailWord_26435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26476 : List Nat := [2, 2, 1, 1, 4, 4, 2, 2, 2]
def baseStart_26476 : Nat := 118140960795 + 26476 * 2 ^ 59
def prefixEnd_26476 : Nat := 4983230072969 + 3 ^ 40 * 26476 * 2
def baseEnd_26476 : Nat := 12084367829816574425107

theorem tailTrace_26476 : CollatzResearch.WordTrace tailWord_26476 prefixEnd_26476 12084367829816574425107 := by
  unfold tailWord_26476
  simp only [CollatzResearch.WordTrace]
  refine ⟨482829526044724292957641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 643772701392965723943521 482829526044724292957641)
  ·
    refine ⟨362122144533543219718231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 482829526044724292957641 362122144533543219718231)
    ·
      refine ⟨543183216800314829577347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362122144533543219718231 543183216800314829577347)
      ·
        refine ⟨814774825200472244366021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543183216800314829577347 814774825200472244366021)
        ·
          refine ⟨152770279725088545818629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 814774825200472244366021 152770279725088545818629)
          ·
            refine ⟨28644427448454102340993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152770279725088545818629 28644427448454102340993)
            ·
              refine ⟨21483320586340576755745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28644427448454102340993 21483320586340576755745)
              ·
                refine ⟨16112490439755432566809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21483320586340576755745 16112490439755432566809)
                ·
                  refine ⟨12084367829816574425107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16112490439755432566809 12084367829816574425107)
                  ·
                    rfl

theorem cell20_26476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 2].length) (baseStart_26476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26476 prefixEnd_26476 := by exact prefixLift 26476
  have htrace : WordTrace (prefixWord ++ tailWord_26476) baseStart_26476 baseEnd_26476 := by
    simpa [prefixWord, tailWord_26476, baseEnd_26476] using wordTrace_append hprefix tailTrace_26476
  have hstable : (prefixWord ++ tailWord_26476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26476).length < 2 ^ (prefixWord ++ tailWord_26476).sum := by decide
  have hdescent : baseEnd_26476 < baseStart_26476 := by decide
  rcases family_descends (prefixWord ++ tailWord_26476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26497 : List Nat := [1, 2, 4, 4, 1, 1, 1, 2, 4]
def baseStart_26497 : Nat := 118140960795 + 26497 * 2 ^ 59
def prefixEnd_26497 : Nat := 4983230072969 + 3 ^ 40 * 26497 * 2
def baseEnd_26497 : Nat := 12093952802033834725021

theorem tailTrace_26497 : CollatzResearch.WordTrace tailWord_26497 prefixEnd_26497 12093952802033834725021 := by
  unfold tailWord_26497
  simp only [CollatzResearch.WordTrace]
  refine ⟨966424985013369172429745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 644283323342246114953163 966424985013369172429745)
  ·
    refine ⟨724818738760026879322309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 966424985013369172429745 724818738760026879322309)
    ·
      refine ⟨135903513517505039872933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 724818738760026879322309 135903513517505039872933)
      ·
        refine ⟨25481908784532194976175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135903513517505039872933 25481908784532194976175)
        ·
          refine ⟨38222863176798292464263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25481908784532194976175 38222863176798292464263)
          ·
            refine ⟨57334294765197438696395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38222863176798292464263 57334294765197438696395)
            ·
              refine ⟨86001442147796158044593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57334294765197438696395 86001442147796158044593)
              ·
                refine ⟨64501081610847118533445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86001442147796158044593 64501081610847118533445)
                ·
                  refine ⟨12093952802033834725021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64501081610847118533445 12093952802033834725021)
                  ·
                    rfl

theorem cell20_26497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 4].length) (baseStart_26497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26497 prefixEnd_26497 := by exact prefixLift 26497
  have htrace : WordTrace (prefixWord ++ tailWord_26497) baseStart_26497 baseEnd_26497 := by
    simpa [prefixWord, tailWord_26497, baseEnd_26497] using wordTrace_append hprefix tailTrace_26497
  have hstable : (prefixWord ++ tailWord_26497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26497).length < 2 ^ (prefixWord ++ tailWord_26497).sum := by decide
  have hdescent : baseEnd_26497 < baseStart_26497 := by decide
  rcases family_descends (prefixWord ++ tailWord_26497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26501 : List Nat := [1, 3, 1, 1, 3, 2, 3, 2, 4]
def baseStart_26501 : Nat := 118140960795 + 26501 * 2 ^ 59
def prefixEnd_26501 : Nat := 4983230072969 + 3 ^ 40 * 26501 * 2
def baseEnd_26501 : Nat := 12095778511027598591671

theorem tailTrace_26501 : CollatzResearch.WordTrace tailWord_26501 prefixEnd_26501 12095778511027598591671 := by
  unfold tailWord_26501
  simp only [CollatzResearch.WordTrace]
  refine ⟨966570876998877855575357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 644380584665918570383571 966570876998877855575357)
  ·
    refine ⟨362464078874579195840759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 966570876998877855575357 362464078874579195840759)
    ·
      refine ⟨543696118311868793761139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362464078874579195840759 543696118311868793761139)
      ·
        refine ⟨815544177467803190641709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543696118311868793761139 815544177467803190641709)
        ·
          refine ⟨305829066550426196490641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 815544177467803190641709 305829066550426196490641)
          ·
            refine ⟨229371799912819647367981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305829066550426196490641 229371799912819647367981)
            ·
              refine ⟨86014424967307367762993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229371799912819647367981 86014424967307367762993)
              ·
                refine ⟨64510818725480525822245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86014424967307367762993 64510818725480525822245)
                ·
                  refine ⟨12095778511027598591671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64510818725480525822245 12095778511027598591671)
                  ·
                    rfl

theorem cell20_26501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_26501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26501 prefixEnd_26501 := by exact prefixLift 26501
  have htrace : WordTrace (prefixWord ++ tailWord_26501) baseStart_26501 baseEnd_26501 := by
    simpa [prefixWord, tailWord_26501, baseEnd_26501] using wordTrace_append hprefix tailTrace_26501
  have hstable : (prefixWord ++ tailWord_26501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26501).length < 2 ^ (prefixWord ++ tailWord_26501).sum := by decide
  have hdescent : baseEnd_26501 < baseStart_26501 := by decide
  rcases family_descends (prefixWord ++ tailWord_26501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26504 : List Nat := [2, 1, 3, 3, 3, 1, 3, 4]
def baseStart_26504 : Nat := 118140960795 + 26504 * 2 ^ 59
def prefixEnd_26504 : Nat := 4983230072969 + 3 ^ 40 * 26504 * 2
def baseEnd_26504 : Nat := 4032382597590973830553

theorem tailTrace_26504 : CollatzResearch.WordTrace tailWord_26504 prefixEnd_26504 4032382597590973830553 := by
  unfold tailWord_26504
  simp only [CollatzResearch.WordTrace]
  refine ⟨483340147994004683967283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 644453530658672911956377 483340147994004683967283)
  ·
    refine ⟨725010221991007025950925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 483340147994004683967283 725010221991007025950925)
    ·
      refine ⟨271878833246627634731597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 725010221991007025950925 271878833246627634731597)
      ·
        refine ⟨101954562467485363024349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271878833246627634731597 101954562467485363024349)
        ·
          refine ⟨38232960925307011134131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101954562467485363024349 38232960925307011134131)
          ·
            refine ⟨57349441387960516701197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38232960925307011134131 57349441387960516701197)
            ·
              refine ⟨21506040520485193762949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57349441387960516701197 21506040520485193762949)
              ·
                refine ⟨4032382597590973830553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21506040520485193762949 4032382597590973830553)
                ·
                  rfl

theorem cell20_26504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 4].length) (baseStart_26504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26504 prefixEnd_26504 := by exact prefixLift 26504
  have htrace : WordTrace (prefixWord ++ tailWord_26504) baseStart_26504 baseEnd_26504 := by
    simpa [prefixWord, tailWord_26504, baseEnd_26504] using wordTrace_append hprefix tailTrace_26504
  have hstable : (prefixWord ++ tailWord_26504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26504).length < 2 ^ (prefixWord ++ tailWord_26504).sum := by decide
  have hdescent : baseEnd_26504 < baseStart_26504 := by decide
  rcases family_descends (prefixWord ++ tailWord_26504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26514 : List Nat := [3, 2, 3, 2, 1, 2, 2, 3, 2]
def baseStart_26514 : Nat := 118140960795 + 26514 * 2 ^ 59
def prefixEnd_26514 : Nat := 4983230072969 + 3 ^ 40 * 26514 * 2
def baseEnd_26514 : Nat := 12101712065257331158285

theorem tailTrace_26514 : CollatzResearch.WordTrace tailWord_26514 prefixEnd_26514 12101712065257331158285 := by
  unfold tailWord_26514
  simp only [CollatzResearch.WordTrace]
  refine ⟨241761256487945268949649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 644696683967854050532397 241761256487945268949649)
  ·
    refine ⟨181320942365958951712237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241761256487945268949649 181320942365958951712237)
    ·
      refine ⟨67995353387234606892089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181320942365958951712237 67995353387234606892089)
      ·
        refine ⟨50996515040425955169067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67995353387234606892089 50996515040425955169067)
        ·
          refine ⟨76494772560638932753601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50996515040425955169067 76494772560638932753601)
          ·
            refine ⟨57371079420479199565201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76494772560638932753601 57371079420479199565201)
            ·
              refine ⟨43028309565359399673901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57371079420479199565201 43028309565359399673901)
              ·
                refine ⟨16135616087009774877713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43028309565359399673901 16135616087009774877713)
                ·
                  refine ⟨12101712065257331158285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16135616087009774877713 12101712065257331158285)
                  ·
                    rfl

theorem cell20_26514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_26514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26514 prefixEnd_26514 := by exact prefixLift 26514
  have htrace : WordTrace (prefixWord ++ tailWord_26514) baseStart_26514 baseEnd_26514 := by
    simpa [prefixWord, tailWord_26514, baseEnd_26514] using wordTrace_append hprefix tailTrace_26514
  have hstable : (prefixWord ++ tailWord_26514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26514).length < 2 ^ (prefixWord ++ tailWord_26514).sum := by decide
  have hdescent : baseEnd_26514 < baseStart_26514 := by decide
  rcases family_descends (prefixWord ++ tailWord_26514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26532 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 5]
def baseStart_26532 : Nat := 118140960795 + 26532 * 2 ^ 59
def prefixEnd_26532 : Nat := 4983230072969 + 3 ^ 40 * 26532 * 2
def baseEnd_26532 : Nat := 12109927755729268558211

theorem tailTrace_26532 : CollatzResearch.WordTrace tailWord_26532 prefixEnd_26532 12109927755729268558211 := by
  unfold tailWord_26532
  simp only [CollatzResearch.WordTrace]
  refine ⟨483850769943285074976925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 645134359924380099969233 483850769943285074976925)
  ·
    refine ⟨181444038728731903116347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 483850769943285074976925 181444038728731903116347)
    ·
      refine ⟨272166058093097854674521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181444038728731903116347 272166058093097854674521)
      ·
        refine ⟨204124543569823391005891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272166058093097854674521 204124543569823391005891)
        ·
          refine ⟨306186815354735086508837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204124543569823391005891 306186815354735086508837)
          ·
            refine ⟨57410027879012828720407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 306186815354735086508837 57410027879012828720407)
            ·
              refine ⟨86115041818519243080611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57410027879012828720407 86115041818519243080611)
              ·
                refine ⟨129172562727778864620917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86115041818519243080611 129172562727778864620917)
                ·
                  refine ⟨12109927755729268558211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129172562727778864620917 12109927755729268558211)
                  ·
                    rfl

theorem cell20_26532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_26532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26532 prefixEnd_26532 := by exact prefixLift 26532
  have htrace : WordTrace (prefixWord ++ tailWord_26532) baseStart_26532 baseEnd_26532 := by
    simpa [prefixWord, tailWord_26532, baseEnd_26532] using wordTrace_append hprefix tailTrace_26532
  have hstable : (prefixWord ++ tailWord_26532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26532).length < 2 ^ (prefixWord ++ tailWord_26532).sum := by decide
  have hdescent : baseEnd_26532 < baseStart_26532 := by decide
  rcases family_descends (prefixWord ++ tailWord_26532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26535 : List Nat := [1, 1, 6, 1, 2, 1, 2, 4, 2]
def baseStart_26535 : Nat := 118140960795 + 26535 * 2 ^ 59
def prefixEnd_26535 : Nat := 4983230072969 + 3 ^ 40 * 26535 * 2
def baseEnd_26535 : Nat := 12111297037474591458199

theorem tailTrace_26535 : CollatzResearch.WordTrace tailWord_26535 prefixEnd_26535 12111297037474591458199 := by
  unfold tailWord_26535
  simp only [CollatzResearch.WordTrace]
  refine ⟨967810958875701662313059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 645207305917134441542039 967810958875701662313059)
  ·
    refine ⟨1451716438313552493469589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 967810958875701662313059 1451716438313552493469589)
    ·
      refine ⟨68049208045947773131387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1451716438313552493469589 68049208045947773131387)
      ·
        refine ⟨102073812068921659697081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68049208045947773131387 102073812068921659697081)
        ·
          refine ⟨76555359051691244772811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102073812068921659697081 76555359051691244772811)
          ·
            refine ⟨114833038577536867159217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76555359051691244772811 114833038577536867159217)
            ·
              refine ⟨86124778933152650369413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114833038577536867159217 86124778933152650369413)
              ·
                refine ⟨16148396049966121944265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86124778933152650369413 16148396049966121944265)
                ·
                  refine ⟨12111297037474591458199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16148396049966121944265 12111297037474591458199)
                  ·
                    rfl

theorem cell20_26535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 2].length) (baseStart_26535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26535 prefixEnd_26535 := by exact prefixLift 26535
  have htrace : WordTrace (prefixWord ++ tailWord_26535) baseStart_26535 baseEnd_26535 := by
    simpa [prefixWord, tailWord_26535, baseEnd_26535] using wordTrace_append hprefix tailTrace_26535
  have hstable : (prefixWord ++ tailWord_26535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26535).length < 2 ^ (prefixWord ++ tailWord_26535).sum := by decide
  have hdescent : baseEnd_26535 < baseStart_26535 := by decide
  rcases family_descends (prefixWord ++ tailWord_26535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26632 : List Nat := [2, 1, 3, 2, 1, 2, 2, 5, 2]
def baseStart_26632 : Nat := 118140960795 + 26632 * 2 ^ 59
def prefixEnd_26632 : Nat := 4983230072969 + 3 ^ 40 * 26632 * 2
def baseEnd_26632 : Nat := 12155570480573365224469

theorem tailTrace_26632 : CollatzResearch.WordTrace tailWord_26632 prefixEnd_26632 12155570480573365224469 := by
  unfold tailWord_26632
  simp only [CollatzResearch.WordTrace]
  refine ⟨485674419762143614297075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 647565893016191485729433 485674419762143614297075)
  ·
    refine ⟨728511629643215421445613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 485674419762143614297075 728511629643215421445613)
    ·
      refine ⟨273191861116205783042105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 728511629643215421445613 273191861116205783042105)
      ·
        refine ⟨204893895837154337281579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273191861116205783042105 204893895837154337281579)
        ·
          refine ⟨307340843755731505922369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204893895837154337281579 307340843755731505922369)
          ·
            refine ⟨230505632816798629441777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307340843755731505922369 230505632816798629441777)
            ·
              refine ⟨172879224612598972081333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230505632816798629441777 172879224612598972081333)
              ·
                refine ⟨16207427307431153632625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 172879224612598972081333 16207427307431153632625)
                ·
                  refine ⟨12155570480573365224469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16207427307431153632625 12155570480573365224469)
                  ·
                    rfl

theorem cell20_26632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 2].length) (baseStart_26632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26632 prefixEnd_26632 := by exact prefixLift 26632
  have htrace : WordTrace (prefixWord ++ tailWord_26632) baseStart_26632 baseEnd_26632 := by
    simpa [prefixWord, tailWord_26632, baseEnd_26632] using wordTrace_append hprefix tailTrace_26632
  have hstable : (prefixWord ++ tailWord_26632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26632).length < 2 ^ (prefixWord ++ tailWord_26632).sum := by decide
  have hdescent : baseEnd_26632 < baseStart_26632 := by decide
  rcases family_descends (prefixWord ++ tailWord_26632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26645 : List Nat := [1, 3, 2, 1, 6, 1, 2, 2, 2]
def baseStart_26645 : Nat := 118140960795 + 26645 * 2 ^ 59
def prefixEnd_26645 : Nat := 4983230072969 + 3 ^ 40 * 26645 * 2
def baseEnd_26645 : Nat := 12161504034803097791083

theorem tailTrace_26645 : CollatzResearch.WordTrace tailWord_26645 prefixEnd_26645 12161504034803097791083 := by
  unfold tailWord_26645
  simp only [CollatzResearch.WordTrace]
  refine ⟨971822988477190448817389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 647881992318126965878259 971822988477190448817389)
  ·
    refine ⟨364433620678946418306521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 971822988477190448817389 364433620678946418306521)
    ·
      refine ⟨273325215509209813729891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364433620678946418306521 273325215509209813729891)
      ·
        refine ⟨409987823263814720594837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273325215509209813729891 409987823263814720594837)
        ·
          refine ⟨19218179215491315027883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 409987823263814720594837 19218179215491315027883)
          ·
            refine ⟨28827268823236972541825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19218179215491315027883 28827268823236972541825)
            ·
              refine ⟨21620451617427729406369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28827268823236972541825 21620451617427729406369)
              ·
                refine ⟨16215338713070797054777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21620451617427729406369 16215338713070797054777)
                ·
                  refine ⟨12161504034803097791083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16215338713070797054777 12161504034803097791083)
                  ·
                    rfl

theorem cell20_26645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 2].length) (baseStart_26645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26645 prefixEnd_26645 := by exact prefixLift 26645
  have htrace : WordTrace (prefixWord ++ tailWord_26645) baseStart_26645 baseEnd_26645 := by
    simpa [prefixWord, tailWord_26645, baseEnd_26645] using wordTrace_append hprefix tailTrace_26645
  have hstable : (prefixWord ++ tailWord_26645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26645).length < 2 ^ (prefixWord ++ tailWord_26645).sum := by decide
  have hdescent : baseEnd_26645 < baseStart_26645 := by decide
  rcases family_descends (prefixWord ++ tailWord_26645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26670 : List Nat := [4, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_26670 : Nat := 118140960795 + 26670 * 2 ^ 59
def prefixEnd_26670 : Nat := 4983230072969 + 3 ^ 40 * 26670 * 2
def baseEnd_26670 : Nat := 12172914716014121957647

theorem tailTrace_26670 : CollatzResearch.WordTrace tailWord_26670 prefixEnd_26670 12172914716014121957647 := by
  unfold tailWord_26670
  simp only [CollatzResearch.WordTrace]
  refine ⟨121591851673327464809683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 648489875591079812318309 121591851673327464809683)
  ·
    refine ⟨182387777509991197214525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121591851673327464809683 182387777509991197214525)
    ·
      refine ⟨68395416566246698955447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182387777509991197214525 68395416566246698955447)
      ·
        refine ⟨102593124849370048433171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68395416566246698955447 102593124849370048433171)
        ·
          refine ⟨153889687274055072649757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102593124849370048433171 153889687274055072649757)
          ·
            refine ⟨57708632727770652243659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153889687274055072649757 57708632727770652243659)
            ·
              refine ⟨86562949091655978365489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57708632727770652243659 86562949091655978365489)
              ·
                refine ⟨64922211818741983774117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86562949091655978365489 64922211818741983774117)
                ·
                  refine ⟨12172914716014121957647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64922211818741983774117 12172914716014121957647)
                  ·
                    rfl

theorem cell20_26670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_26670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26670 prefixEnd_26670 := by exact prefixLift 26670
  have htrace : WordTrace (prefixWord ++ tailWord_26670) baseStart_26670 baseEnd_26670 := by
    simpa [prefixWord, tailWord_26670, baseEnd_26670] using wordTrace_append hprefix tailTrace_26670
  have hstable : (prefixWord ++ tailWord_26670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26670).length < 2 ^ (prefixWord ++ tailWord_26670).sum := by decide
  have hdescent : baseEnd_26670 < baseStart_26670 := by decide
  rcases family_descends (prefixWord ++ tailWord_26670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26736 : List Nat := [2, 1, 1, 1, 5, 3, 1, 6]
def baseStart_26736 : Nat := 118140960795 + 26736 * 2 ^ 59
def prefixEnd_26736 : Nat := 4983230072969 + 3 ^ 40 * 26736 * 2
def baseEnd_26736 : Nat := 4067679638137075252459

theorem tailTrace_26736 : CollatzResearch.WordTrace tailWord_26736 prefixEnd_26736 4067679638137075252459 := by
  unfold tailWord_26736
  simp only [CollatzResearch.WordTrace]
  refine ⟨487571015573756495190031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 650094687431675326920041 487571015573756495190031)
  ·
    refine ⟨731356523360634742785047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 487571015573756495190031 731356523360634742785047)
    ·
      refine ⟨1097034785040952114177571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 731356523360634742785047 1097034785040952114177571)
      ·
        refine ⟨1645552177561428171266357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1097034785040952114177571 1645552177561428171266357)
        ·
          refine ⟨154270516646383891056221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1645552177561428171266357 154270516646383891056221)
          ·
            refine ⟨57851443742393959146083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154270516646383891056221 57851443742393959146083)
            ·
              refine ⟨86777165613590938719125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57851443742393959146083 86777165613590938719125)
              ·
                refine ⟨4067679638137075252459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86777165613590938719125 4067679638137075252459)
                ·
                  rfl

theorem cell20_26736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_26736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26736 prefixEnd_26736 := by exact prefixLift 26736
  have htrace : WordTrace (prefixWord ++ tailWord_26736) baseStart_26736 baseEnd_26736 := by
    simpa [prefixWord, tailWord_26736, baseEnd_26736] using wordTrace_append hprefix tailTrace_26736
  have hstable : (prefixWord ++ tailWord_26736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26736).length < 2 ^ (prefixWord ++ tailWord_26736).sum := by decide
  have hdescent : baseEnd_26736 < baseStart_26736 := by decide
  rcases family_descends (prefixWord ++ tailWord_26736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26742 : List Nat := [5, 1, 1, 2, 1, 4, 1, 3, 2]
def baseStart_26742 : Nat := 118140960795 + 26742 * 2 ^ 59
def prefixEnd_26742 : Nat := 4983230072969 + 3 ^ 40 * 26742 * 2
def baseEnd_26742 : Nat := 12205777477901871557353

theorem tailTrace_26742 : CollatzResearch.WordTrace tailWord_26742 prefixEnd_26742 12205777477901871557353 := by
  unfold tailWord_26742
  simp only [CollatzResearch.WordTrace]
  refine ⟨60960054320361000943655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 650240579417184010065653 60960054320361000943655)
  ·
    refine ⟨91440081480541501415483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60960054320361000943655 91440081480541501415483)
    ·
      refine ⟨137160122220812252123225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91440081480541501415483 137160122220812252123225)
      ·
        refine ⟨102870091665609189092419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137160122220812252123225 102870091665609189092419)
        ·
          refine ⟨154305137498413783638629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102870091665609189092419 154305137498413783638629)
          ·
            refine ⟨28932213280952584432243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154305137498413783638629 28932213280952584432243)
            ·
              refine ⟨43398319921428876648365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28932213280952584432243 43398319921428876648365)
              ·
                refine ⟨16274369970535828743137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43398319921428876648365 16274369970535828743137)
                ·
                  refine ⟨12205777477901871557353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16274369970535828743137 12205777477901871557353)
                  ·
                    rfl

theorem cell20_26742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_26742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26742 prefixEnd_26742 := by exact prefixLift 26742
  have htrace : WordTrace (prefixWord ++ tailWord_26742) baseStart_26742 baseEnd_26742 := by
    simpa [prefixWord, tailWord_26742, baseEnd_26742] using wordTrace_append hprefix tailTrace_26742
  have hstable : (prefixWord ++ tailWord_26742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26742).length < 2 ^ (prefixWord ++ tailWord_26742).sum := by decide
  have hdescent : baseEnd_26742 < baseStart_26742 := by decide
  rcases family_descends (prefixWord ++ tailWord_26742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26743 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 5]
def baseStart_26743 : Nat := 118140960795 + 26743 * 2 ^ 59
def prefixEnd_26743 : Nat := 4983230072969 + 3 ^ 40 * 26743 * 2
def baseEnd_26743 : Nat := 12206233905150312524015

theorem tailTrace_26743 : CollatzResearch.WordTrace tailWord_26743 prefixEnd_26743 12206233905150312524015 := by
  unfold tailWord_26743
  simp only [CollatzResearch.WordTrace]
  refine ⟨975397342122153185884883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 650264894748102123923255 975397342122153185884883)
  ·
    refine ⟨1463096013183229778827325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 975397342122153185884883 1463096013183229778827325)
    ·
      refine ⟨548661004943711167060247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1463096013183229778827325 548661004943711167060247)
      ·
        refine ⟨822991507415566750590371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548661004943711167060247 822991507415566750590371)
        ·
          refine ⟨1234487261123350125885557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822991507415566750590371 1234487261123350125885557)
          ·
            refine ⟨115733180730314074301771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1234487261123350125885557 115733180730314074301771)
            ·
              refine ⟨173599771095471111452657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115733180730314074301771 173599771095471111452657)
              ·
                refine ⟨130199828321603333589493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173599771095471111452657 130199828321603333589493)
                ·
                  refine ⟨12206233905150312524015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130199828321603333589493 12206233905150312524015)
                  ·
                    rfl

theorem cell20_26743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 5].length) (baseStart_26743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26743 prefixEnd_26743 := by exact prefixLift 26743
  have htrace : WordTrace (prefixWord ++ tailWord_26743) baseStart_26743 baseEnd_26743 := by
    simpa [prefixWord, tailWord_26743, baseEnd_26743] using wordTrace_append hprefix tailTrace_26743
  have hstable : (prefixWord ++ tailWord_26743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26743).length < 2 ^ (prefixWord ++ tailWord_26743).sum := by decide
  have hdescent : baseEnd_26743 < baseStart_26743 := by decide
  rcases family_descends (prefixWord ++ tailWord_26743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26753 : List Nat := [1, 2, 4, 2, 3, 2, 6]
def baseStart_26753 : Nat := 118140960795 + 26753 * 2 ^ 59
def prefixEnd_26753 : Nat := 4983230072969 + 3 ^ 40 * 26753 * 2
def baseEnd_26753 : Nat := 1356755353070524687849

theorem tailTrace_26753 : CollatzResearch.WordTrace tailWord_26753 prefixEnd_26753 1356755353070524687849 := by
  unfold tailWord_26753
  simp only [CollatzResearch.WordTrace]
  refine ⟨975762072085924893748913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 650508048057283262499275 975762072085924893748913)
  ·
    refine ⟨731821554064443670311685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 975762072085924893748913 731821554064443670311685)
    ·
      refine ⟨137216541387083188183441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 731821554064443670311685 137216541387083188183441)
      ·
        refine ⟨102912406040312391137581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137216541387083188183441 102912406040312391137581)
        ·
          refine ⟨38592152265117146676593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102912406040312391137581 38592152265117146676593)
          ·
            refine ⟨28944114198837860007445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38592152265117146676593 28944114198837860007445)
            ·
              refine ⟨1356755353070524687849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28944114198837860007445 1356755353070524687849)
              ·
                rfl

theorem cell20_26753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 6].length) (baseStart_26753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26753 prefixEnd_26753 := by exact prefixLift 26753
  have htrace : WordTrace (prefixWord ++ tailWord_26753) baseStart_26753 baseEnd_26753 := by
    simpa [prefixWord, tailWord_26753, baseEnd_26753] using wordTrace_append hprefix tailTrace_26753
  have hstable : (prefixWord ++ tailWord_26753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26753).length < 2 ^ (prefixWord ++ tailWord_26753).sum := by decide
  have hdescent : baseEnd_26753 < baseStart_26753 := by decide
  rcases family_descends (prefixWord ++ tailWord_26753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26760 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 5]
def baseStart_26760 : Nat := 118140960795 + 26760 * 2 ^ 59
def prefixEnd_26760 : Nat := 4983230072969 + 3 ^ 40 * 26760 * 2
def baseEnd_26760 : Nat := 12213993168373808957279

theorem tailTrace_26760 : CollatzResearch.WordTrace tailWord_26760 prefixEnd_26760 12213993168373808957279 := by
  unfold tailWord_26760
  simp only [CollatzResearch.WordTrace]
  refine ⟨488008691530282544626867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 650678255373710059502489 488008691530282544626867)
  ·
    refine ⟨732013037295423816940301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 488008691530282544626867 732013037295423816940301)
    ·
      refine ⟨274504888985783931352613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 732013037295423816940301 274504888985783931352613)
      ·
        refine ⟨51469666684834487128615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 274504888985783931352613 51469666684834487128615)
        ·
          refine ⟨77204500027251730692923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51469666684834487128615 77204500027251730692923)
          ·
            refine ⟨115806750040877596039385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77204500027251730692923 115806750040877596039385)
            ·
              refine ⟨86855062530658197029539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115806750040877596039385 86855062530658197029539)
              ·
                refine ⟨130282593795987295544309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86855062530658197029539 130282593795987295544309)
                ·
                  refine ⟨12213993168373808957279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130282593795987295544309 12213993168373808957279)
                  ·
                    rfl

theorem cell20_26760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_26760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26760 prefixEnd_26760 := by exact prefixLift 26760
  have htrace : WordTrace (prefixWord ++ tailWord_26760) baseStart_26760 baseEnd_26760 := by
    simpa [prefixWord, tailWord_26760, baseEnd_26760] using wordTrace_append hprefix tailTrace_26760
  have hstable : (prefixWord ++ tailWord_26760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26760).length < 2 ^ (prefixWord ++ tailWord_26760).sum := by decide
  have hdescent : baseEnd_26760 < baseStart_26760 := by decide
  rcases family_descends (prefixWord ++ tailWord_26760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26812 : List Nat := [2, 2, 2, 3, 3, 8]
def baseStart_26812 : Nat := 118140960795 + 26812 * 2 ^ 59
def prefixEnd_26812 : Nat := 4983230072969 + 3 ^ 40 * 26812 * 2
def baseEnd_26812 : Nat := 453249162418249600879

theorem tailTrace_26812 : CollatzResearch.WordTrace tailWord_26812 prefixEnd_26812 453249162418249600879 := by
  unfold tailWord_26812
  simp only [CollatzResearch.WordTrace]
  refine ⟨488956989436088985073345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 651942652581451980097793 488956989436088985073345)
  ·
    refine ⟨366717742077066738805009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 488956989436088985073345 366717742077066738805009)
    ·
      refine ⟨275038306557800054103757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366717742077066738805009 275038306557800054103757)
      ·
        refine ⟨103139364959175020288909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275038306557800054103757 103139364959175020288909)
        ·
          refine ⟨38677261859690632608341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103139364959175020288909 38677261859690632608341)
          ·
            refine ⟨453249162418249600879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 38677261859690632608341 453249162418249600879)
            ·
              rfl

theorem cell20_26812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 8].length) (baseStart_26812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26812 prefixEnd_26812 := by exact prefixLift 26812
  have htrace : WordTrace (prefixWord ++ tailWord_26812) baseStart_26812 baseEnd_26812 := by
    simpa [prefixWord, tailWord_26812, baseEnd_26812] using wordTrace_append hprefix tailTrace_26812
  have hstable : (prefixWord ++ tailWord_26812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26812).length < 2 ^ (prefixWord ++ tailWord_26812).sum := by decide
  have hdescent : baseEnd_26812 < baseStart_26812 := by decide
  rcases family_descends (prefixWord ++ tailWord_26812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26860 : List Nat := [2, 2, 1, 1, 2, 3, 4, 3, 2]
def baseStart_26860 : Nat := 118140960795 + 26860 * 2 ^ 59
def prefixEnd_26860 : Nat := 4983230072969 + 3 ^ 40 * 26860 * 2
def baseEnd_26860 : Nat := 12259635893217905623537

theorem tailTrace_26860 : CollatzResearch.WordTrace tailWord_26860 prefixEnd_26860 12259635893217905623537 := by
  unfold tailWord_26860
  simp only [CollatzResearch.WordTrace]
  refine ⟨489832341349141083947017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 653109788465521445262689 489832341349141083947017)
  ·
    refine ⟨367374256011855812960263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 489832341349141083947017 367374256011855812960263)
    ·
      refine ⟨551061384017783719440395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367374256011855812960263 551061384017783719440395)
      ·
        refine ⟨826592076026675579160593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551061384017783719440395 826592076026675579160593)
        ·
          refine ⟨619944057020006684370445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 826592076026675579160593 619944057020006684370445)
          ·
            refine ⟨232479021382502506638917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 619944057020006684370445 232479021382502506638917)
            ·
              refine ⟨43589816509219219994797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 232479021382502506638917 43589816509219219994797)
              ·
                refine ⟨16346181190957207498049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43589816509219219994797 16346181190957207498049)
                ·
                  refine ⟨12259635893217905623537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16346181190957207498049 12259635893217905623537)
                  ·
                    rfl

theorem cell20_26860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 2].length) (baseStart_26860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26860 prefixEnd_26860 := by exact prefixLift 26860
  have htrace : WordTrace (prefixWord ++ tailWord_26860) baseStart_26860 baseEnd_26860 := by
    simpa [prefixWord, tailWord_26860, baseEnd_26860] using wordTrace_append hprefix tailTrace_26860
  have hstable : (prefixWord ++ tailWord_26860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26860).length < 2 ^ (prefixWord ++ tailWord_26860).sum := by decide
  have hdescent : baseEnd_26860 < baseStart_26860 := by decide
  rcases family_descends (prefixWord ++ tailWord_26860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26874 : List Nat := [3, 1, 1, 1, 1, 5, 3, 2, 3]
def baseStart_26874 : Nat := 118140960795 + 26874 * 2 ^ 59
def prefixEnd_26874 : Nat := 4983230072969 + 3 ^ 40 * 26874 * 2
def baseEnd_26874 : Nat := 12266025874696079156813

theorem tailTrace_26874 : CollatzResearch.WordTrace tailWord_26874 prefixEnd_26874 12266025874696079156813 := by
  unfold tailWord_26874
  simp only [CollatzResearch.WordTrace]
  refine ⟨245043826161890639725919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 653450203098375039269117 245043826161890639725919)
  ·
    refine ⟨367565739242835959588879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245043826161890639725919 367565739242835959588879)
    ·
      refine ⟨551348608864253939383319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367565739242835959588879 551348608864253939383319)
      ·
        refine ⟨827022913296380909074979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551348608864253939383319 827022913296380909074979)
        ·
          refine ⟨1240534369944571363612469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 827022913296380909074979 1240534369944571363612469)
          ·
            refine ⟨116300097182303565338669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1240534369944571363612469 116300097182303565338669)
            ·
              refine ⟨43612536443363837002001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116300097182303565338669 43612536443363837002001)
              ·
                refine ⟨32709402332522877751501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43612536443363837002001 32709402332522877751501)
                ·
                  refine ⟨12266025874696079156813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32709402332522877751501 12266025874696079156813)
                  ·
                    rfl

theorem cell20_26874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_26874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26874 prefixEnd_26874 := by exact prefixLift 26874
  have htrace : WordTrace (prefixWord ++ tailWord_26874) baseStart_26874 baseEnd_26874 := by
    simpa [prefixWord, tailWord_26874, baseEnd_26874] using wordTrace_append hprefix tailTrace_26874
  have hstable : (prefixWord ++ tailWord_26874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26874).length < 2 ^ (prefixWord ++ tailWord_26874).sum := by decide
  have hdescent : baseEnd_26874 < baseStart_26874 := by decide
  rcases family_descends (prefixWord ++ tailWord_26874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26881 : List Nat := [1, 2, 4, 1, 1, 2, 4, 1, 4]
def baseStart_26881 : Nat := 118140960795 + 26881 * 2 ^ 59
def prefixEnd_26881 : Nat := 4983230072969 + 3 ^ 40 * 26881 * 2
def baseEnd_26881 : Nat := 12269220865435165923451

theorem tailTrace_26881 : CollatzResearch.WordTrace tailWord_26881 prefixEnd_26881 12269220865435165923451 := by
  unfold tailWord_26881
  simp only [CollatzResearch.WordTrace]
  refine ⟨980430615622202754408497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 653620410414801836272331 980430615622202754408497)
  ·
    refine ⟨735322961716652065806373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 980430615622202754408497 735322961716652065806373)
    ·
      refine ⟨137873055321872262338695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 735322961716652065806373 137873055321872262338695)
      ·
        refine ⟨206809582982808393508043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137873055321872262338695 206809582982808393508043)
        ·
          refine ⟨310214374474212590262065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206809582982808393508043 310214374474212590262065)
          ·
            refine ⟨232660780855659442696549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310214374474212590262065 232660780855659442696549)
            ·
              refine ⟨43623896410436145505603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 232660780855659442696549 43623896410436145505603)
              ·
                refine ⟨65435844615654218258405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43623896410436145505603 65435844615654218258405)
                ·
                  refine ⟨12269220865435165923451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65435844615654218258405 12269220865435165923451)
                  ·
                    rfl

theorem cell20_26881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_26881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26881 prefixEnd_26881 := by exact prefixLift 26881
  have htrace : WordTrace (prefixWord ++ tailWord_26881) baseStart_26881 baseEnd_26881 := by
    simpa [prefixWord, tailWord_26881, baseEnd_26881] using wordTrace_append hprefix tailTrace_26881
  have hstable : (prefixWord ++ tailWord_26881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26881).length < 2 ^ (prefixWord ++ tailWord_26881).sum := by decide
  have hdescent : baseEnd_26881 < baseStart_26881 := by decide
  rcases family_descends (prefixWord ++ tailWord_26881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26895 : List Nat := [1, 1, 2, 1, 1, 1, 3, 7, 3]
def baseStart_26895 : Nat := 118140960795 + 26895 * 2 ^ 59
def prefixEnd_26895 : Nat := 4983230072969 + 3 ^ 40 * 26895 * 2
def baseEnd_26895 : Nat := 12275610846913339456727

theorem tailTrace_26895 : CollatzResearch.WordTrace tailWord_26895 prefixEnd_26895 12275610846913339456727 := by
  unfold tailWord_26895
  simp only [CollatzResearch.WordTrace]
  refine ⟨980941237571483145418139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 653960825047655430278759 980941237571483145418139)
  ·
    refine ⟨1471411856357224718127209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 980941237571483145418139 1471411856357224718127209)
    ·
      refine ⟨1103558892267918538595407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1471411856357224718127209 1103558892267918538595407)
      ·
        refine ⟨1655338338401877807893111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1103558892267918538595407 1655338338401877807893111)
        ·
          refine ⟨2483007507602816711839667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1655338338401877807893111 2483007507602816711839667)
          ·
            refine ⟨3724511261404225067759501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2483007507602816711839667 3724511261404225067759501)
            ·
              refine ⟨1396691723026584400409813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3724511261404225067759501 1396691723026584400409813)
              ·
                refine ⟨32734962258435571884605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1396691723026584400409813 32734962258435571884605)
                ·
                  refine ⟨12275610846913339456727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32734962258435571884605 12275610846913339456727)
                  ·
                    rfl

theorem cell20_26895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 3].length) (baseStart_26895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26895 prefixEnd_26895 := by exact prefixLift 26895
  have htrace : WordTrace (prefixWord ++ tailWord_26895) baseStart_26895 baseEnd_26895 := by
    simpa [prefixWord, tailWord_26895, baseEnd_26895] using wordTrace_append hprefix tailTrace_26895
  have hstable : (prefixWord ++ tailWord_26895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26895).length < 2 ^ (prefixWord ++ tailWord_26895).sum := by decide
  have hdescent : baseEnd_26895 < baseStart_26895 := by decide
  rcases family_descends (prefixWord ++ tailWord_26895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26922 : List Nat := [3, 1, 4, 2, 3, 1, 6]
def baseStart_26922 : Nat := 118140960795 + 26922 * 2 ^ 59
def prefixEnd_26922 : Nat := 4983230072969 + 3 ^ 40 * 26922 * 2
def baseEnd_26922 : Nat := 1365326042513471728513

theorem tailTrace_26922 : CollatzResearch.WordTrace tailWord_26922 prefixEnd_26922 1365326042513471728513 := by
  unfold tailWord_26922
  simp only [CollatzResearch.WordTrace]
  refine ⟨245481502118416689162755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 654617338982444504434013 245481502118416689162755)
  ·
    refine ⟨368222253177625033744133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245481502118416689162755 368222253177625033744133)
    ·
      refine ⟨69041672470804693827025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 368222253177625033744133 69041672470804693827025)
      ·
        refine ⟨51781254353103520370269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69041672470804693827025 51781254353103520370269)
        ·
          refine ⟨19417970382413820138851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51781254353103520370269 19417970382413820138851)
          ·
            refine ⟨29126955573620730208277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19417970382413820138851 29126955573620730208277)
            ·
              refine ⟨1365326042513471728513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29126955573620730208277 1365326042513471728513)
              ·
                rfl

theorem cell20_26922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 6].length) (baseStart_26922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26922 prefixEnd_26922 := by exact prefixLift 26922
  have htrace : WordTrace (prefixWord ++ tailWord_26922) baseStart_26922 baseEnd_26922 := by
    simpa [prefixWord, tailWord_26922, baseEnd_26922] using wordTrace_append hprefix tailTrace_26922
  have hstable : (prefixWord ++ tailWord_26922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26922).length < 2 ^ (prefixWord ++ tailWord_26922).sum := by decide
  have hdescent : baseEnd_26922 < baseStart_26922 := by decide
  rcases family_descends (prefixWord ++ tailWord_26922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26932 : List Nat := [2, 5, 1, 1, 1, 3, 3, 2, 2]
def baseStart_26932 : Nat := 118140960795 + 26932 * 2 ^ 59
def prefixEnd_26932 : Nat := 4983230072969 + 3 ^ 40 * 26932 * 2
def baseEnd_26932 : Nat := 12292498655105655223243

theorem tailTrace_26932 : CollatzResearch.WordTrace tailWord_26932 prefixEnd_26932 12292498655105655223243 := by
  unfold tailWord_26932
  simp only [CollatzResearch.WordTrace]
  refine ⟨491145369218719232257525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 654860492291625643010033 491145369218719232257525)
  ·
    refine ⟨46044878364254928024143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 491145369218719232257525 46044878364254928024143)
    ·
      refine ⟨69067317546382392036215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46044878364254928024143 69067317546382392036215)
      ·
        refine ⟨103600976319573588054323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69067317546382392036215 103600976319573588054323)
        ·
          refine ⟨155401464479360382081485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103600976319573588054323 155401464479360382081485)
          ·
            refine ⟨58275549179760143280557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155401464479360382081485 58275549179760143280557)
            ·
              refine ⟨21853330942410053730209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58275549179760143280557 21853330942410053730209)
              ·
                refine ⟨16389998206807540297657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21853330942410053730209 16389998206807540297657)
                ·
                  refine ⟨12292498655105655223243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16389998206807540297657 12292498655105655223243)
                  ·
                    rfl

theorem cell20_26932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_26932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26932 prefixEnd_26932 := by exact prefixLift 26932
  have htrace : WordTrace (prefixWord ++ tailWord_26932) baseStart_26932 baseEnd_26932 := by
    simpa [prefixWord, tailWord_26932, baseEnd_26932] using wordTrace_append hprefix tailTrace_26932
  have hstable : (prefixWord ++ tailWord_26932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26932).length < 2 ^ (prefixWord ++ tailWord_26932).sum := by decide
  have hdescent : baseEnd_26932 < baseStart_26932 := by decide
  rcases family_descends (prefixWord ++ tailWord_26932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26933 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 5]
def baseStart_26933 : Nat := 118140960795 + 26933 * 2 ^ 59
def prefixEnd_26933 : Nat := 4983230072969 + 3 ^ 40 * 26933 * 2
def baseEnd_26933 : Nat := 12292955082354096189905

theorem tailTrace_26933 : CollatzResearch.WordTrace tailWord_26933 prefixEnd_26933 12292955082354096189905 := by
  unfold tailWord_26933
  simp only [CollatzResearch.WordTrace]
  refine ⟨982327211433815635301453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 654884807622543756867635 982327211433815635301453)
  ·
    refine ⟨368372704287680863238045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 982327211433815635301453 368372704287680863238045)
    ·
      refine ⟨138139764107880323714267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368372704287680863238045 138139764107880323714267)
      ·
        refine ⟨207209646161820485571401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138139764107880323714267 207209646161820485571401)
        ·
          refine ⟨155407234621365364178551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207209646161820485571401 155407234621365364178551)
          ·
            refine ⟨233110851932048046267827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155407234621365364178551 233110851932048046267827)
            ·
              refine ⟨349666277898072069401741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233110851932048046267827 349666277898072069401741)
              ·
                refine ⟨131124854211777026025653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 349666277898072069401741 131124854211777026025653)
                ·
                  refine ⟨12292955082354096189905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131124854211777026025653 12292955082354096189905)
                  ·
                    rfl

theorem cell20_26933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_26933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26933 prefixEnd_26933 := by exact prefixLift 26933
  have htrace : WordTrace (prefixWord ++ tailWord_26933) baseStart_26933 baseEnd_26933 := by
    simpa [prefixWord, tailWord_26933, baseEnd_26933] using wordTrace_append hprefix tailTrace_26933
  have hstable : (prefixWord ++ tailWord_26933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26933).length < 2 ^ (prefixWord ++ tailWord_26933).sum := by decide
  have hdescent : baseEnd_26933 < baseStart_26933 := by decide
  rcases family_descends (prefixWord ++ tailWord_26933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26947 : List Nat := [1, 1, 1, 3, 1, 3, 3, 7]
def baseStart_26947 : Nat := 118140960795 + 26947 * 2 ^ 59
def prefixEnd_26947 : Nat := 4983230072969 + 3 ^ 40 * 26947 * 2
def baseEnd_26947 : Nat := 4099781687944089907727

theorem tailTrace_26947 : CollatzResearch.WordTrace tailWord_26947 prefixEnd_26947 4099781687944089907727 := by
  unfold tailWord_26947
  simp only [CollatzResearch.WordTrace]
  refine ⟨982837833383096026311095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 655225222255397350874063 982837833383096026311095)
  ·
    refine ⟨1474256750074644039466643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 982837833383096026311095 1474256750074644039466643)
    ·
      refine ⟨2211385125111966059199965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1474256750074644039466643 2211385125111966059199965)
      ·
        refine ⟨829269421916987272199987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2211385125111966059199965 829269421916987272199987)
        ·
          refine ⟨1243904132875480908299981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829269421916987272199987 1243904132875480908299981)
          ·
            refine ⟨466464049828305340612493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1243904132875480908299981 466464049828305340612493)
            ·
              refine ⟨174924018685614502729685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 466464049828305340612493 174924018685614502729685)
              ·
                refine ⟨4099781687944089907727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 174924018685614502729685 4099781687944089907727)
                ·
                  rfl

theorem cell20_26947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 7].length) (baseStart_26947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26947 prefixEnd_26947 := by exact prefixLift 26947
  have htrace : WordTrace (prefixWord ++ tailWord_26947) baseStart_26947 baseEnd_26947 := by
    simpa [prefixWord, tailWord_26947, baseEnd_26947] using wordTrace_append hprefix tailTrace_26947
  have hstable : (prefixWord ++ tailWord_26947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26947).length < 2 ^ (prefixWord ++ tailWord_26947).sum := by decide
  have hdescent : baseEnd_26947 < baseStart_26947 := by decide
  rcases family_descends (prefixWord ++ tailWord_26947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26964 : List Nat := [2, 4, 1, 1, 2, 2, 2, 6]
def baseStart_26964 : Nat := 118140960795 + 26964 * 2 ^ 59
def prefixEnd_26964 : Nat := 4983230072969 + 3 ^ 40 * 26964 * 2
def baseEnd_26964 : Nat := 4102368109018588718815

theorem tailTrace_26964 : CollatzResearch.WordTrace tailWord_26964 prefixEnd_26964 4102368109018588718815 := by
  unfold tailWord_26964
  simp only [CollatzResearch.WordTrace]
  refine ⟨491728937160753964839973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 655638582881005286453297 491728937160753964839973)
  ·
    refine ⟨92199175717641368407495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 491728937160753964839973 92199175717641368407495)
    ·
      refine ⟨138298763576462052611243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92199175717641368407495 138298763576462052611243)
      ·
        refine ⟨207448145364693078916865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138298763576462052611243 207448145364693078916865)
        ·
          refine ⟨155586109023519809187649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207448145364693078916865 155586109023519809187649)
          ·
            refine ⟨116689581767639856890737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155586109023519809187649 116689581767639856890737)
            ·
              refine ⟨87517186325729892668053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116689581767639856890737 87517186325729892668053)
              ·
                refine ⟨4102368109018588718815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87517186325729892668053 4102368109018588718815)
                ·
                  rfl

theorem cell20_26964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_26964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26964 prefixEnd_26964 := by exact prefixLift 26964
  have htrace : WordTrace (prefixWord ++ tailWord_26964) baseStart_26964 baseEnd_26964 := by
    simpa [prefixWord, tailWord_26964, baseEnd_26964] using wordTrace_append hprefix tailTrace_26964
  have hstable : (prefixWord ++ tailWord_26964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26964).length < 2 ^ (prefixWord ++ tailWord_26964).sum := by decide
  have hdescent : baseEnd_26964 < baseStart_26964 := by decide
  rcases family_descends (prefixWord ++ tailWord_26964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26995 : List Nat := [1, 1, 1, 2, 2, 1, 2, 8, 2]
def baseStart_26995 : Nat := 118140960795 + 26995 * 2 ^ 59
def prefixEnd_26995 : Nat := 4983230072969 + 3 ^ 40 * 26995 * 2
def baseEnd_26995 : Nat := 12321253571757436122985

theorem tailTrace_26995 : CollatzResearch.WordTrace tailWord_26995 prefixEnd_26995 12321253571757436122985 := by
  unfold tailWord_26995
  simp only [CollatzResearch.WordTrace]
  refine ⟨984588537209200224058439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 656392358139466816038959 984588537209200224058439)
  ·
    refine ⟨1476882805813800336087659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 984588537209200224058439 1476882805813800336087659)
    ·
      refine ⟨2215324208720700504131489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1476882805813800336087659 2215324208720700504131489)
      ·
        refine ⟨1661493156540525378098617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2215324208720700504131489 1661493156540525378098617)
        ·
          refine ⟨1246119867405394033573963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1661493156540525378098617 1246119867405394033573963)
          ·
            refine ⟨1869179801108091050360945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1246119867405394033573963 1869179801108091050360945)
            ·
              refine ⟨1401884850831068287770709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1869179801108091050360945 1401884850831068287770709)
              ·
                refine ⟨16428338095676581497313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1401884850831068287770709 16428338095676581497313)
                ·
                  refine ⟨12321253571757436122985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16428338095676581497313 12321253571757436122985)
                  ·
                    rfl

theorem cell20_26995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 2].length) (baseStart_26995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_26995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_26995 prefixEnd_26995 := by exact prefixLift 26995
  have htrace : WordTrace (prefixWord ++ tailWord_26995) baseStart_26995 baseEnd_26995 := by
    simpa [prefixWord, tailWord_26995, baseEnd_26995] using wordTrace_append hprefix tailTrace_26995
  have hstable : (prefixWord ++ tailWord_26995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26995).length < 2 ^ (prefixWord ++ tailWord_26995).sum := by decide
  have hdescent : baseEnd_26995 < baseStart_26995 := by decide
  rcases family_descends (prefixWord ++ tailWord_26995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27084 : List Nat := [2, 2, 1, 4, 4, 1, 1, 3, 2]
def baseStart_27084 : Nat := 118140960795 + 27084 * 2 ^ 59
def prefixEnd_27084 : Nat := 4983230072969 + 3 ^ 40 * 27084 * 2
def baseEnd_27084 : Nat := 12361875596868682155955

theorem tailTrace_27084 : CollatzResearch.WordTrace tailWord_27084 prefixEnd_27084 12361875596868682155955 := by
  unfold tailWord_27084
  simp only [CollatzResearch.WordTrace]
  refine ⟨493917316943384212024153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 658556422591178949365537 493917316943384212024153)
  ·
    refine ⟨370437987707538159018115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 493917316943384212024153 370437987707538159018115)
    ·
      refine ⟨555656981561307238527173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370437987707538159018115 555656981561307238527173)
      ·
        refine ⟨104185684042745107223845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 555656981561307238527173 104185684042745107223845)
        ·
          refine ⟨19534815758014707604471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104185684042745107223845 19534815758014707604471)
          ·
            refine ⟨29302223637022061406707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19534815758014707604471 29302223637022061406707)
            ·
              refine ⟨43953335455533092110061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29302223637022061406707 43953335455533092110061)
              ·
                refine ⟨16482500795824909541273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43953335455533092110061 16482500795824909541273)
                ·
                  refine ⟨12361875596868682155955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16482500795824909541273 12361875596868682155955)
                  ·
                    rfl

theorem cell20_27084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 2].length) (baseStart_27084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27084 prefixEnd_27084 := by exact prefixLift 27084
  have htrace : WordTrace (prefixWord ++ tailWord_27084) baseStart_27084 baseEnd_27084 := by
    simpa [prefixWord, tailWord_27084, baseEnd_27084] using wordTrace_append hprefix tailTrace_27084
  have hstable : (prefixWord ++ tailWord_27084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27084).length < 2 ^ (prefixWord ++ tailWord_27084).sum := by decide
  have hdescent : baseEnd_27084 < baseStart_27084 := by decide
  rcases family_descends (prefixWord ++ tailWord_27084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27123 : List Nat := [1, 1, 1, 2, 2, 2, 5, 3, 3]
def baseStart_27123 : Nat := 118140960795 + 27123 * 2 ^ 59
def prefixEnd_27123 : Nat := 4983230072969 + 3 ^ 40 * 27123 * 2
def baseEnd_27123 : Nat := 12379676259557879855795

theorem tailTrace_27123 : CollatzResearch.WordTrace tailWord_27123 prefixEnd_27123 12379676259557879855795 := by
  unfold tailWord_27123
  simp only [CollatzResearch.WordTrace]
  refine ⟨989257080745478084718023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 659504720496985389812015 989257080745478084718023)
  ·
    refine ⟨1483885621118217127077035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 989257080745478084718023 1483885621118217127077035)
    ·
      refine ⟨2225828431677325690615553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1483885621118217127077035 2225828431677325690615553)
      ·
        refine ⟨1669371323757994267961665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2225828431677325690615553 1669371323757994267961665)
        ·
          refine ⟨1252028492818495700971249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1669371323757994267961665 1252028492818495700971249)
          ·
            refine ⟨939021369613871775728437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1252028492818495700971249 939021369613871775728437)
            ·
              refine ⟨88033253401300478974541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 939021369613871775728437 88033253401300478974541)
              ·
                refine ⟨33012470025487679615453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88033253401300478974541 33012470025487679615453)
                ·
                  refine ⟨12379676259557879855795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33012470025487679615453 12379676259557879855795)
                  ·
                    rfl

theorem cell20_27123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 3].length) (baseStart_27123 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27123 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27123 prefixEnd_27123 := by exact prefixLift 27123
  have htrace : WordTrace (prefixWord ++ tailWord_27123) baseStart_27123 baseEnd_27123 := by
    simpa [prefixWord, tailWord_27123, baseEnd_27123] using wordTrace_append hprefix tailTrace_27123
  have hstable : (prefixWord ++ tailWord_27123).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27123).length < 2 ^ (prefixWord ++ tailWord_27123).sum := by decide
  have hdescent : baseEnd_27123 < baseStart_27123 := by decide
  rcases family_descends (prefixWord ++ tailWord_27123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27164 : List Nat := [2, 2, 3, 1, 2, 3, 1, 4, 2]
def baseStart_27164 : Nat := 118140960795 + 27164 * 2 ^ 59
def prefixEnd_27164 : Nat := 4983230072969 + 3 ^ 40 * 27164 * 2
def baseEnd_27164 : Nat := 12398389776743959488961

theorem tailTrace_27164 : CollatzResearch.WordTrace tailWord_27164 prefixEnd_27164 12398389776743959488961 := by
  unfold tailWord_27164
  simp only [CollatzResearch.WordTrace]
  refine ⟨495376236798471043480273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 660501649064628057973697 495376236798471043480273)
  ·
    refine ⟨371532177598853282610205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 495376236798471043480273 371532177598853282610205)
    ·
      refine ⟨139324566599569980978827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371532177598853282610205 139324566599569980978827)
      ·
        refine ⟨208986849899354971468241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139324566599569980978827 208986849899354971468241)
        ·
          refine ⟨156740137424516228601181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208986849899354971468241 156740137424516228601181)
          ·
            refine ⟨58777551534193585725443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156740137424516228601181 58777551534193585725443)
            ·
              refine ⟨88166327301290378588165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58777551534193585725443 88166327301290378588165)
              ·
                refine ⟨16531186368991945985281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88166327301290378588165 16531186368991945985281)
                ·
                  refine ⟨12398389776743959488961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16531186368991945985281 12398389776743959488961)
                  ·
                    rfl

theorem cell20_27164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 2].length) (baseStart_27164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27164 prefixEnd_27164 := by exact prefixLift 27164
  have htrace : WordTrace (prefixWord ++ tailWord_27164) baseStart_27164 baseEnd_27164 := by
    simpa [prefixWord, tailWord_27164, baseEnd_27164] using wordTrace_append hprefix tailTrace_27164
  have hstable : (prefixWord ++ tailWord_27164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27164).length < 2 ^ (prefixWord ++ tailWord_27164).sum := by decide
  have hdescent : baseEnd_27164 < baseStart_27164 := by decide
  rcases family_descends (prefixWord ++ tailWord_27164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27178 : List Nat := [3, 1, 4, 1, 1, 2, 2, 3, 3]
def baseStart_27178 : Nat := 118140960795 + 27178 * 2 ^ 59
def prefixEnd_27178 : Nat := 4983230072969 + 3 ^ 40 * 27178 * 2
def baseEnd_27178 : Nat := 12404779758222133022237

theorem tailTrace_27178 : CollatzResearch.WordTrace tailWord_27178 prefixEnd_27178 12404779758222133022237 := by
  unfold tailWord_27178
  simp only [CollatzResearch.WordTrace]
  refine ⟨247815773886555619492547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 660842063697481651980125 247815773886555619492547)
  ·
    refine ⟨371723660829833429238821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247815773886555619492547 371723660829833429238821)
    ·
      refine ⟨69698186405593767982279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 371723660829833429238821 69698186405593767982279)
      ·
        refine ⟨104547279608390651973419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69698186405593767982279 104547279608390651973419)
        ·
          refine ⟨156820919412585977960129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104547279608390651973419 156820919412585977960129)
          ·
            refine ⟨117615689559439483470097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156820919412585977960129 117615689559439483470097)
            ·
              refine ⟨88211767169579612602573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117615689559439483470097 88211767169579612602573)
              ·
                refine ⟨33079412688592354725965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88211767169579612602573 33079412688592354725965)
                ·
                  refine ⟨12404779758222133022237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33079412688592354725965 12404779758222133022237)
                  ·
                    rfl

theorem cell20_27178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_27178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27178 prefixEnd_27178 := by exact prefixLift 27178
  have htrace : WordTrace (prefixWord ++ tailWord_27178) baseStart_27178 baseEnd_27178 := by
    simpa [prefixWord, tailWord_27178, baseEnd_27178] using wordTrace_append hprefix tailTrace_27178
  have hstable : (prefixWord ++ tailWord_27178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27178).length < 2 ^ (prefixWord ++ tailWord_27178).sum := by decide
  have hdescent : baseEnd_27178 < baseStart_27178 := by decide
  rcases family_descends (prefixWord ++ tailWord_27178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27192 : List Nat := [2, 1, 2, 1, 4, 1, 5, 4]
def baseStart_27192 : Nat := 118140960795 + 27192 * 2 ^ 59
def prefixEnd_27192 : Nat := 4983230072969 + 3 ^ 40 * 27192 * 2
def baseEnd_27192 : Nat := 4137056579900102185171

theorem tailTrace_27192 : CollatzResearch.WordTrace tailWord_27192 prefixEnd_27192 4137056579900102185171 := by
  unfold tailWord_27192
  simp only [CollatzResearch.WordTrace]
  refine ⟨495886858747751434489915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 661182478330335245986553 495886858747751434489915)
  ·
    refine ⟨743830288121627151734873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 495886858747751434489915 743830288121627151734873)
    ·
      refine ⟨557872716091220363801155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 743830288121627151734873 557872716091220363801155)
      ·
        refine ⟨836809074136830545701733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557872716091220363801155 836809074136830545701733)
        ·
          refine ⟨156901701400655727319075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 836809074136830545701733 156901701400655727319075)
          ·
            refine ⟨235352552100983590978613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156901701400655727319075 235352552100983590978613)
            ·
              refine ⟨22064301759467211654245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 235352552100983590978613 22064301759467211654245)
              ·
                refine ⟨4137056579900102185171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22064301759467211654245 4137056579900102185171)
                ·
                  rfl

theorem cell20_27192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 4].length) (baseStart_27192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27192 prefixEnd_27192 := by exact prefixLift 27192
  have htrace : WordTrace (prefixWord ++ tailWord_27192) baseStart_27192 baseEnd_27192 := by
    simpa [prefixWord, tailWord_27192, baseEnd_27192] using wordTrace_append hprefix tailTrace_27192
  have hstable : (prefixWord ++ tailWord_27192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27192).length < 2 ^ (prefixWord ++ tailWord_27192).sum := by decide
  have hdescent : baseEnd_27192 < baseStart_27192 := by decide
  rcases family_descends (prefixWord ++ tailWord_27192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27198 : List Nat := [4, 2, 1, 4, 1, 1, 2, 3, 2]
def baseStart_27198 : Nat := 118140960795 + 27198 * 2 ^ 59
def prefixEnd_27198 : Nat := 4983230072969 + 3 ^ 40 * 27198 * 2
def baseEnd_27198 : Nat := 12413908303190952355489

theorem tailTrace_27198 : CollatzResearch.WordTrace tailWord_27198 prefixEnd_27198 12413908303190952355489 := by
  unfold tailWord_27198
  simp only [CollatzResearch.WordTrace]
  refine ⟨123999069434220736712281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 661328370315843929132165 123999069434220736712281)
  ·
    refine ⟨92999302075665552534211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123999069434220736712281 92999302075665552534211)
    ·
      refine ⟨139498953113498328801317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92999302075665552534211 139498953113498328801317)
      ·
        refine ⟨26156053708780936650247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139498953113498328801317 26156053708780936650247)
        ·
          refine ⟨39234080563171404975371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26156053708780936650247 39234080563171404975371)
          ·
            refine ⟨58851120844757107463057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39234080563171404975371 58851120844757107463057)
            ·
              refine ⟨44138340633567830597293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58851120844757107463057 44138340633567830597293)
              ·
                refine ⟨16551877737587936473985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44138340633567830597293 16551877737587936473985)
                ·
                  refine ⟨12413908303190952355489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16551877737587936473985 12413908303190952355489)
                  ·
                    rfl

theorem cell20_27198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_27198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27198 prefixEnd_27198 := by exact prefixLift 27198
  have htrace : WordTrace (prefixWord ++ tailWord_27198) baseStart_27198 baseEnd_27198 := by
    simpa [prefixWord, tailWord_27198, baseEnd_27198] using wordTrace_append hprefix tailTrace_27198
  have hstable : (prefixWord ++ tailWord_27198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27198).length < 2 ^ (prefixWord ++ tailWord_27198).sum := by decide
  have hdescent : baseEnd_27198 < baseStart_27198 := by decide
  rcases family_descends (prefixWord ++ tailWord_27198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27223 : List Nat := [1, 1, 3, 2, 2, 2, 1, 6, 2]
def baseStart_27223 : Nat := 118140960795 + 27223 * 2 ^ 59
def prefixEnd_27223 : Nat := 4983230072969 + 3 ^ 40 * 27223 * 2
def baseEnd_27223 : Nat := 12425318984401976522053

theorem tailTrace_27223 : CollatzResearch.WordTrace tailWord_27223 prefixEnd_27223 12425318984401976522053 := by
  unfold tailWord_27223
  simp only [CollatzResearch.WordTrace]
  refine ⟨992904380383195163358323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 661936253588796775572215 992904380383195163358323)
  ·
    refine ⟨1489356570574792745037485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 992904380383195163358323 1489356570574792745037485)
    ·
      refine ⟨558508713965547279389057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1489356570574792745037485 558508713965547279389057)
      ·
        refine ⟨418881535474160459541793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 558508713965547279389057 418881535474160459541793)
        ·
          refine ⟨314161151605620344656345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418881535474160459541793 314161151605620344656345)
          ·
            refine ⟨235620863704215258492259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314161151605620344656345 235620863704215258492259)
            ·
              refine ⟨353431295556322887738389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235620863704215258492259 353431295556322887738389)
              ·
                refine ⟨16567091979202635362737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 353431295556322887738389 16567091979202635362737)
                ·
                  refine ⟨12425318984401976522053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16567091979202635362737 12425318984401976522053)
                  ·
                    rfl

theorem cell20_27223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 2].length) (baseStart_27223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27223 prefixEnd_27223 := by exact prefixLift 27223
  have htrace : WordTrace (prefixWord ++ tailWord_27223) baseStart_27223 baseEnd_27223 := by
    simpa [prefixWord, tailWord_27223, baseEnd_27223] using wordTrace_append hprefix tailTrace_27223
  have hstable : (prefixWord ++ tailWord_27223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27223).length < 2 ^ (prefixWord ++ tailWord_27223).sum := by decide
  have hdescent : baseEnd_27223 < baseStart_27223 := by decide
  rcases family_descends (prefixWord ++ tailWord_27223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27244 : List Nat := [2, 2, 1, 1, 3, 1, 4, 2, 4]
def baseStart_27244 : Nat := 118140960795 + 27244 * 2 ^ 59
def prefixEnd_27244 : Nat := 4983230072969 + 3 ^ 40 * 27244 * 2
def baseEnd_27244 : Nat := 12434903956619236821967

theorem tailTrace_27244 : CollatzResearch.WordTrace tailWord_27244 prefixEnd_27244 12434903956619236821967 := by
  unfold tailWord_27244
  simp only [CollatzResearch.WordTrace]
  refine ⟨496835156653557874936393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 662446875538077166581857 496835156653557874936393)
  ·
    refine ⟨372626367490168406202295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 496835156653557874936393 372626367490168406202295)
    ·
      refine ⟨558939551235252609303443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372626367490168406202295 558939551235252609303443)
      ·
        refine ⟨838409326852878913955165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558939551235252609303443 838409326852878913955165)
        ·
          refine ⟨314403497569829592733187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 838409326852878913955165 314403497569829592733187)
          ·
            refine ⟨471605246354744389099781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314403497569829592733187 471605246354744389099781)
            ·
              refine ⟨88425983691514572956209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 471605246354744389099781 88425983691514572956209)
              ·
                refine ⟨66319487768635929717157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88425983691514572956209 66319487768635929717157)
                ·
                  refine ⟨12434903956619236821967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66319487768635929717157 12434903956619236821967)
                  ·
                    rfl

theorem cell20_27244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_27244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27244 prefixEnd_27244 := by exact prefixLift 27244
  have htrace : WordTrace (prefixWord ++ tailWord_27244) baseStart_27244 baseEnd_27244 := by
    simpa [prefixWord, tailWord_27244, baseEnd_27244] using wordTrace_append hprefix tailTrace_27244
  have hstable : (prefixWord ++ tailWord_27244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27244).length < 2 ^ (prefixWord ++ tailWord_27244).sum := by decide
  have hdescent : baseEnd_27244 < baseStart_27244 := by decide
  rcases family_descends (prefixWord ++ tailWord_27244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27268 : List Nat := [2, 3, 2, 1, 3, 3, 6]
def baseStart_27268 : Nat := 118140960795 + 27268 * 2 ^ 59
def prefixEnd_27268 : Nat := 4983230072969 + 3 ^ 40 * 27268 * 2
def baseEnd_27268 : Nat := 1382873134509091113541

theorem tailTrace_27268 : CollatzResearch.WordTrace tailWord_27268 prefixEnd_27268 1382873134509091113541 := by
  unfold tailWord_27268
  simp only [CollatzResearch.WordTrace]
  refine ⟨497272832610083924373229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 663030443480111899164305 497272832610083924373229)
  ·
    refine ⟨186477312228781471639961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 497272832610083924373229 186477312228781471639961)
    ·
      refine ⟨139857984171586103729971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186477312228781471639961 139857984171586103729971)
      ·
        refine ⟨209786976257379155594957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139857984171586103729971 209786976257379155594957)
        ·
          refine ⟨78670116096517183348109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209786976257379155594957 78670116096517183348109)
          ·
            refine ⟨29501293536193943755541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78670116096517183348109 29501293536193943755541)
            ·
              refine ⟨1382873134509091113541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29501293536193943755541 1382873134509091113541)
              ·
                rfl

theorem cell20_27268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 6].length) (baseStart_27268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27268 prefixEnd_27268 := by exact prefixLift 27268
  have htrace : WordTrace (prefixWord ++ tailWord_27268) baseStart_27268 baseEnd_27268 := by
    simpa [prefixWord, tailWord_27268, baseEnd_27268] using wordTrace_append hprefix tailTrace_27268
  have hstable : (prefixWord ++ tailWord_27268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27268).length < 2 ^ (prefixWord ++ tailWord_27268).sum := by decide
  have hdescent : baseEnd_27268 < baseStart_27268 := by decide
  rcases family_descends (prefixWord ++ tailWord_27268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27289 : List Nat := [1, 2, 1, 2, 1, 2, 6, 5]
def baseStart_27289 : Nat := 118140960795 + 27289 * 2 ^ 59
def prefixEnd_27289 : Nat := 4983230072969 + 3 ^ 40 * 27289 * 2
def baseEnd_27289 : Nat := 4151814394266360107261

theorem tailTrace_27289 : CollatzResearch.WordTrace tailWord_27289 prefixEnd_27289 4151814394266360107261 := by
  unfold tailWord_27289
  simp only [CollatzResearch.WordTrace]
  refine ⟨995311598144088435260921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 663541065429392290173947 995311598144088435260921)
  ·
    refine ⟨746483698608066326445691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 995311598144088435260921 746483698608066326445691)
    ·
      refine ⟨1119725547912099489668537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 746483698608066326445691 1119725547912099489668537)
      ·
        refine ⟨839794160934074617251403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1119725547912099489668537 839794160934074617251403)
        ·
          refine ⟨1259691241401111925877105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 839794160934074617251403 1259691241401111925877105)
          ·
            refine ⟨944768431050833944407829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1259691241401111925877105 944768431050833944407829)
            ·
              refine ⟨44286020205507841144117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 944768431050833944407829 44286020205507841144117)
              ·
                refine ⟨4151814394266360107261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44286020205507841144117 4151814394266360107261)
                ·
                  rfl

theorem cell20_27289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 5].length) (baseStart_27289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27289 prefixEnd_27289 := by exact prefixLift 27289
  have htrace : WordTrace (prefixWord ++ tailWord_27289) baseStart_27289 baseEnd_27289 := by
    simpa [prefixWord, tailWord_27289, baseEnd_27289] using wordTrace_append hprefix tailTrace_27289
  have hstable : (prefixWord ++ tailWord_27289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27289).length < 2 ^ (prefixWord ++ tailWord_27289).sum := by decide
  have hdescent : baseEnd_27289 < baseStart_27289 := by decide
  rcases family_descends (prefixWord ++ tailWord_27289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27292 : List Nat := [2, 2, 3, 2, 2, 2, 1, 3, 3]
def baseStart_27292 : Nat := 118140960795 + 27292 * 2 ^ 59
def prefixEnd_27292 : Nat := 4983230072969 + 3 ^ 40 * 27292 * 2
def baseEnd_27292 : Nat := 12456812464544403221771

theorem tailTrace_27292 : CollatzResearch.WordTrace tailWord_27292 prefixEnd_27292 12456812464544403221771 := by
  unfold tailWord_27292
  simp only [CollatzResearch.WordTrace]
  refine ⟨497710508566609973810065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 663614011422146631746753 497710508566609973810065)
  ·
    refine ⟨373282881424957480357549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 497710508566609973810065 373282881424957480357549)
    ·
      refine ⟨139981080534359055134081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373282881424957480357549 139981080534359055134081)
      ·
        refine ⟨104985810400769291350561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139981080534359055134081 104985810400769291350561)
        ·
          refine ⟨78739357800576968512921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104985810400769291350561 78739357800576968512921)
          ·
            refine ⟨59054518350432726384691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78739357800576968512921 59054518350432726384691)
            ·
              refine ⟨88581777525649089577037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59054518350432726384691 88581777525649089577037)
              ·
                refine ⟨33218166572118408591389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88581777525649089577037 33218166572118408591389)
                ·
                  refine ⟨12456812464544403221771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33218166572118408591389 12456812464544403221771)
                  ·
                    rfl

theorem cell20_27292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_27292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27292 prefixEnd_27292 := by exact prefixLift 27292
  have htrace : WordTrace (prefixWord ++ tailWord_27292) baseStart_27292 baseEnd_27292 := by
    simpa [prefixWord, tailWord_27292, baseEnd_27292] using wordTrace_append hprefix tailTrace_27292
  have hstable : (prefixWord ++ tailWord_27292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27292).length < 2 ^ (prefixWord ++ tailWord_27292).sum := by decide
  have hdescent : baseEnd_27292 < baseStart_27292 := by decide
  rcases family_descends (prefixWord ++ tailWord_27292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27329 : List Nat := [1, 2, 6, 2, 1, 2, 2, 2, 2]
def baseStart_27329 : Nat := 118140960795 + 27329 * 2 ^ 59
def prefixEnd_27329 : Nat := 4983230072969 + 3 ^ 40 * 27329 * 2
def baseEnd_27329 : Nat := 12473700272736718988287

theorem tailTrace_27329 : CollatzResearch.WordTrace tailWord_27329 prefixEnd_27329 12473700272736718988287 := by
  unfold tailWord_27329
  simp only [CollatzResearch.WordTrace]
  refine ⟨996770517999175266717041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 664513678666116844478027 996770517999175266717041)
  ·
    refine ⟨747577888499381450037781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 996770517999175266717041 747577888499381450037781)
    ·
      refine ⟨35042713523408505470521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 747577888499381450037781 35042713523408505470521)
      ·
        refine ⟨26282035142556379102891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35042713523408505470521 26282035142556379102891)
        ·
          refine ⟨39423052713834568654337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26282035142556379102891 39423052713834568654337)
          ·
            refine ⟨29567289535375926490753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39423052713834568654337 29567289535375926490753)
            ·
              refine ⟨22175467151531944868065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29567289535375926490753 22175467151531944868065)
              ·
                refine ⟨16631600363648958651049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22175467151531944868065 16631600363648958651049)
                ·
                  refine ⟨12473700272736718988287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16631600363648958651049 12473700272736718988287)
                  ·
                    rfl

theorem cell20_27329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 2].length) (baseStart_27329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27329 prefixEnd_27329 := by exact prefixLift 27329
  have htrace : WordTrace (prefixWord ++ tailWord_27329) baseStart_27329 baseEnd_27329 := by
    simpa [prefixWord, tailWord_27329, baseEnd_27329] using wordTrace_append hprefix tailTrace_27329
  have hstable : (prefixWord ++ tailWord_27329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27329).length < 2 ^ (prefixWord ++ tailWord_27329).sum := by decide
  have hdescent : baseEnd_27329 < baseStart_27329 := by decide
  rcases family_descends (prefixWord ++ tailWord_27329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27351 : List Nat := [1, 1, 3, 2, 1, 4, 2, 3, 3]
def baseStart_27351 : Nat := 118140960795 + 27351 * 2 ^ 59
def prefixEnd_27351 : Nat := 4983230072969 + 3 ^ 40 * 27351 * 2
def baseEnd_27351 : Nat := 12483741672202420254863

theorem tailTrace_27351 : CollatzResearch.WordTrace tailWord_27351 prefixEnd_27351 12483741672202420254863 := by
  unfold tailWord_27351
  simp only [CollatzResearch.WordTrace]
  refine ⟨997572923919473024017907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 665048615946315349345271 997572923919473024017907)
  ·
    refine ⟨1496359385879209536026861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 997572923919473024017907 1496359385879209536026861)
    ·
      refine ⟨561134769704703576010073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1496359385879209536026861 561134769704703576010073)
      ·
        refine ⟨420851077278527682007555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 561134769704703576010073 420851077278527682007555)
        ·
          refine ⟨631276615917791523011333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420851077278527682007555 631276615917791523011333)
          ·
            refine ⟨118364365484585910564625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 631276615917791523011333 118364365484585910564625)
            ·
              refine ⟨88773274113439432923469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118364365484585910564625 88773274113439432923469)
              ·
                refine ⟨33289977792539787346301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88773274113439432923469 33289977792539787346301)
                ·
                  refine ⟨12483741672202420254863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33289977792539787346301 12483741672202420254863)
                  ·
                    rfl

theorem cell20_27351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 3].length) (baseStart_27351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27351 prefixEnd_27351 := by exact prefixLift 27351
  have htrace : WordTrace (prefixWord ++ tailWord_27351) baseStart_27351 baseEnd_27351 := by
    simpa [prefixWord, tailWord_27351, baseEnd_27351] using wordTrace_append hprefix tailTrace_27351
  have hstable : (prefixWord ++ tailWord_27351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27351).length < 2 ^ (prefixWord ++ tailWord_27351).sum := by decide
  have hdescent : baseEnd_27351 < baseStart_27351 := by decide
  rcases family_descends (prefixWord ++ tailWord_27351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27372 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 5]
def baseStart_27372 : Nat := 118140960795 + 27372 * 2 ^ 59
def prefixEnd_27372 : Nat := 4983230072969 + 3 ^ 40 * 27372 * 2
def baseEnd_27372 : Nat := 12493326644419680554777

theorem tailTrace_27372 : CollatzResearch.WordTrace tailWord_27372 prefixEnd_27372 12493326644419680554777 := by
  unfold tailWord_27372
  simp only [CollatzResearch.WordTrace]
  refine ⟨499169428421696805266185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 665559237895595740354913 499169428421696805266185)
  ·
    refine ⟨374377071316272603949639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 499169428421696805266185 374377071316272603949639)
    ·
      refine ⟨561565606974408905924459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374377071316272603949639 561565606974408905924459)
      ·
        refine ⟨842348410461613358886689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561565606974408905924459 842348410461613358886689)
        ·
          refine ⟨631761307846210019165017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 842348410461613358886689 631761307846210019165017)
          ·
            refine ⟨473820980884657514373763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 631761307846210019165017 473820980884657514373763)
            ·
              refine ⟨710731471326986271560645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473820980884657514373763 710731471326986271560645)
              ·
                refine ⟨133262150873809925917621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 710731471326986271560645 133262150873809925917621)
                ·
                  refine ⟨12493326644419680554777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133262150873809925917621 12493326644419680554777)
                  ·
                    rfl

theorem cell20_27372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_27372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27372 prefixEnd_27372 := by exact prefixLift 27372
  have htrace : WordTrace (prefixWord ++ tailWord_27372) baseStart_27372 baseEnd_27372 := by
    simpa [prefixWord, tailWord_27372, baseEnd_27372] using wordTrace_append hprefix tailTrace_27372
  have hstable : (prefixWord ++ tailWord_27372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27372).length < 2 ^ (prefixWord ++ tailWord_27372).sum := by decide
  have hdescent : baseEnd_27372 < baseStart_27372 := by decide
  rcases family_descends (prefixWord ++ tailWord_27372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27375 : List Nat := [1, 1, 2, 1, 5, 2, 1, 5, 2]
def baseStart_27375 : Nat := 118140960795 + 27375 * 2 ^ 59
def prefixEnd_27375 : Nat := 4983230072969 + 3 ^ 40 * 27375 * 2
def baseEnd_27375 : Nat := 12494695926165003454765

theorem tailTrace_27375 : CollatzResearch.WordTrace tailWord_27375 prefixEnd_27375 12494695926165003454765 := by
  unfold tailWord_27375
  simp only [CollatzResearch.WordTrace]
  refine ⟨998448275832525122891579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 665632183888350081927719 998448275832525122891579)
  ·
    refine ⟨1497672413748787684337369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 998448275832525122891579 1497672413748787684337369)
    ·
      refine ⟨1123254310311590763253027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1497672413748787684337369 1123254310311590763253027)
      ·
        refine ⟨1684881465467386144879541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1123254310311590763253027 1684881465467386144879541)
        ·
          refine ⟨157957637387567451082457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1684881465467386144879541 157957637387567451082457)
          ·
            refine ⟨118468228040675588311843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157957637387567451082457 118468228040675588311843)
            ·
              refine ⟨177702342061013382467765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118468228040675588311843 177702342061013382467765)
              ·
                refine ⟨16659594568220004606353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 177702342061013382467765 16659594568220004606353)
                ·
                  refine ⟨12494695926165003454765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16659594568220004606353 12494695926165003454765)
                  ·
                    rfl

theorem cell20_27375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 2].length) (baseStart_27375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27375 prefixEnd_27375 := by exact prefixLift 27375
  have htrace : WordTrace (prefixWord ++ tailWord_27375) baseStart_27375 baseEnd_27375 := by
    simpa [prefixWord, tailWord_27375, baseEnd_27375] using wordTrace_append hprefix tailTrace_27375
  have hstable : (prefixWord ++ tailWord_27375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27375).length < 2 ^ (prefixWord ++ tailWord_27375).sum := by decide
  have hdescent : baseEnd_27375 < baseStart_27375 := by decide
  rcases family_descends (prefixWord ++ tailWord_27375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27379 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 8]
def baseStart_27379 : Nat := 118140960795 + 27379 * 2 ^ 59
def prefixEnd_27379 : Nat := 4983230072969 + 3 ^ 40 * 27379 * 2
def baseEnd_27379 : Nat := 12496521635158767321415

theorem tailTrace_27379 : CollatzResearch.WordTrace tailWord_27379 prefixEnd_27379 12496521635158767321415 := by
  unfold tailWord_27379
  simp only [CollatzResearch.WordTrace]
  refine ⟨998594167818033806037191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 665729445212022537358127 998594167818033806037191)
  ·
    refine ⟨1497891251727050709055787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 998594167818033806037191 1497891251727050709055787)
    ·
      refine ⟨2246836877590576063583681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1497891251727050709055787 2246836877590576063583681)
      ·
        refine ⟨1685127658192932047687761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2246836877590576063583681 1685127658192932047687761)
        ·
          refine ⟨1263845743644699035765821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1685127658192932047687761 1263845743644699035765821)
          ·
            refine ⟨473942153866762138412183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1263845743644699035765821 473942153866762138412183)
            ·
              refine ⟨710913230800143207618275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473942153866762138412183 710913230800143207618275)
              ·
                refine ⟨1066369846200214811427413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 710913230800143207618275 1066369846200214811427413)
                ·
                  refine ⟨12496521635158767321415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1066369846200214811427413 12496521635158767321415)
                  ·
                    rfl

theorem cell20_27379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_27379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27379 prefixEnd_27379 := by exact prefixLift 27379
  have htrace : WordTrace (prefixWord ++ tailWord_27379) baseStart_27379 baseEnd_27379 := by
    simpa [prefixWord, tailWord_27379, baseEnd_27379] using wordTrace_append hprefix tailTrace_27379
  have hstable : (prefixWord ++ tailWord_27379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27379).length < 2 ^ (prefixWord ++ tailWord_27379).sum := by decide
  have hdescent : baseEnd_27379 < baseStart_27379 := by decide
  rcases family_descends (prefixWord ++ tailWord_27379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27381 : List Nat := [1, 3, 6, 1, 1, 2, 1, 2, 3]
def baseStart_27381 : Nat := 118140960795 + 27381 * 2 ^ 59
def prefixEnd_27381 : Nat := 4983230072969 + 3 ^ 40 * 27381 * 2
def baseEnd_27381 : Nat := 12497434489655649254741

theorem tailTrace_27381 : CollatzResearch.WordTrace tailWord_27381 prefixEnd_27381 12497434489655649254741 := by
  unfold tailWord_27381
  simp only [CollatzResearch.WordTrace]
  refine ⟨998667113810788147609997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 665778075873858765073331 998667113810788147609997)
  ·
    refine ⟨374500167679045555353749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 998667113810788147609997 374500167679045555353749)
    ·
      refine ⟨17554695359955260407207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 374500167679045555353749 17554695359955260407207)
      ·
        refine ⟨26332043039932890610811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17554695359955260407207 26332043039932890610811)
        ·
          refine ⟨39498064559899335916217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26332043039932890610811 39498064559899335916217)
          ·
            refine ⟨29623548419924501937163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39498064559899335916217 29623548419924501937163)
            ·
              refine ⟨44435322629886752905745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29623548419924501937163 44435322629886752905745)
              ·
                refine ⟨33326491972415064679309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44435322629886752905745 33326491972415064679309)
                ·
                  refine ⟨12497434489655649254741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33326491972415064679309 12497434489655649254741)
                  ·
                    rfl

theorem cell20_27381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 3].length) (baseStart_27381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27381 prefixEnd_27381 := by exact prefixLift 27381
  have htrace : WordTrace (prefixWord ++ tailWord_27381) baseStart_27381 baseEnd_27381 := by
    simpa [prefixWord, tailWord_27381, baseEnd_27381] using wordTrace_append hprefix tailTrace_27381
  have hstable : (prefixWord ++ tailWord_27381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27381).length < 2 ^ (prefixWord ++ tailWord_27381).sum := by decide
  have hdescent : baseEnd_27381 < baseStart_27381 := by decide
  rcases family_descends (prefixWord ++ tailWord_27381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27417 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 6]
def baseStart_27417 : Nat := 118140960795 + 27417 * 2 ^ 59
def prefixEnd_27417 : Nat := 4983230072969 + 3 ^ 40 * 27417 * 2
def baseEnd_27417 : Nat := 12513865870599524054593

theorem tailTrace_27417 : CollatzResearch.WordTrace tailWord_27417 prefixEnd_27417 12513865870599524054593 := by
  unfold tailWord_27417
  simp only [CollatzResearch.WordTrace]
  refine ⟨999980141680366295920505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 666653427786910863947003 999980141680366295920505)
  ·
    refine ⟨749985106260274721940379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 999980141680366295920505 749985106260274721940379)
    ·
      refine ⟨1124977659390412082910569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 749985106260274721940379 1124977659390412082910569)
      ·
        refine ⟨843733244542809062182927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1124977659390412082910569 843733244542809062182927)
        ·
          refine ⟨1265599866814213593274391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843733244542809062182927 1265599866814213593274391)
          ·
            refine ⟨1898399800221320389911587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1265599866814213593274391 1898399800221320389911587)
            ·
              refine ⟨2847599700331980584867381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1898399800221320389911587 2847599700331980584867381)
              ·
                refine ⟨266962471906123179831317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2847599700331980584867381 266962471906123179831317)
                ·
                  refine ⟨12513865870599524054593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 266962471906123179831317 12513865870599524054593)
                  ·
                    rfl

theorem cell20_27417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_27417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27417 prefixEnd_27417 := by exact prefixLift 27417
  have htrace : WordTrace (prefixWord ++ tailWord_27417) baseStart_27417 baseEnd_27417 := by
    simpa [prefixWord, tailWord_27417, baseEnd_27417] using wordTrace_append hprefix tailTrace_27417
  have hstable : (prefixWord ++ tailWord_27417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27417).length < 2 ^ (prefixWord ++ tailWord_27417).sum := by decide
  have hdescent : baseEnd_27417 < baseStart_27417 := by decide
  rcases family_descends (prefixWord ++ tailWord_27417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27420 : List Nat := [2, 2, 3, 1, 1, 3, 4, 4]
def baseStart_27420 : Nat := 118140960795 + 27420 * 2 ^ 59
def prefixEnd_27420 : Nat := 4983230072969 + 3 ^ 40 * 27420 * 2
def baseEnd_27420 : Nat := 4171745050781615651527

theorem tailTrace_27420 : CollatzResearch.WordTrace tailWord_27420 prefixEnd_27420 4171745050781615651527 := by
  unfold tailWord_27420
  simp only [CollatzResearch.WordTrace]
  refine ⟨500044780334748904139857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 666726373779665205519809 500044780334748904139857)
  ·
    refine ⟨375033585251061678104893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 500044780334748904139857 375033585251061678104893)
    ·
      refine ⟨140637594469148129289335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375033585251061678104893 140637594469148129289335)
      ·
        refine ⟨210956391703722193934003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140637594469148129289335 210956391703722193934003)
        ·
          refine ⟨316434587555583290901005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210956391703722193934003 316434587555583290901005)
          ·
            refine ⟨118662970333343734087877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316434587555583290901005 118662970333343734087877)
            ·
              refine ⟨22249306937501950141477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118662970333343734087877 22249306937501950141477)
              ·
                refine ⟨4171745050781615651527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22249306937501950141477 4171745050781615651527)
                ·
                  rfl

theorem cell20_27420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 4].length) (baseStart_27420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27420 prefixEnd_27420 := by exact prefixLift 27420
  have htrace : WordTrace (prefixWord ++ tailWord_27420) baseStart_27420 baseEnd_27420 := by
    simpa [prefixWord, tailWord_27420, baseEnd_27420] using wordTrace_append hprefix tailTrace_27420
  have hstable : (prefixWord ++ tailWord_27420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27420).length < 2 ^ (prefixWord ++ tailWord_27420).sum := by decide
  have hdescent : baseEnd_27420 < baseStart_27420 := by decide
  rcases family_descends (prefixWord ++ tailWord_27420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27448 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 5]
def baseStart_27448 : Nat := 118140960795 + 27448 * 2 ^ 59
def prefixEnd_27448 : Nat := 4983230072969 + 3 ^ 40 * 27448 * 2
def baseEnd_27448 : Nat := 12528015115301194021133

theorem tailTrace_27448 : CollatzResearch.WordTrace tailWord_27448 prefixEnd_27448 12528015115301194021133 := by
  unfold tailWord_27448
  simp only [CollatzResearch.WordTrace]
  refine ⟨500555402284029295149499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 667407203045372393532665 500555402284029295149499)
  ·
    refine ⟨750833103426043942724249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 500555402284029295149499 750833103426043942724249)
    ·
      refine ⟨563124827569532957043187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 750833103426043942724249 563124827569532957043187)
      ·
        refine ⟨844687241354299435564781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563124827569532957043187 844687241354299435564781)
        ·
          refine ⟨316757715507862288336793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 844687241354299435564781 316757715507862288336793)
          ·
            refine ⟨237568286630896716252595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316757715507862288336793 237568286630896716252595)
            ·
              refine ⟨356352429946345074378893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237568286630896716252595 356352429946345074378893)
              ·
                refine ⟨133632161229879402892085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 356352429946345074378893 133632161229879402892085)
                ·
                  refine ⟨12528015115301194021133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133632161229879402892085 12528015115301194021133)
                  ·
                    rfl

theorem cell20_27448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_27448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27448 prefixEnd_27448 := by exact prefixLift 27448
  have htrace : WordTrace (prefixWord ++ tailWord_27448) baseStart_27448 baseEnd_27448 := by
    simpa [prefixWord, tailWord_27448, baseEnd_27448] using wordTrace_append hprefix tailTrace_27448
  have hstable : (prefixWord ++ tailWord_27448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27448).length < 2 ^ (prefixWord ++ tailWord_27448).sum := by decide
  have hdescent : baseEnd_27448 < baseStart_27448 := by decide
  rcases family_descends (prefixWord ++ tailWord_27448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27457 : List Nat := [1, 2, 5, 3, 2, 1, 2, 1, 3]
def baseStart_27457 : Nat := 118140960795 + 27457 * 2 ^ 59
def prefixEnd_27457 : Nat := 4983230072969 + 3 ^ 40 * 27457 * 2
def baseEnd_27457 : Nat := 12532122960537162721097

theorem tailTrace_27457 : CollatzResearch.WordTrace tailWord_27457 prefixEnd_27457 12532122960537162721097 := by
  unfold tailWord_27457
  simp only [CollatzResearch.WordTrace]
  refine ⟨1001439061535453127376625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 667626041023635418251083 1001439061535453127376625)
  ·
    refine ⟨751079296151589845532469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1001439061535453127376625 751079296151589845532469)
    ·
      refine ⟨70413684014211548018669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 751079296151589845532469 70413684014211548018669)
      ·
        refine ⟨26405131505329330507001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70413684014211548018669 26405131505329330507001)
        ·
          refine ⟨19803848628996997880251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26405131505329330507001 19803848628996997880251)
          ·
            refine ⟨29705772943495496820377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19803848628996997880251 29705772943495496820377)
            ·
              refine ⟨22279329707621622615283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29705772943495496820377 22279329707621622615283)
              ·
                refine ⟨33418994561432433922925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22279329707621622615283 33418994561432433922925)
                ·
                  refine ⟨12532122960537162721097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33418994561432433922925 12532122960537162721097)
                  ·
                    rfl

theorem cell20_27457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 3].length) (baseStart_27457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27457 prefixEnd_27457 := by exact prefixLift 27457
  have htrace : WordTrace (prefixWord ++ tailWord_27457) baseStart_27457 baseEnd_27457 := by
    simpa [prefixWord, tailWord_27457, baseEnd_27457] using wordTrace_append hprefix tailTrace_27457
  have hstable : (prefixWord ++ tailWord_27457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27457).length < 2 ^ (prefixWord ++ tailWord_27457).sum := by decide
  have hdescent : baseEnd_27457 < baseStart_27457 := by decide
  rcases family_descends (prefixWord ++ tailWord_27457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27465 : List Nat := [1, 2, 1, 1, 2, 6, 1, 3, 3]
def baseStart_27465 : Nat := 118140960795 + 27465 * 2 ^ 59
def prefixEnd_27465 : Nat := 4983230072969 + 3 ^ 40 * 27465 * 2
def baseEnd_27465 : Nat := 12535774378524690454397

theorem tailTrace_27465 : CollatzResearch.WordTrace tailWord_27465 prefixEnd_27465 12535774378524690454397 := by
  unfold tailWord_27465
  simp only [CollatzResearch.WordTrace]
  refine ⟨1001730845506470493667849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 667820563670980329111899 1001730845506470493667849)
  ·
    refine ⟨751298134129852870250887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1001730845506470493667849 751298134129852870250887)
    ·
      refine ⟨1126947201194779305376331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 751298134129852870250887 1126947201194779305376331)
      ·
        refine ⟨1690420801792168958064497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1126947201194779305376331 1690420801792168958064497)
        ·
          refine ⟨1267815601344126718548373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1690420801792168958064497 1267815601344126718548373)
          ·
            refine ⟨59428856313005939931955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1267815601344126718548373 59428856313005939931955)
            ·
              refine ⟨89143284469508909897933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59428856313005939931955 89143284469508909897933)
              ·
                refine ⟨33428731676065841211725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89143284469508909897933 33428731676065841211725)
                ·
                  refine ⟨12535774378524690454397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33428731676065841211725 12535774378524690454397)
                  ·
                    rfl

theorem cell20_27465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 3].length) (baseStart_27465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27465 prefixEnd_27465 := by exact prefixLift 27465
  have htrace : WordTrace (prefixWord ++ tailWord_27465) baseStart_27465 baseEnd_27465 := by
    simpa [prefixWord, tailWord_27465, baseEnd_27465] using wordTrace_append hprefix tailTrace_27465
  have hstable : (prefixWord ++ tailWord_27465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27465).length < 2 ^ (prefixWord ++ tailWord_27465).sum := by decide
  have hdescent : baseEnd_27465 < baseStart_27465 := by decide
  rcases family_descends (prefixWord ++ tailWord_27465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27479 : List Nat := [1, 1, 3, 2, 4, 1, 2, 6]
def baseStart_27479 : Nat := 118140960795 + 27479 * 2 ^ 59
def prefixEnd_27479 : Nat := 4983230072969 + 3 ^ 40 * 27479 * 2
def baseEnd_27479 : Nat := 4180721453334287995891

theorem tailTrace_27479 : CollatzResearch.WordTrace tailWord_27479 prefixEnd_27479 4180721453334287995891 := by
  unfold tailWord_27479
  simp only [CollatzResearch.WordTrace]
  refine ⟨1002241467455750884677491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 668160978303833923118327 1002241467455750884677491)
  ·
    refine ⟨1503362201183626327016237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1002241467455750884677491 1503362201183626327016237)
    ·
      refine ⟨563760825443859872631089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1503362201183626327016237 563760825443859872631089)
      ·
        refine ⟨422820619082894904473317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 563760825443859872631089 422820619082894904473317)
        ·
          refine ⟨79278866078042794588747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 422820619082894904473317 79278866078042794588747)
          ·
            refine ⟨118918299117064191883121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79278866078042794588747 118918299117064191883121)
            ·
              refine ⟨89188724337798143912341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118918299117064191883121 89188724337798143912341)
              ·
                refine ⟨4180721453334287995891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89188724337798143912341 4180721453334287995891)
                ·
                  rfl

theorem cell20_27479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 6].length) (baseStart_27479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27479 prefixEnd_27479 := by exact prefixLift 27479
  have htrace : WordTrace (prefixWord ++ tailWord_27479) baseStart_27479 baseEnd_27479 := by
    simpa [prefixWord, tailWord_27479, baseEnd_27479] using wordTrace_append hprefix tailTrace_27479
  have hstable : (prefixWord ++ tailWord_27479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27479).length < 2 ^ (prefixWord ++ tailWord_27479).sum := by decide
  have hdescent : baseEnd_27479 < baseStart_27479 := by decide
  rcases family_descends (prefixWord ++ tailWord_27479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27502 : List Nat := [4, 1, 2, 3, 2, 2, 2, 2, 2]
def baseStart_27502 : Nat := 118140960795 + 27502 * 2 ^ 59
def prefixEnd_27502 : Nat := 4983230072969 + 3 ^ 40 * 27502 * 2
def baseEnd_27502 : Nat := 12552662186717006220913

theorem tailTrace_27502 : CollatzResearch.WordTrace tailWord_27502 prefixEnd_27502 12552662186717006220913 := by
  unfold tailWord_27502
  simp only [CollatzResearch.WordTrace]
  refine ⟨125385043296553226595595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 668720230914950541843173 125385043296553226595595)
  ·
    refine ⟨188077564944829839893393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125385043296553226595595 188077564944829839893393)
    ·
      refine ⟨141058173708622379920045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188077564944829839893393 141058173708622379920045)
      ·
        refine ⟨52896815140733392470017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141058173708622379920045 52896815140733392470017)
        ·
          refine ⟨39672611355550044352513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52896815140733392470017 39672611355550044352513)
          ·
            refine ⟨29754458516662533264385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39672611355550044352513 29754458516662533264385)
            ·
              refine ⟨22315843887496899948289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29754458516662533264385 22315843887496899948289)
              ·
                refine ⟨16736882915622674961217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22315843887496899948289 16736882915622674961217)
                ·
                  refine ⟨12552662186717006220913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16736882915622674961217 12552662186717006220913)
                  ·
                    rfl

theorem cell20_27502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_27502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27502 prefixEnd_27502 := by exact prefixLift 27502
  have htrace : WordTrace (prefixWord ++ tailWord_27502) baseStart_27502 baseEnd_27502 := by
    simpa [prefixWord, tailWord_27502, baseEnd_27502] using wordTrace_append hprefix tailTrace_27502
  have hstable : (prefixWord ++ tailWord_27502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27502).length < 2 ^ (prefixWord ++ tailWord_27502).sum := by decide
  have hdescent : baseEnd_27502 < baseStart_27502 := by decide
  rcases family_descends (prefixWord ++ tailWord_27502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27506 : List Nat := [3, 2, 1, 2, 1, 1, 6, 2, 2]
def baseStart_27506 : Nat := 118140960795 + 27506 * 2 ^ 59
def prefixEnd_27506 : Nat := 4983230072969 + 3 ^ 40 * 27506 * 2
def baseEnd_27506 : Nat := 12554487895710770087563

theorem tailTrace_27506 : CollatzResearch.WordTrace tailWord_27506 prefixEnd_27506 12554487895710770087563 := by
  unfold tailWord_27506
  simp only [CollatzResearch.WordTrace]
  refine ⟨250806559589483623977593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 668817492238622997273581 250806559589483623977593)
  ·
    refine ⟨188104919692112717983195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250806559589483623977593 188104919692112717983195)
    ·
      refine ⟨282157379538169076974793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188104919692112717983195 282157379538169076974793)
      ·
        refine ⟨211618034653626807731095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282157379538169076974793 211618034653626807731095)
        ·
          refine ⟨317427051980440211596643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211618034653626807731095 317427051980440211596643)
          ·
            refine ⟨476140577970660317394965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317427051980440211596643 476140577970660317394965)
            ·
              refine ⟨22319089592374702377889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 476140577970660317394965 22319089592374702377889)
              ·
                refine ⟨16739317194281026783417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22319089592374702377889 16739317194281026783417)
                ·
                  refine ⟨12554487895710770087563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16739317194281026783417 12554487895710770087563)
                  ·
                    rfl

theorem cell20_27506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_27506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27506 prefixEnd_27506 := by exact prefixLift 27506
  have htrace : WordTrace (prefixWord ++ tailWord_27506) baseStart_27506 baseEnd_27506 := by
    simpa [prefixWord, tailWord_27506, baseEnd_27506] using wordTrace_append hprefix tailTrace_27506
  have hstable : (prefixWord ++ tailWord_27506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27506).length < 2 ^ (prefixWord ++ tailWord_27506).sum := by decide
  have hdescent : baseEnd_27506 < baseStart_27506 := by decide
  rcases family_descends (prefixWord ++ tailWord_27506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27517 : List Nat := [1, 4, 1, 1, 2, 1, 5, 5]
def baseStart_27517 : Nat := 118140960795 + 27517 * 2 ^ 59
def prefixEnd_27517 : Nat := 4983230072969 + 3 ^ 40 * 27517 * 2
def baseEnd_27517 : Nat := 4186502865147873573617

theorem tailTrace_27517 : CollatzResearch.WordTrace tailWord_27517 prefixEnd_27517 4186502865147873573617 := by
  unfold tailWord_27517
  simp only [CollatzResearch.WordTrace]
  refine ⟨1003627441318083374560805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 669084960878722249707203 1003627441318083374560805)
  ·
    refine ⟨188180145247140632730151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1003627441318083374560805 188180145247140632730151)
    ·
      refine ⟨282270217870710949095227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188180145247140632730151 282270217870710949095227)
      ·
        refine ⟨423405326806066423642841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282270217870710949095227 423405326806066423642841)
        ·
          refine ⟨317553995104549817732131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423405326806066423642841 317553995104549817732131)
          ·
            refine ⟨476330992656824726598197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317553995104549817732131 476330992656824726598197)
            ·
              refine ⟨44656030561577318118581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 476330992656824726598197 44656030561577318118581)
              ·
                refine ⟨4186502865147873573617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44656030561577318118581 4186502865147873573617)
                ·
                  rfl

theorem cell20_27517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 5].length) (baseStart_27517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27517 prefixEnd_27517 := by exact prefixLift 27517
  have htrace : WordTrace (prefixWord ++ tailWord_27517) baseStart_27517 baseEnd_27517 := by
    simpa [prefixWord, tailWord_27517, baseEnd_27517] using wordTrace_append hprefix tailTrace_27517
  have hstable : (prefixWord ++ tailWord_27517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27517).length < 2 ^ (prefixWord ++ tailWord_27517).sum := by decide
  have hdescent : baseEnd_27517 < baseStart_27517 := by decide
  rcases family_descends (prefixWord ++ tailWord_27517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27524 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 7]
def baseStart_27524 : Nat := 118140960795 + 27524 * 2 ^ 59
def prefixEnd_27524 : Nat := 4983230072969 + 3 ^ 40 * 27524 * 2
def baseEnd_27524 : Nat := 12562703586182707487489

theorem tailTrace_27524 : CollatzResearch.WordTrace tailWord_27524 prefixEnd_27524 12562703586182707487489 := by
  unfold tailWord_27524
  simp only [CollatzResearch.WordTrace]
  refine ⟨501941376146361785032813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 669255168195149046710417 501941376146361785032813)
  ·
    refine ⟨188228016054885669387305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 501941376146361785032813 188228016054885669387305)
    ·
      refine ⟨141171012041164252040479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188228016054885669387305 141171012041164252040479)
      ·
        refine ⟨211756518061746378060719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141171012041164252040479 211756518061746378060719)
        ·
          refine ⟨317634777092619567091079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211756518061746378060719 317634777092619567091079)
          ·
            refine ⟨476452165638929350636619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317634777092619567091079 476452165638929350636619)
            ·
              refine ⟨714678248458394025954929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476452165638929350636619 714678248458394025954929)
              ·
                refine ⟨536008686343795519466197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 714678248458394025954929 536008686343795519466197)
                ·
                  refine ⟨12562703586182707487489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 536008686343795519466197 12562703586182707487489)
                  ·
                    rfl

theorem cell20_27524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_27524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27524 prefixEnd_27524 := by exact prefixLift 27524
  have htrace : WordTrace (prefixWord ++ tailWord_27524) baseStart_27524 baseEnd_27524 := by
    simpa [prefixWord, tailWord_27524, baseEnd_27524] using wordTrace_append hprefix tailTrace_27524
  have hstable : (prefixWord ++ tailWord_27524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27524).length < 2 ^ (prefixWord ++ tailWord_27524).sum := by decide
  have hdescent : baseEnd_27524 < baseStart_27524 := by decide
  rcases family_descends (prefixWord ++ tailWord_27524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27531 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 6]
def baseStart_27531 : Nat := 118140960795 + 27531 * 2 ^ 59
def prefixEnd_27531 : Nat := 4983230072969 + 3 ^ 40 * 27531 * 2
def baseEnd_27531 : Nat := 12565898576921794254127

theorem tailTrace_27531 : CollatzResearch.WordTrace tailWord_27531 prefixEnd_27531 12565898576921794254127 := by
  unfold tailWord_27531
  simp only [CollatzResearch.WordTrace]
  refine ⟨1004138063267363765570447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 669425375511575843713631 1004138063267363765570447)
  ·
    refine ⟨1506207094901045648355671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1004138063267363765570447 1506207094901045648355671)
    ·
      refine ⟨2259310642351568472533507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1506207094901045648355671 2259310642351568472533507)
      ·
        refine ⟨3388965963527352708800261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2259310642351568472533507 3388965963527352708800261)
        ·
          refine ⟨635431118161378632900049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3388965963527352708800261 635431118161378632900049)
          ·
            refine ⟨476573338621033974675037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 635431118161378632900049 476573338621033974675037)
            ·
              refine ⟨178715001982887740503139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 476573338621033974675037 178715001982887740503139)
              ·
                refine ⟨268072502974331610754709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178715001982887740503139 268072502974331610754709)
                ·
                  refine ⟨12565898576921794254127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 268072502974331610754709 12565898576921794254127)
                  ·
                    rfl

theorem cell20_27531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_27531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27531 prefixEnd_27531 := by exact prefixLift 27531
  have htrace : WordTrace (prefixWord ++ tailWord_27531) baseStart_27531 baseEnd_27531 := by
    simpa [prefixWord, tailWord_27531, baseEnd_27531] using wordTrace_append hprefix tailTrace_27531
  have hstable : (prefixWord ++ tailWord_27531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27531).length < 2 ^ (prefixWord ++ tailWord_27531).sum := by decide
  have hdescent : baseEnd_27531 < baseStart_27531 := by decide
  rcases family_descends (prefixWord ++ tailWord_27531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27624 : List Nat := [2, 1, 4, 1, 1, 1, 5, 1, 4]
def baseStart_27624 : Nat := 118140960795 + 27624 * 2 ^ 59
def prefixEnd_27624 : Nat := 4983230072969 + 3 ^ 40 * 27624 * 2
def baseEnd_27624 : Nat := 12608346311026804153747

theorem tailTrace_27624 : CollatzResearch.WordTrace tailWord_27624 prefixEnd_27624 12608346311026804153747 := by
  unfold tailWord_27624
  simp only [CollatzResearch.WordTrace]
  refine ⟨503765025965220324352963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 671686701286960432470617 503765025965220324352963)
  ·
    refine ⟨755647538947830486529445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 503765025965220324352963 755647538947830486529445)
    ·
      refine ⟨141683913552718216224271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 755647538947830486529445 141683913552718216224271)
      ·
        refine ⟨212525870329077324336407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141683913552718216224271 212525870329077324336407)
        ·
          refine ⟨318788805493615986504611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212525870329077324336407 318788805493615986504611)
          ·
            refine ⟨478183208240423979756917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318788805493615986504611 478183208240423979756917)
            ·
              refine ⟨44829675772539748102211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 478183208240423979756917 44829675772539748102211)
              ·
                refine ⟨67244513658809622153317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44829675772539748102211 67244513658809622153317)
                ·
                  refine ⟨12608346311026804153747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67244513658809622153317 12608346311026804153747)
                  ·
                    rfl

theorem cell20_27624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_27624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27624 prefixEnd_27624 := by exact prefixLift 27624
  have htrace : WordTrace (prefixWord ++ tailWord_27624) baseStart_27624 baseEnd_27624 := by
    simpa [prefixWord, tailWord_27624, baseEnd_27624] using wordTrace_append hprefix tailTrace_27624
  have hstable : (prefixWord ++ tailWord_27624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27624).length < 2 ^ (prefixWord ++ tailWord_27624).sum := by decide
  have hdescent : baseEnd_27624 < baseStart_27624 := by decide
  rcases family_descends (prefixWord ++ tailWord_27624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27630 : List Nat := [4, 1, 2, 1, 5, 1, 2, 1, 3]
def baseStart_27630 : Nat := 118140960795 + 27630 * 2 ^ 59
def prefixEnd_27630 : Nat := 4983230072969 + 3 ^ 40 * 27630 * 2
def baseEnd_27630 : Nat := 12611084874517449953723

theorem tailTrace_27630 : CollatzResearch.WordTrace tailWord_27630 prefixEnd_27630 12611084874517449953723 := by
  unfold tailWord_27630
  simp only [CollatzResearch.WordTrace]
  refine ⟨125968611238587959178043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 671832593272469115616229 125968611238587959178043)
  ·
    refine ⟨188952916857881938767065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125968611238587959178043 188952916857881938767065)
    ·
      refine ⟨141714687643411454075299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188952916857881938767065 141714687643411454075299)
      ·
        refine ⟨212572031465117181112949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141714687643411454075299 212572031465117181112949)
        ·
          refine ⟨19928627949854735729339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212572031465117181112949 19928627949854735729339)
          ·
            refine ⟨29892941924782103594009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19928627949854735729339 29892941924782103594009)
            ·
              refine ⟨22419706443586577695507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29892941924782103594009 22419706443586577695507)
              ·
                refine ⟨33629559665379866543261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22419706443586577695507 33629559665379866543261)
                ·
                  refine ⟨12611084874517449953723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33629559665379866543261 12611084874517449953723)
                  ·
                    rfl

theorem cell20_27630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_27630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27630 prefixEnd_27630 := by exact prefixLift 27630
  have htrace : WordTrace (prefixWord ++ tailWord_27630) baseStart_27630 baseEnd_27630 := by
    simpa [prefixWord, tailWord_27630, baseEnd_27630] using wordTrace_append hprefix tailTrace_27630
  have hstable : (prefixWord ++ tailWord_27630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27630).length < 2 ^ (prefixWord ++ tailWord_27630).sum := by decide
  have hdescent : baseEnd_27630 < baseStart_27630 := by decide
  rcases family_descends (prefixWord ++ tailWord_27630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27631 : List Nat := [1, 1, 2, 1, 4, 4, 2, 5]
def baseStart_27631 : Nat := 118140960795 + 27631 * 2 ^ 59
def prefixEnd_27631 : Nat := 4983230072969 + 3 ^ 40 * 27631 * 2
def baseEnd_27631 : Nat := 4203847100588630306795

theorem tailTrace_27631 : CollatzResearch.WordTrace tailWord_27631 prefixEnd_27631 4203847100588630306795 := by
  unfold tailWord_27631
  simp only [CollatzResearch.WordTrace]
  refine ⟨1007785362905080844210747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 671856908603387229473831 1007785362905080844210747)
  ·
    refine ⟨1511678044357621266316121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1007785362905080844210747 1511678044357621266316121)
    ·
      refine ⟨1133758533268215949737091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1511678044357621266316121 1133758533268215949737091)
      ·
        refine ⟨1700637799902323924605637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1133758533268215949737091 1700637799902323924605637)
        ·
          refine ⟨318869587481685735863557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1700637799902323924605637 318869587481685735863557)
          ·
            refine ⟨59788047652816075474417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 318869587481685735863557 59788047652816075474417)
            ·
              refine ⟨44841035739612056605813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59788047652816075474417 44841035739612056605813)
              ·
                refine ⟨4203847100588630306795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44841035739612056605813 4203847100588630306795)
                ·
                  rfl

theorem cell20_27631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 5].length) (baseStart_27631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27631 prefixEnd_27631 := by exact prefixLift 27631
  have htrace : WordTrace (prefixWord ++ tailWord_27631) baseStart_27631 baseEnd_27631 := by
    simpa [prefixWord, tailWord_27631, baseEnd_27631] using wordTrace_append hprefix tailTrace_27631
  have hstable : (prefixWord ++ tailWord_27631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27631).length < 2 ^ (prefixWord ++ tailWord_27631).sum := by decide
  have hdescent : baseEnd_27631 < baseStart_27631 := by decide
  rcases family_descends (prefixWord ++ tailWord_27631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27645 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 6]
def baseStart_27645 : Nat := 118140960795 + 27645 * 2 ^ 59
def prefixEnd_27645 : Nat := 4983230072969 + 3 ^ 40 * 27645 * 2
def baseEnd_27645 : Nat := 12617931283244064453661

theorem tailTrace_27645 : CollatzResearch.WordTrace tailWord_27645 prefixEnd_27645 12617931283244064453661 := by
  unfold tailWord_27645
  simp only [CollatzResearch.WordTrace]
  refine ⟨1008295984854361235220389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 672197323236240823480259 1008295984854361235220389)
  ·
    refine ⟨189055497160192731603823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1008295984854361235220389 189055497160192731603823)
    ·
      refine ⟨283583245740289097405735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189055497160192731603823 283583245740289097405735)
      ·
        refine ⟨425374868610433646108603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283583245740289097405735 425374868610433646108603)
        ·
          refine ⟨638062302915650469162905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425374868610433646108603 638062302915650469162905)
          ·
            refine ⟨478546727186737851872179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 638062302915650469162905 478546727186737851872179)
            ·
              refine ⟨717820090780106777808269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478546727186737851872179 717820090780106777808269)
              ·
                refine ⟨269182534042540041678101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 717820090780106777808269 269182534042540041678101)
                ·
                  refine ⟨12617931283244064453661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 269182534042540041678101 12617931283244064453661)
                  ·
                    rfl

theorem cell20_27645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_27645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27645 prefixEnd_27645 := by exact prefixLift 27645
  have htrace : WordTrace (prefixWord ++ tailWord_27645) baseStart_27645 baseEnd_27645 := by
    simpa [prefixWord, tailWord_27645, baseEnd_27645] using wordTrace_append hprefix tailTrace_27645
  have hstable : (prefixWord ++ tailWord_27645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27645).length < 2 ^ (prefixWord ++ tailWord_27645).sum := by decide
  have hdescent : baseEnd_27645 < baseStart_27645 := by decide
  rcases family_descends (prefixWord ++ tailWord_27645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27679 : List Nat := [1, 1, 2, 4, 1, 4, 1, 4, 2]
def baseStart_27679 : Nat := 118140960795 + 27679 * 2 ^ 59
def prefixEnd_27679 : Nat := 4983230072969 + 3 ^ 40 * 27679 * 2
def baseEnd_27679 : Nat := 12633449809691057320189

theorem tailTrace_27679 : CollatzResearch.WordTrace tailWord_27679 prefixEnd_27679 12633449809691057320189 := by
  unfold tailWord_27679
  simp only [CollatzResearch.WordTrace]
  refine ⟨1009536066731185041958091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 673024044487456694638727 1009536066731185041958091)
  ·
    refine ⟨1514304100096777562937137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1009536066731185041958091 1514304100096777562937137)
    ·
      refine ⟨1135728075072583172202853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1514304100096777562937137 1135728075072583172202853)
      ·
        refine ⟨212949014076109344788035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1135728075072583172202853 212949014076109344788035)
        ·
          refine ⟨319423521114164017182053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212949014076109344788035 319423521114164017182053)
          ·
            refine ⟨59891910208905753221635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 319423521114164017182053 59891910208905753221635)
            ·
              refine ⟨89837865313358629832453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59891910208905753221635 89837865313358629832453)
              ·
                refine ⟨16844599746254743093585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89837865313358629832453 16844599746254743093585)
                ·
                  refine ⟨12633449809691057320189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16844599746254743093585 12633449809691057320189)
                  ·
                    rfl

theorem cell20_27679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 2].length) (baseStart_27679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27679 prefixEnd_27679 := by exact prefixLift 27679
  have htrace : WordTrace (prefixWord ++ tailWord_27679) baseStart_27679 baseEnd_27679 := by
    simpa [prefixWord, tailWord_27679, baseEnd_27679] using wordTrace_append hprefix tailTrace_27679
  have hstable : (prefixWord ++ tailWord_27679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27679).length < 2 ^ (prefixWord ++ tailWord_27679).sum := by decide
  have hdescent : baseEnd_27679 < baseStart_27679 := by decide
  rcases family_descends (prefixWord ++ tailWord_27679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27759 : List Nat := [1, 1, 2, 1, 3, 3, 1, 4, 4]
def baseStart_27759 : Nat := 118140960795 + 27759 * 2 ^ 59
def prefixEnd_27759 : Nat := 4983230072969 + 3 ^ 40 * 27759 * 2
def baseEnd_27759 : Nat := 12669963989566334653195

theorem tailTrace_27759 : CollatzResearch.WordTrace tailWord_27759 prefixEnd_27759 12669963989566334653195 := by
  unfold tailWord_27759
  simp only [CollatzResearch.WordTrace]
  refine ⟨1012453906441358704870331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 674969270960905803246887 1012453906441358704870331)
  ·
    refine ⟨1518680859662038057305497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1012453906441358704870331 1518680859662038057305497)
    ·
      refine ⟨1139010644746528542979123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1518680859662038057305497 1139010644746528542979123)
      ·
        refine ⟨1708515967119792814468685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1139010644746528542979123 1708515967119792814468685)
        ·
          refine ⟨640693487669922305425757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1708515967119792814468685 640693487669922305425757)
          ·
            refine ⟨240260057876220864534659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 640693487669922305425757 240260057876220864534659)
            ·
              refine ⟨360390086814331296801989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240260057876220864534659 360390086814331296801989)
              ·
                refine ⟨67573141277687118150373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 360390086814331296801989 67573141277687118150373)
                ·
                  refine ⟨12669963989566334653195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67573141277687118150373 12669963989566334653195)
                  ·
                    rfl

theorem cell20_27759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 4].length) (baseStart_27759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27759 prefixEnd_27759 := by exact prefixLift 27759
  have htrace : WordTrace (prefixWord ++ tailWord_27759) baseStart_27759 baseEnd_27759 := by
    simpa [prefixWord, tailWord_27759, baseEnd_27759] using wordTrace_append hprefix tailTrace_27759
  have hstable : (prefixWord ++ tailWord_27759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27759).length < 2 ^ (prefixWord ++ tailWord_27759).sum := by decide
  have hdescent : baseEnd_27759 < baseStart_27759 := by decide
  rcases family_descends (prefixWord ++ tailWord_27759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27797 : List Nat := [1, 3, 2, 1, 1, 1, 2, 5, 4]
def baseStart_27797 : Nat := 118140960795 + 27797 * 2 ^ 59
def prefixEnd_27797 : Nat := 4983230072969 + 3 ^ 40 * 27797 * 2
def baseEnd_27797 : Nat := 12687308225007091386373

theorem tailTrace_27797 : CollatzResearch.WordTrace tailWord_27797 prefixEnd_27797 12687308225007091386373 := by
  unfold tailWord_27797
  simp only [CollatzResearch.WordTrace]
  refine ⟨1013839880303691194753645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 675893253535794129835763 1013839880303691194753645)
  ·
    refine ⟨380189955113884198032617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1013839880303691194753645 380189955113884198032617)
    ·
      refine ⟨285142466335413148524463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380189955113884198032617 285142466335413148524463)
      ·
        refine ⟨427713699503119722786695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285142466335413148524463 427713699503119722786695)
        ·
          refine ⟨641570549254679584180043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427713699503119722786695 641570549254679584180043)
          ·
            refine ⟨962355823882019376270065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641570549254679584180043 962355823882019376270065)
            ·
              refine ⟨721766867911514532202549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 962355823882019376270065 721766867911514532202549)
              ·
                refine ⟨67665643866704487393989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 721766867911514532202549 67665643866704487393989)
                ·
                  refine ⟨12687308225007091386373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67665643866704487393989 12687308225007091386373)
                  ·
                    rfl

theorem cell20_27797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_27797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27797 prefixEnd_27797 := by exact prefixLift 27797
  have htrace : WordTrace (prefixWord ++ tailWord_27797) baseStart_27797 baseEnd_27797 := by
    simpa [prefixWord, tailWord_27797, baseEnd_27797] using wordTrace_append hprefix tailTrace_27797
  have hstable : (prefixWord ++ tailWord_27797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27797).length < 2 ^ (prefixWord ++ tailWord_27797).sum := by decide
  have hdescent : baseEnd_27797 < baseStart_27797 := by decide
  rcases family_descends (prefixWord ++ tailWord_27797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27844 : List Nat := [2, 3, 3, 1, 4, 1, 2, 2, 2]
def baseStart_27844 : Nat := 118140960795 + 27844 * 2 ^ 59
def prefixEnd_27844 : Nat := 4983230072969 + 3 ^ 40 * 27844 * 2
def baseEnd_27844 : Nat := 12708760305683816819515

theorem tailTrace_27844 : CollatzResearch.WordTrace tailWord_27844 prefixEnd_27844 12708760305683816819515 := by
  unfold tailWord_27844
  simp only [CollatzResearch.WordTrace]
  refine ⟨507777055566709110857293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 677036074088945481143057 507777055566709110857293)
  ·
    refine ⟨190416395837515916571485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 507777055566709110857293 190416395837515916571485)
    ·
      refine ⟨71406148439068468714307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190416395837515916571485 71406148439068468714307)
      ·
        refine ⟨107109222658602703071461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71406148439068468714307 107109222658602703071461)
        ·
          refine ⟨20082979248488006825899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107109222658602703071461 20082979248488006825899)
          ·
            refine ⟨30124468872732010238849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20082979248488006825899 30124468872732010238849)
            ·
              refine ⟨22593351654549007679137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30124468872732010238849 22593351654549007679137)
              ·
                refine ⟨16945013740911755759353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22593351654549007679137 16945013740911755759353)
                ·
                  refine ⟨12708760305683816819515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16945013740911755759353 12708760305683816819515)
                  ·
                    rfl

theorem cell20_27844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_27844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27844 prefixEnd_27844 := by exact prefixLift 27844
  have htrace : WordTrace (prefixWord ++ tailWord_27844) baseStart_27844 baseEnd_27844 := by
    simpa [prefixWord, tailWord_27844, baseEnd_27844] using wordTrace_append hprefix tailTrace_27844
  have hstable : (prefixWord ++ tailWord_27844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27844).length < 2 ^ (prefixWord ++ tailWord_27844).sum := by decide
  have hdescent : baseEnd_27844 < baseStart_27844 := by decide
  rcases family_descends (prefixWord ++ tailWord_27844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27849 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 9]
def baseStart_27849 : Nat := 118140960795 + 27849 * 2 ^ 59
def prefixEnd_27849 : Nat := 4983230072969 + 3 ^ 40 * 27849 * 2
def baseEnd_27849 : Nat := 12711042441926021652827

theorem tailTrace_27849 : CollatzResearch.WordTrace tailWord_27849 prefixEnd_27849 12711042441926021652827 := by
  unfold tailWord_27849
  simp only [CollatzResearch.WordTrace]
  refine ⟨1015736476115304075646601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 677157650743536050431067 1015736476115304075646601)
  ·
    refine ⟨761802357086478056734951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1015736476115304075646601 761802357086478056734951)
    ·
      refine ⟨1142703535629717085102427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 761802357086478056734951 1142703535629717085102427)
      ·
        refine ⟨1714055303444575627653641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1142703535629717085102427 1714055303444575627653641)
        ·
          refine ⟨1285541477583431720740231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1714055303444575627653641 1285541477583431720740231)
          ·
            refine ⟨1928312216375147581110347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1285541477583431720740231 1928312216375147581110347)
            ·
              refine ⟨2892468324562721371665521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1928312216375147581110347 2892468324562721371665521)
              ·
                refine ⟨2169351243422041028749141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2892468324562721371665521 2169351243422041028749141)
                ·
                  refine ⟨12711042441926021652827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2169351243422041028749141 12711042441926021652827)
                  ·
                    rfl

theorem cell20_27849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_27849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27849 prefixEnd_27849 := by exact prefixLift 27849
  have htrace : WordTrace (prefixWord ++ tailWord_27849) baseStart_27849 baseEnd_27849 := by
    simpa [prefixWord, tailWord_27849, baseEnd_27849] using wordTrace_append hprefix tailTrace_27849
  have hstable : (prefixWord ++ tailWord_27849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27849).length < 2 ^ (prefixWord ++ tailWord_27849).sum := by decide
  have hdescent : baseEnd_27849 < baseStart_27849 := by decide
  rcases family_descends (prefixWord ++ tailWord_27849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27869 : List Nat := [1, 4, 3, 2, 2, 1, 1, 2, 4]
def baseStart_27869 : Nat := 118140960795 + 27869 * 2 ^ 59
def prefixEnd_27869 : Nat := 4983230072969 + 3 ^ 40 * 27869 * 2
def baseEnd_27869 : Nat := 12720170986894840986079

theorem tailTrace_27869 : CollatzResearch.WordTrace tailWord_27869 prefixEnd_27869 12720170986894840986079 := by
  unfold tailWord_27869
  simp only [CollatzResearch.WordTrace]
  refine ⟨1016465936042847491374661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 677643957361898327583107 1016465936042847491374661)
  ·
    refine ⟨190587363008033904632749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1016465936042847491374661 190587363008033904632749)
    ·
      refine ⟨71470261128012714237281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190587363008033904632749 71470261128012714237281)
      ·
        refine ⟨53602695846009535677961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71470261128012714237281 53602695846009535677961)
        ·
          refine ⟨40202021884507151758471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53602695846009535677961 40202021884507151758471)
          ·
            refine ⟨60303032826760727637707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40202021884507151758471 60303032826760727637707)
            ·
              refine ⟨90454549240141091456561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60303032826760727637707 90454549240141091456561)
              ·
                refine ⟨67840911930105818592421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90454549240141091456561 67840911930105818592421)
                ·
                  refine ⟨12720170986894840986079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67840911930105818592421 12720170986894840986079)
                  ·
                    rfl

theorem cell20_27869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_27869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27869 prefixEnd_27869 := by exact prefixLift 27869
  have htrace : WordTrace (prefixWord ++ tailWord_27869) baseStart_27869 baseEnd_27869 := by
    simpa [prefixWord, tailWord_27869, baseEnd_27869] using wordTrace_append hprefix tailTrace_27869
  have hstable : (prefixWord ++ tailWord_27869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27869).length < 2 ^ (prefixWord ++ tailWord_27869).sum := by decide
  have hdescent : baseEnd_27869 < baseStart_27869 := by decide
  rcases family_descends (prefixWord ++ tailWord_27869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27873 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 6]
def baseStart_27873 : Nat := 118140960795 + 27873 * 2 ^ 59
def prefixEnd_27873 : Nat := 4983230072969 + 3 ^ 40 * 27873 * 2
def baseEnd_27873 : Nat := 12721996695888604852729

theorem tailTrace_27873 : CollatzResearch.WordTrace tailWord_27873 prefixEnd_27873 12721996695888604852729 := by
  unfold tailWord_27873
  simp only [CollatzResearch.WordTrace]
  refine ⟨1016611828028356174520273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 677741218685570783013515 1016611828028356174520273)
  ·
    refine ⟨762458871021267130890205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1016611828028356174520273 762458871021267130890205)
    ·
      refine ⟨285922076632975174083827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 762458871021267130890205 285922076632975174083827)
      ·
        refine ⟨428883114949462761125741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285922076632975174083827 428883114949462761125741)
        ·
          refine ⟨160831168106048535422153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 428883114949462761125741 160831168106048535422153)
          ·
            refine ⟨120623376079536401566615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160831168106048535422153 120623376079536401566615)
            ·
              refine ⟨180935064119304602349923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120623376079536401566615 180935064119304602349923)
              ·
                refine ⟨271402596178956903524885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180935064119304602349923 271402596178956903524885)
                ·
                  refine ⟨12721996695888604852729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 271402596178956903524885 12721996695888604852729)
                  ·
                    rfl

theorem cell20_27873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_27873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27873 prefixEnd_27873 := by exact prefixLift 27873
  have htrace : WordTrace (prefixWord ++ tailWord_27873) baseStart_27873 baseEnd_27873 := by
    simpa [prefixWord, tailWord_27873, baseEnd_27873] using wordTrace_append hprefix tailTrace_27873
  have hstable : (prefixWord ++ tailWord_27873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27873).length < 2 ^ (prefixWord ++ tailWord_27873).sum := by decide
  have hdescent : baseEnd_27873 < baseStart_27873 := by decide
  rcases family_descends (prefixWord ++ tailWord_27873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27900 : List Nat := [2, 2, 2, 1, 5, 2, 1, 2, 3]
def baseStart_27900 : Nat := 118140960795 + 27900 * 2 ^ 59
def prefixEnd_27900 : Nat := 4983230072969 + 3 ^ 40 * 27900 * 2
def baseEnd_27900 : Nat := 12734320231596510952619

theorem tailTrace_27900 : CollatzResearch.WordTrace tailWord_27900 prefixEnd_27900 12734320231596510952619 := by
  unfold tailWord_27900
  simp only [CollatzResearch.WordTrace]
  refine ⟨508798299465269892876577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 678397732620359857168769 508798299465269892876577)
  ·
    refine ⟨381598724598952419657433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 508798299465269892876577 381598724598952419657433)
    ·
      refine ⟨286199043449214314743075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381598724598952419657433 286199043449214314743075)
      ·
        refine ⟨429298565173821472114613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286199043449214314743075 429298565173821472114613)
        ·
          refine ⟨40246740485045763010745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 429298565173821472114613 40246740485045763010745)
          ·
            refine ⟨30185055363784322258059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40246740485045763010745 30185055363784322258059)
            ·
              refine ⟨45277583045676483387089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30185055363784322258059 45277583045676483387089)
              ·
                refine ⟨33958187284257362540317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45277583045676483387089 33958187284257362540317)
                ·
                  refine ⟨12734320231596510952619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33958187284257362540317 12734320231596510952619)
                  ·
                    rfl

theorem cell20_27900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_27900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27900 prefixEnd_27900 := by exact prefixLift 27900
  have htrace : WordTrace (prefixWord ++ tailWord_27900) baseStart_27900 baseEnd_27900 := by
    simpa [prefixWord, tailWord_27900, baseEnd_27900] using wordTrace_append hprefix tailTrace_27900
  have hstable : (prefixWord ++ tailWord_27900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27900).length < 2 ^ (prefixWord ++ tailWord_27900).sum := by decide
  have hdescent : baseEnd_27900 < baseStart_27900 := by decide
  rcases family_descends (prefixWord ++ tailWord_27900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27921 : List Nat := [1, 2, 2, 1, 1, 4, 5, 1, 3]
def baseStart_27921 : Nat := 118140960795 + 27921 * 2 ^ 59
def prefixEnd_27921 : Nat := 4983230072969 + 3 ^ 40 * 27921 * 2
def baseEnd_27921 : Nat := 12743905203813771252533

theorem tailTrace_27921 : CollatzResearch.WordTrace tailWord_27921 prefixEnd_27921 12743905203813771252533 := by
  unfold tailWord_27921
  simp only [CollatzResearch.WordTrace]
  refine ⟨1018362531854460372267617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 678908354569640248178411 1018362531854460372267617)
  ·
    refine ⟨763771898890845279200713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1018362531854460372267617 763771898890845279200713)
    ·
      refine ⟨572828924168133959400535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 763771898890845279200713 572828924168133959400535)
      ·
        refine ⟨859243386252200939100803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572828924168133959400535 859243386252200939100803)
        ·
          refine ⟨1288865079378301408651205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859243386252200939100803 1288865079378301408651205)
          ·
            refine ⟨241662202383431514122101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1288865079378301408651205 241662202383431514122101)
            ·
              refine ⟨22655831473446704448947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 241662202383431514122101 22655831473446704448947)
              ·
                refine ⟨33983747210170056673421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22655831473446704448947 33983747210170056673421)
                ·
                  refine ⟨12743905203813771252533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33983747210170056673421 12743905203813771252533)
                  ·
                    rfl

theorem cell20_27921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 3].length) (baseStart_27921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27921 prefixEnd_27921 := by exact prefixLift 27921
  have htrace : WordTrace (prefixWord ++ tailWord_27921) baseStart_27921 baseEnd_27921 := by
    simpa [prefixWord, tailWord_27921, baseEnd_27921] using wordTrace_append hprefix tailTrace_27921
  have hstable : (prefixWord ++ tailWord_27921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27921).length < 2 ^ (prefixWord ++ tailWord_27921).sum := by decide
  have hdescent : baseEnd_27921 < baseStart_27921 := by decide
  rcases family_descends (prefixWord ++ tailWord_27921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27935 : List Nat := [1, 1, 2, 4, 4, 1, 1, 6]
def baseStart_27935 : Nat := 118140960795 + 27935 * 2 ^ 59
def prefixEnd_27935 : Nat := 4983230072969 + 3 ^ 40 * 27935 * 2
def baseEnd_27935 : Nat := 4250098395097314928603

theorem tailTrace_27935 : CollatzResearch.WordTrace tailWord_27935 prefixEnd_27935 4250098395097314928603 := by
  unfold tailWord_27935
  simp only [CollatzResearch.WordTrace]
  refine ⟨1018873153803740763277259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 679248769202493842184839 1018873153803740763277259)
  ·
    refine ⟨1528309730705611144915889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1018873153803740763277259 1528309730705611144915889)
    ·
      refine ⟨1146232298029208358686917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1528309730705611144915889 1146232298029208358686917)
      ·
        refine ⟨214918555880476567253797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1146232298029208358686917 214918555880476567253797)
        ·
          refine ⟨40297229227589356360087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214918555880476567253797 40297229227589356360087)
          ·
            refine ⟨60445843841384034540131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40297229227589356360087 60445843841384034540131)
            ·
              refine ⟨90668765762076051810197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60445843841384034540131 90668765762076051810197)
              ·
                refine ⟨4250098395097314928603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90668765762076051810197 4250098395097314928603)
                ·
                  rfl

theorem cell20_27935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 6].length) (baseStart_27935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27935 prefixEnd_27935 := by exact prefixLift 27935
  have htrace : WordTrace (prefixWord ++ tailWord_27935) baseStart_27935 baseEnd_27935 := by
    simpa [prefixWord, tailWord_27935, baseEnd_27935] using wordTrace_append hprefix tailTrace_27935
  have hstable : (prefixWord ++ tailWord_27935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27935).length < 2 ^ (prefixWord ++ tailWord_27935).sum := by decide
  have hdescent : baseEnd_27935 < baseStart_27935 := by decide
  rcases family_descends (prefixWord ++ tailWord_27935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27958 : List Nat := [5, 1, 2, 3, 1, 1, 3, 2, 2]
def baseStart_27958 : Nat := 118140960795 + 27958 * 2 ^ 59
def prefixEnd_27958 : Nat := 4983230072969 + 3 ^ 40 * 27958 * 2
def baseEnd_27958 : Nat := 12760793012006087019049

theorem tailTrace_27958 : CollatzResearch.WordTrace tailWord_27958 prefixEnd_27958 12760793012006087019049 := by
  unfold tailWord_27958
  simp only [CollatzResearch.WordTrace]
  refine ⟨63732002045025980710283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 679808021813610460909685 63732002045025980710283)
  ·
    refine ⟨95598003067538971065425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63732002045025980710283 95598003067538971065425)
    ·
      refine ⟨71698502300654228299069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95598003067538971065425 71698502300654228299069)
      ·
        refine ⟨26886938362745335612151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71698502300654228299069 26886938362745335612151)
        ·
          refine ⟨40330407544118003418227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26886938362745335612151 40330407544118003418227)
          ·
            refine ⟨60495611316177005127341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40330407544118003418227 60495611316177005127341)
            ·
              refine ⟨22685854243566376922753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60495611316177005127341 22685854243566376922753)
              ·
                refine ⟨17014390682674782692065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22685854243566376922753 17014390682674782692065)
                ·
                  refine ⟨12760793012006087019049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17014390682674782692065 12760793012006087019049)
                  ·
                    rfl

theorem cell20_27958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_27958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27958 prefixEnd_27958 := by exact prefixLift 27958
  have htrace : WordTrace (prefixWord ++ tailWord_27958) baseStart_27958 baseEnd_27958 := by
    simpa [prefixWord, tailWord_27958, baseEnd_27958] using wordTrace_append hprefix tailTrace_27958
  have hstable : (prefixWord ++ tailWord_27958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27958).length < 2 ^ (prefixWord ++ tailWord_27958).sum := by decide
  have hdescent : baseEnd_27958 < baseStart_27958 := by decide
  rcases family_descends (prefixWord ++ tailWord_27958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27994 : List Nat := [3, 1, 1, 2, 1, 2, 4, 6]
def baseStart_27994 : Nat := 118140960795 + 27994 * 2 ^ 59
def prefixEnd_27994 : Nat := 4983230072969 + 3 ^ 40 * 27994 * 2
def baseEnd_27994 : Nat := 4259074797649987272967

theorem tailTrace_27994 : CollatzResearch.WordTrace tailWord_27994 prefixEnd_27994 4259074797649987272967 := by
  unfold tailWord_27994
  simp only [CollatzResearch.WordTrace]
  refine ⟨255256265147498459918759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 680683373726662559783357 255256265147498459918759)
  ·
    refine ⟨382884397721247689878139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255256265147498459918759 382884397721247689878139)
    ·
      refine ⟨574326596581871534817209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382884397721247689878139 574326596581871534817209)
      ·
        refine ⟨430744947436403651112907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 574326596581871534817209 430744947436403651112907)
        ·
          refine ⟨646117421154605476669361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430744947436403651112907 646117421154605476669361)
          ·
            refine ⟨484588065865954107502021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 646117421154605476669361 484588065865954107502021)
            ·
              refine ⟨90860262349866395156629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 484588065865954107502021 90860262349866395156629)
              ·
                refine ⟨4259074797649987272967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90860262349866395156629 4259074797649987272967)
                ·
                  rfl

theorem cell20_27994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_27994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_27994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_27994 prefixEnd_27994 := by exact prefixLift 27994
  have htrace : WordTrace (prefixWord ++ tailWord_27994) baseStart_27994 baseEnd_27994 := by
    simpa [prefixWord, tailWord_27994, baseEnd_27994] using wordTrace_append hprefix tailTrace_27994
  have hstable : (prefixWord ++ tailWord_27994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27994).length < 2 ^ (prefixWord ++ tailWord_27994).sum := by decide
  have hdescent : baseEnd_27994 < baseStart_27994 := by decide
  rcases family_descends (prefixWord ++ tailWord_27994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28001 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 7]
def baseStart_28001 : Nat := 118140960795 + 28001 * 2 ^ 59
def prefixEnd_28001 : Nat := 4983230072969 + 3 ^ 40 * 28001 * 2
def baseEnd_28001 : Nat := 12780419383689048585539

theorem tailTrace_28001 : CollatzResearch.WordTrace tailWord_28001 prefixEnd_28001 12780419383689048585539 := by
  unfold tailWord_28001
  simp only [CollatzResearch.WordTrace]
  refine ⟨1021280371564634035179857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 680853581043089356786571 1021280371564634035179857)
  ·
    refine ⟨765960278673475526384893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1021280371564634035179857 765960278673475526384893)
    ·
      refine ⟨287235104502553322394335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 765960278673475526384893 287235104502553322394335)
      ·
        refine ⟨430852656753829983591503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287235104502553322394335 430852656753829983591503)
        ·
          refine ⟨646278985130744975387255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430852656753829983591503 646278985130744975387255)
          ·
            refine ⟨969418477696117463080883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646278985130744975387255 969418477696117463080883)
            ·
              refine ⟨1454127716544176194621325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 969418477696117463080883 1454127716544176194621325)
              ·
                refine ⟨545297893704066072982997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1454127716544176194621325 545297893704066072982997)
                ·
                  refine ⟨12780419383689048585539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 545297893704066072982997 12780419383689048585539)
                  ·
                    rfl

theorem cell20_28001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_28001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28001 prefixEnd_28001 := by exact prefixLift 28001
  have htrace : WordTrace (prefixWord ++ tailWord_28001) baseStart_28001 baseEnd_28001 := by
    simpa [prefixWord, tailWord_28001, baseEnd_28001] using wordTrace_append hprefix tailTrace_28001
  have hstable : (prefixWord ++ tailWord_28001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28001).length < 2 ^ (prefixWord ++ tailWord_28001).sum := by decide
  have hdescent : baseEnd_28001 < baseStart_28001 := by decide
  rcases family_descends (prefixWord ++ tailWord_28001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28125 : List Nat := [1, 4, 3, 1, 1, 4, 6]
def baseStart_28125 : Nat := 118140960795 + 28125 * 2 ^ 59
def prefixEnd_28125 : Nat := 4983230072969 + 3 ^ 40 * 28125 * 2
def baseEnd_28125 : Nat := 1426335151388414272411

theorem tailTrace_28125 : CollatzResearch.WordTrace tailWord_28125 prefixEnd_28125 1426335151388414272411 := by
  unfold tailWord_28125
  simp only [CollatzResearch.WordTrace]
  refine ⟨1025803023115403212693829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 683868682076935475129219 1025803023115403212693829)
  ·
    refine ⟨192338066834138102380093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1025803023115403212693829 192338066834138102380093)
    ·
      refine ⟨72126775062801788392535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192338066834138102380093 72126775062801788392535)
      ·
        refine ⟨108190162594202682588803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72126775062801788392535 108190162594202682588803)
        ·
          refine ⟨162285243891304023883205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108190162594202682588803 162285243891304023883205)
          ·
            refine ⟨30428483229619504478101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162285243891304023883205 30428483229619504478101)
            ·
              refine ⟨1426335151388414272411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30428483229619504478101 1426335151388414272411)
              ·
                rfl

theorem cell20_28125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 6].length) (baseStart_28125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28125 prefixEnd_28125 := by exact prefixLift 28125
  have htrace : WordTrace (prefixWord ++ tailWord_28125) baseStart_28125 baseEnd_28125 := by
    simpa [prefixWord, tailWord_28125, baseEnd_28125] using wordTrace_append hprefix tailTrace_28125
  have hstable : (prefixWord ++ tailWord_28125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28125).length < 2 ^ (prefixWord ++ tailWord_28125).sum := by decide
  have hdescent : baseEnd_28125 < baseStart_28125 := by decide
  rcases family_descends (prefixWord ++ tailWord_28125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28180 : List Nat := [2, 4, 3, 1, 3, 7]
def baseStart_28180 : Nat := 118140960795 + 28180 * 2 ^ 59
def prefixEnd_28180 : Nat := 4983230072969 + 3 ^ 40 * 28180 * 2
def baseEnd_28180 : Nat := 476374809672591911783

theorem tailTrace_28180 : CollatzResearch.WordTrace tailWord_28180 prefixEnd_28180 476374809672591911783 := by
  unfold tailWord_28180
  simp only [CollatzResearch.WordTrace]
  refine ⟨513904518958073802972997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 685206025277431737297329 513904518958073802972997)
  ·
    refine ⟨96357097304638838057437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 513904518958073802972997 96357097304638838057437)
    ·
      refine ⟨36133911489239564271539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96357097304638838057437 36133911489239564271539)
      ·
        refine ⟨54200867233859346407309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36133911489239564271539 54200867233859346407309)
        ·
          refine ⟨20325325212697254902741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54200867233859346407309 20325325212697254902741)
          ·
            refine ⟨476374809672591911783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 20325325212697254902741 476374809672591911783)
            ·
              rfl

theorem cell20_28180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 7].length) (baseStart_28180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28180 prefixEnd_28180 := by exact prefixLift 28180
  have htrace : WordTrace (prefixWord ++ tailWord_28180) baseStart_28180 baseEnd_28180 := by
    simpa [prefixWord, tailWord_28180, baseEnd_28180] using wordTrace_append hprefix tailTrace_28180
  have hstable : (prefixWord ++ tailWord_28180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28180).length < 2 ^ (prefixWord ++ tailWord_28180).sum := by decide
  have hdescent : baseEnd_28180 < baseStart_28180 := by decide
  rcases family_descends (prefixWord ++ tailWord_28180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28184 : List Nat := [2, 1, 2, 3, 4, 8]
def baseStart_28184 : Nat := 118140960795 + 28184 * 2 ^ 59
def prefixEnd_28184 : Nat := 4983230072969 + 3 ^ 40 * 28184 * 2
def baseEnd_28184 : Nat := 476442428524212795733

theorem tailTrace_28184 : CollatzResearch.WordTrace tailWord_28184 prefixEnd_28184 476442428524212795733 := by
  unfold tailWord_28184
  simp only [CollatzResearch.WordTrace]
  refine ⟨513977464950828144545803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 685303286601104192727737 513977464950828144545803)
  ·
    refine ⟨770966197426242216818705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 513977464950828144545803 770966197426242216818705)
    ·
      refine ⟨578224648069681662614029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 770966197426242216818705 578224648069681662614029)
      ·
        refine ⟨216834243026130623480261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 578224648069681662614029 216834243026130623480261)
        ·
          refine ⟨40656420567399491902549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216834243026130623480261 40656420567399491902549)
          ·
            refine ⟨476442428524212795733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 40656420567399491902549 476442428524212795733)
            ·
              rfl

theorem cell20_28184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 8].length) (baseStart_28184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28184 prefixEnd_28184 := by exact prefixLift 28184
  have htrace : WordTrace (prefixWord ++ tailWord_28184) baseStart_28184 baseEnd_28184 := by
    simpa [prefixWord, tailWord_28184, baseEnd_28184] using wordTrace_append hprefix tailTrace_28184
  have hstable : (prefixWord ++ tailWord_28184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28184).length < 2 ^ (prefixWord ++ tailWord_28184).sum := by decide
  have hdescent : baseEnd_28184 < baseStart_28184 := by decide
  rcases family_descends (prefixWord ++ tailWord_28184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28191 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 5]
def baseStart_28191 : Nat := 118140960795 + 28191 * 2 ^ 59
def prefixEnd_28191 : Nat := 4983230072969 + 3 ^ 40 * 28191 * 2
def baseEnd_28191 : Nat := 12867140560892832251429

theorem tailTrace_28191 : CollatzResearch.WordTrace tailWord_28191 prefixEnd_28191 12867140560892832251429 := by
  unfold tailWord_28191
  simp only [CollatzResearch.WordTrace]
  refine ⟨1028210240876296484596427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 685473493917530989730951 1028210240876296484596427)
  ·
    refine ⟨1542315361314444726894641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1028210240876296484596427 1542315361314444726894641)
    ·
      refine ⟨1156736520985833545170981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1542315361314444726894641 1156736520985833545170981)
      ·
        refine ⟨216888097684843789719559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1156736520985833545170981 216888097684843789719559)
        ·
          refine ⟨325332146527265684579339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216888097684843789719559 325332146527265684579339)
          ·
            refine ⟨487998219790898526869009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325332146527265684579339 487998219790898526869009)
            ·
              refine ⟨365998664843173895151757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487998219790898526869009 365998664843173895151757)
              ·
                refine ⟨137249499316190210681909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365998664843173895151757 137249499316190210681909)
                ·
                  refine ⟨12867140560892832251429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137249499316190210681909 12867140560892832251429)
                  ·
                    rfl

theorem cell20_28191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_28191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28191 prefixEnd_28191 := by exact prefixLift 28191
  have htrace : WordTrace (prefixWord ++ tailWord_28191) baseStart_28191 baseEnd_28191 := by
    simpa [prefixWord, tailWord_28191, baseEnd_28191] using wordTrace_append hprefix tailTrace_28191
  have hstable : (prefixWord ++ tailWord_28191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28191).length < 2 ^ (prefixWord ++ tailWord_28191).sum := by decide
  have hdescent : baseEnd_28191 < baseStart_28191 := by decide
  rcases family_descends (prefixWord ++ tailWord_28191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28215 : List Nat := [1, 1, 3, 1, 2, 5, 1, 2, 4]
def baseStart_28215 : Nat := 118140960795 + 28215 * 2 ^ 59
def prefixEnd_28215 : Nat := 4983230072969 + 3 ^ 40 * 28215 * 2
def baseEnd_28215 : Nat := 12878094814855415451331

theorem tailTrace_28215 : CollatzResearch.WordTrace tailWord_28215 prefixEnd_28215 12878094814855415451331 := by
  unfold tailWord_28215
  simp only [CollatzResearch.WordTrace]
  refine ⟨1029085592789348583470099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 686057061859565722313399 1029085592789348583470099)
  ·
    refine ⟨1543628389184022875205149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1029085592789348583470099 1543628389184022875205149)
    ·
      refine ⟨578860645944008578201931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1543628389184022875205149 578860645944008578201931)
      ·
        refine ⟨868290968916012867302897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578860645944008578201931 868290968916012867302897)
        ·
          refine ⟨651218226687009650477173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 868290968916012867302897 651218226687009650477173)
          ·
            refine ⟨61051708751907154732235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 651218226687009650477173 61051708751907154732235)
            ·
              refine ⟨91577563127860732098353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61051708751907154732235 91577563127860732098353)
              ·
                refine ⟨68683172345895549073765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91577563127860732098353 68683172345895549073765)
                ·
                  refine ⟨12878094814855415451331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68683172345895549073765 12878094814855415451331)
                  ·
                    rfl

theorem cell20_28215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 4].length) (baseStart_28215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28215 prefixEnd_28215 := by exact prefixLift 28215
  have htrace : WordTrace (prefixWord ++ tailWord_28215) baseStart_28215 baseEnd_28215 := by
    simpa [prefixWord, tailWord_28215, baseEnd_28215] using wordTrace_append hprefix tailTrace_28215
  have hstable : (prefixWord ++ tailWord_28215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28215).length < 2 ^ (prefixWord ++ tailWord_28215).sum := by decide
  have hdescent : baseEnd_28215 < baseStart_28215 := by decide
  rcases family_descends (prefixWord ++ tailWord_28215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28229 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 5]
def baseStart_28229 : Nat := 118140960795 + 28229 * 2 ^ 59
def prefixEnd_28229 : Nat := 4983230072969 + 3 ^ 40 * 28229 * 2
def baseEnd_28229 : Nat := 12884484796333588984607

theorem tailTrace_28229 : CollatzResearch.WordTrace tailWord_28229 prefixEnd_28229 12884484796333588984607 := by
  unfold tailWord_28229
  simp only [CollatzResearch.WordTrace]
  refine ⟨1029596214738628974479741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 686397476492419316319827 1029596214738628974479741)
  ·
    refine ⟨386098580526985865429903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1029596214738628974479741 386098580526985865429903)
    ·
      refine ⟨579147870790478798144855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386098580526985865429903 579147870790478798144855)
      ·
        refine ⟨868721806185718197217283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579147870790478798144855 868721806185718197217283)
        ·
          refine ⟨1303082709278577295825925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 868721806185718197217283 1303082709278577295825925)
          ·
            refine ⟨244328007989733242967361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1303082709278577295825925 244328007989733242967361)
            ·
              refine ⟨183246005992299932225521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244328007989733242967361 183246005992299932225521)
              ·
                refine ⟨137434504494224949169141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183246005992299932225521 137434504494224949169141)
                ·
                  refine ⟨12884484796333588984607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137434504494224949169141 12884484796333588984607)
                  ·
                    rfl

theorem cell20_28229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_28229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28229 prefixEnd_28229 := by exact prefixLift 28229
  have htrace : WordTrace (prefixWord ++ tailWord_28229) baseStart_28229 baseEnd_28229 := by
    simpa [prefixWord, tailWord_28229, baseEnd_28229] using wordTrace_append hprefix tailTrace_28229
  have hstable : (prefixWord ++ tailWord_28229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28229).length < 2 ^ (prefixWord ++ tailWord_28229).sum := by decide
  have hdescent : baseEnd_28229 < baseStart_28229 := by decide
  rcases family_descends (prefixWord ++ tailWord_28229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28277 : List Nat := [1, 3, 4, 2, 1, 2, 1, 6]
def baseStart_28277 : Nat := 118140960795 + 28277 * 2 ^ 59
def prefixEnd_28277 : Nat := 4983230072969 + 3 ^ 40 * 28277 * 2
def baseEnd_28277 : Nat := 4302131101419585128137

theorem tailTrace_28277 : CollatzResearch.WordTrace tailWord_28277 prefixEnd_28277 4302131101419585128137 := by
  unfold tailWord_28277
  simp only [CollatzResearch.WordTrace]
  refine ⟨1031346918564733172227085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 687564612376488781484723 1031346918564733172227085)
  ·
    refine ⟨386755094461774939585157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1031346918564733172227085 386755094461774939585157)
    ·
      refine ⟨72516580211582801172217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 386755094461774939585157 72516580211582801172217)
      ·
        refine ⟨54387435158687100879163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72516580211582801172217 54387435158687100879163)
        ·
          refine ⟨81581152738030651318745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54387435158687100879163 81581152738030651318745)
          ·
            refine ⟨61185864553522988489059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81581152738030651318745 61185864553522988489059)
            ·
              refine ⟨91778796830284482733589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61185864553522988489059 91778796830284482733589)
              ·
                refine ⟨4302131101419585128137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91778796830284482733589 4302131101419585128137)
                ·
                  rfl

theorem cell20_28277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 6].length) (baseStart_28277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28277 prefixEnd_28277 := by exact prefixLift 28277
  have htrace : WordTrace (prefixWord ++ tailWord_28277) baseStart_28277 baseEnd_28277 := by
    simpa [prefixWord, tailWord_28277, baseEnd_28277] using wordTrace_append hprefix tailTrace_28277
  have hstable : (prefixWord ++ tailWord_28277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28277).length < 2 ^ (prefixWord ++ tailWord_28277).sum := by decide
  have hdescent : baseEnd_28277 < baseStart_28277 := by decide
  rcases family_descends (prefixWord ++ tailWord_28277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28298 : List Nat := [3, 1, 2, 3, 2, 1, 8]
def baseStart_28298 : Nat := 118140960795 + 28298 * 2 ^ 59
def prefixEnd_28298 : Nat := 4983230072969 + 3 ^ 40 * 28298 * 2
def baseEnd_28298 : Nat := 1435108697386223964925

theorem tailTrace_28298 : CollatzResearch.WordTrace tailWord_28298 prefixEnd_28298 1435108697386223964925 := by
  unfold tailWord_28298
  simp only [CollatzResearch.WordTrace]
  refine ⟨258028212872163439685387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 688075234325769172494365 258028212872163439685387)
  ·
    refine ⟨387042319308245159528081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258028212872163439685387 387042319308245159528081)
    ·
      refine ⟨290281739481183869646061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387042319308245159528081 290281739481183869646061)
      ·
        refine ⟨108855652305443951117273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290281739481183869646061 108855652305443951117273)
        ·
          refine ⟨81641739229082963337955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108855652305443951117273 81641739229082963337955)
          ·
            refine ⟨122462608843624445006933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81641739229082963337955 122462608843624445006933)
            ·
              refine ⟨1435108697386223964925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 122462608843624445006933 1435108697386223964925)
              ·
                rfl

theorem cell20_28298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 8].length) (baseStart_28298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28298 prefixEnd_28298 := by exact prefixLift 28298
  have htrace : WordTrace (prefixWord ++ tailWord_28298) baseStart_28298 baseEnd_28298 := by
    simpa [prefixWord, tailWord_28298, baseEnd_28298] using wordTrace_append hprefix tailTrace_28298
  have hstable : (prefixWord ++ tailWord_28298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28298).length < 2 ^ (prefixWord ++ tailWord_28298).sum := by decide
  have hdescent : baseEnd_28298 < baseStart_28298 := by decide
  rcases family_descends (prefixWord ++ tailWord_28298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28318 : List Nat := [4, 3, 1, 1, 1, 2, 4, 1, 3]
def baseStart_28318 : Nat := 118140960795 + 28318 * 2 ^ 59
def prefixEnd_28318 : Nat := 4983230072969 + 3 ^ 40 * 28318 * 2
def baseEnd_28318 : Nat := 12925106821444835017577

theorem tailTrace_28318 : CollatzResearch.WordTrace tailWord_28318 prefixEnd_28318 12925106821444835017577 := by
  unfold tailWord_28318
  simp only [CollatzResearch.WordTrace]
  refine ⟨129105288927024646808701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 688561540944131449646405 129105288927024646808701)
  ·
    refine ⟨48414483347634242553263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129105288927024646808701 48414483347634242553263)
    ·
      refine ⟨72621725021451363829895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48414483347634242553263 72621725021451363829895)
      ·
        refine ⟨108932587532177045744843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72621725021451363829895 108932587532177045744843)
        ·
          refine ⟨163398881298265568617265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108932587532177045744843 163398881298265568617265)
          ·
            refine ⟨122549160973699176462949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163398881298265568617265 122549160973699176462949)
            ·
              refine ⟨22977967682568595586803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122549160973699176462949 22977967682568595586803)
              ·
                refine ⟨34466951523852893380205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22977967682568595586803 34466951523852893380205)
                ·
                  refine ⟨12925106821444835017577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34466951523852893380205 12925106821444835017577)
                  ·
                    rfl

theorem cell20_28318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_28318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28318 prefixEnd_28318 := by exact prefixLift 28318
  have htrace : WordTrace (prefixWord ++ tailWord_28318) baseStart_28318 baseEnd_28318 := by
    simpa [prefixWord, tailWord_28318, baseEnd_28318] using wordTrace_append hprefix tailTrace_28318
  have hstable : (prefixWord ++ tailWord_28318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28318).length < 2 ^ (prefixWord ++ tailWord_28318).sum := by decide
  have hdescent : baseEnd_28318 < baseStart_28318 := by decide
  rcases family_descends (prefixWord ++ tailWord_28318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28360 : List Nat := [2, 1, 3, 1, 2, 2, 4, 2, 3]
def baseStart_28360 : Nat := 118140960795 + 28360 * 2 ^ 59
def prefixEnd_28360 : Nat := 4983230072969 + 3 ^ 40 * 28360 * 2
def baseEnd_28360 : Nat := 12944276765879355617405

theorem tailTrace_28360 : CollatzResearch.WordTrace tailWord_28360 prefixEnd_28360 12944276765879355617405 := by
  unfold tailWord_28360
  simp only [CollatzResearch.WordTrace]
  refine ⟨517187088632019173749267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 689582784842692231665689 517187088632019173749267)
  ·
    refine ⟨775780632948028760623901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 517187088632019173749267 775780632948028760623901)
    ·
      refine ⟨290917737355510785233963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 775780632948028760623901 290917737355510785233963)
      ·
        refine ⟨436376606033266177850945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290917737355510785233963 436376606033266177850945)
        ·
          refine ⟨327282454524949633388209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436376606033266177850945 327282454524949633388209)
          ·
            refine ⟨245461840893712225041157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327282454524949633388209 245461840893712225041157)
            ·
              refine ⟨46024095167571042195217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 245461840893712225041157 46024095167571042195217)
              ·
                refine ⟨34518071375678281646413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46024095167571042195217 34518071375678281646413)
                ·
                  refine ⟨12944276765879355617405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34518071375678281646413 12944276765879355617405)
                  ·
                    rfl

theorem cell20_28360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 3].length) (baseStart_28360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28360 prefixEnd_28360 := by exact prefixLift 28360
  have htrace : WordTrace (prefixWord ++ tailWord_28360) baseStart_28360 baseEnd_28360 := by
    simpa [prefixWord, tailWord_28360, baseEnd_28360] using wordTrace_append hprefix tailTrace_28360
  have hstable : (prefixWord ++ tailWord_28360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28360).length < 2 ^ (prefixWord ++ tailWord_28360).sum := by decide
  have hdescent : baseEnd_28360 < baseStart_28360 := by decide
  rcases family_descends (prefixWord ++ tailWord_28360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28395 : List Nat := [1, 1, 1, 1, 2, 4, 2, 8]
def baseStart_28395 : Nat := 118140960795 + 28395 * 2 ^ 59
def prefixEnd_28395 : Nat := 4983230072969 + 3 ^ 40 * 28395 * 2
def baseEnd_28395 : Nat := 4320083906524929816865

theorem tailTrace_28395 : CollatzResearch.WordTrace tailWord_28395 prefixEnd_28395 4320083906524929816865 := by
  unfold tailWord_28395
  simp only [CollatzResearch.WordTrace]
  refine ⟨1035650732137239325022639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 690433821424826216681759 1035650732137239325022639)
  ·
    refine ⟨1553476098205858987533959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1035650732137239325022639 1553476098205858987533959)
    ·
      refine ⟨2330214147308788481300939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1553476098205858987533959 2330214147308788481300939)
      ·
        refine ⟨3495321220963182721951409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2330214147308788481300939 3495321220963182721951409)
        ·
          refine ⟨2621490915722387041463557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3495321220963182721951409 2621490915722387041463557)
          ·
            refine ⟨491529546697947570274417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2621490915722387041463557 491529546697947570274417)
            ·
              refine ⟨368647160023460677705813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491529546697947570274417 368647160023460677705813)
              ·
                refine ⟨4320083906524929816865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 368647160023460677705813 4320083906524929816865)
                ·
                  rfl

theorem cell20_28395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 8].length) (baseStart_28395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28395 prefixEnd_28395 := by exact prefixLift 28395
  have htrace : WordTrace (prefixWord ++ tailWord_28395) baseStart_28395 baseEnd_28395 := by
    simpa [prefixWord, tailWord_28395, baseEnd_28395] using wordTrace_append hprefix tailTrace_28395
  have hstable : (prefixWord ++ tailWord_28395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28395).length < 2 ^ (prefixWord ++ tailWord_28395).sum := by decide
  have hdescent : baseEnd_28395 < baseStart_28395 := by decide
  rcases family_descends (prefixWord ++ tailWord_28395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28433 : List Nat := [1, 2, 2, 1, 1, 3, 1, 9]
def baseStart_28433 : Nat := 118140960795 + 28433 * 2 ^ 59
def prefixEnd_28433 : Nat := 4983230072969 + 3 ^ 40 * 28433 * 2
def baseEnd_28433 : Nat := 4325865318338515394591

theorem tailTrace_28433 : CollatzResearch.WordTrace tailWord_28433 prefixEnd_28433 4325865318338515394591 := by
  unfold tailWord_28433
  simp only [CollatzResearch.WordTrace]
  refine ⟨1037036705999571814905953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 691357803999714543270635 1037036705999571814905953)
  ·
    refine ⟨777777529499678861179465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1037036705999571814905953 777777529499678861179465)
    ·
      refine ⟨583333147124759145884599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 777777529499678861179465 583333147124759145884599)
      ·
        refine ⟨874999720687138718826899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583333147124759145884599 874999720687138718826899)
        ·
          refine ⟨1312499581030708078240349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 874999720687138718826899 1312499581030708078240349)
          ·
            refine ⟨492187342886515529340131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1312499581030708078240349 492187342886515529340131)
            ·
              refine ⟨738281014329773294010197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492187342886515529340131 738281014329773294010197)
              ·
                refine ⟨4325865318338515394591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 738281014329773294010197 4325865318338515394591)
                ·
                  rfl

theorem cell20_28433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 9].length) (baseStart_28433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28433 prefixEnd_28433 := by exact prefixLift 28433
  have htrace : WordTrace (prefixWord ++ tailWord_28433) baseStart_28433 baseEnd_28433 := by
    simpa [prefixWord, tailWord_28433, baseEnd_28433] using wordTrace_append hprefix tailTrace_28433
  have hstable : (prefixWord ++ tailWord_28433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28433).length < 2 ^ (prefixWord ++ tailWord_28433).sum := by decide
  have hdescent : baseEnd_28433 < baseStart_28433 := by decide
  rcases family_descends (prefixWord ++ tailWord_28433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28450 : List Nat := [3, 3, 1, 1, 2, 1, 3, 6]
def baseStart_28450 : Nat := 118140960795 + 28450 * 2 ^ 59
def prefixEnd_28450 : Nat := 4983230072969 + 3 ^ 40 * 28450 * 2
def baseEnd_28450 : Nat := 4328451739413014205679

theorem tailTrace_28450 : CollatzResearch.WordTrace tailWord_28450 prefixEnd_28450 4328451739413014205679 := by
  unfold tailWord_28450
  simp only [CollatzResearch.WordTrace]
  refine ⟨259414186734495929568701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 691771164625322478849869 259414186734495929568701)
  ·
    refine ⟨97280320025435973588263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259414186734495929568701 97280320025435973588263)
    ·
      refine ⟨145920480038153960382395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97280320025435973588263 145920480038153960382395)
      ·
        refine ⟨218880720057230940573593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145920480038153960382395 218880720057230940573593)
        ·
          refine ⟨164160540042923205430195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218880720057230940573593 164160540042923205430195)
          ·
            refine ⟨246240810064384808145293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164160540042923205430195 246240810064384808145293)
            ·
              refine ⟨92340303774144303054485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246240810064384808145293 92340303774144303054485)
              ·
                refine ⟨4328451739413014205679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92340303774144303054485 4328451739413014205679)
                ·
                  rfl

theorem cell20_28450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_28450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28450 prefixEnd_28450 := by exact prefixLift 28450
  have htrace : WordTrace (prefixWord ++ tailWord_28450) baseStart_28450 baseEnd_28450 := by
    simpa [prefixWord, tailWord_28450, baseEnd_28450] using wordTrace_append hprefix tailTrace_28450
  have hstable : (prefixWord ++ tailWord_28450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28450).length < 2 ^ (prefixWord ++ tailWord_28450).sum := by decide
  have hdescent : baseEnd_28450 < baseStart_28450 := by decide
  rcases family_descends (prefixWord ++ tailWord_28450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28460 : List Nat := [2, 2, 1, 1, 1, 5, 3, 3, 2]
def baseStart_28460 : Nat := 118140960795 + 28460 * 2 ^ 59
def prefixEnd_28460 : Nat := 4983230072969 + 3 ^ 40 * 28460 * 2
def baseEnd_28460 : Nat := 12989919490723452283663

theorem tailTrace_28460 : CollatzResearch.WordTrace tailWord_28460 prefixEnd_28460 12989919490723452283663 := by
  unfold tailWord_28460
  simp only [CollatzResearch.WordTrace]
  refine ⟨519010738450877713069417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 692014317934503617425889 519010738450877713069417)
  ·
    refine ⟨389258053838158284802063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 519010738450877713069417 389258053838158284802063)
    ·
      refine ⟨583887080757237427203095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389258053838158284802063 583887080757237427203095)
      ·
        refine ⟨875830621135856140804643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583887080757237427203095 875830621135856140804643)
        ·
          refine ⟨1313745931703784211206965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 875830621135856140804643 1313745931703784211206965)
          ·
            refine ⟨123163681097229769800653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1313745931703784211206965 123163681097229769800653)
            ·
              refine ⟨46186380411461163675245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123163681097229769800653 46186380411461163675245)
              ·
                refine ⟨17319892654297936378217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46186380411461163675245 17319892654297936378217)
                ·
                  refine ⟨12989919490723452283663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17319892654297936378217 12989919490723452283663)
                  ·
                    rfl

theorem cell20_28460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 2].length) (baseStart_28460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28460 prefixEnd_28460 := by exact prefixLift 28460
  have htrace : WordTrace (prefixWord ++ tailWord_28460) baseStart_28460 baseEnd_28460 := by
    simpa [prefixWord, tailWord_28460, baseEnd_28460] using wordTrace_append hprefix tailTrace_28460
  have hstable : (prefixWord ++ tailWord_28460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28460).length < 2 ^ (prefixWord ++ tailWord_28460).sum := by decide
  have hdescent : baseEnd_28460 < baseStart_28460 := by decide
  rcases family_descends (prefixWord ++ tailWord_28460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28467 : List Nat := [1, 1, 1, 2, 8, 1, 6]
def baseStart_28467 : Nat := 118140960795 + 28467 * 2 ^ 59
def prefixEnd_28467 : Nat := 4983230072969 + 3 ^ 40 * 28467 * 2
def baseEnd_28467 : Nat := 1443679386829171005589

theorem tailTrace_28467 : CollatzResearch.WordTrace tailWord_28467 prefixEnd_28467 1443679386829171005589 := by
  unfold tailWord_28467
  simp only [CollatzResearch.WordTrace]
  refine ⟨1038276787876395621643655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 692184525250930414429103 1038276787876395621643655)
  ·
    refine ⟨1557415181814593432465483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1038276787876395621643655 1557415181814593432465483)
    ·
      refine ⟨2336122772721890148698225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1557415181814593432465483 2336122772721890148698225)
      ·
        refine ⟨1752092079541417611523669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2336122772721890148698225 1752092079541417611523669)
        ·
          refine ⟨20532329057125987635043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 1752092079541417611523669 20532329057125987635043)
          ·
            refine ⟨30798493585688981452565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20532329057125987635043 30798493585688981452565)
            ·
              refine ⟨1443679386829171005589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30798493585688981452565 1443679386829171005589)
              ·
                rfl

theorem cell20_28467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 6].length) (baseStart_28467 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28467 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28467 prefixEnd_28467 := by exact prefixLift 28467
  have htrace : WordTrace (prefixWord ++ tailWord_28467) baseStart_28467 baseEnd_28467 := by
    simpa [prefixWord, tailWord_28467, baseEnd_28467] using wordTrace_append hprefix tailTrace_28467
  have hstable : (prefixWord ++ tailWord_28467).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28467).length < 2 ^ (prefixWord ++ tailWord_28467).sum := by decide
  have hdescent : baseEnd_28467 < baseStart_28467 := by decide
  rcases family_descends (prefixWord ++ tailWord_28467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28488 : List Nat := [2, 1, 3, 1, 1, 5, 2, 5]
def baseStart_28488 : Nat := 118140960795 + 28488 * 2 ^ 59
def prefixEnd_28488 : Nat := 4983230072969 + 3 ^ 40 * 28488 * 2
def baseEnd_28488 : Nat := 4334233151226599783405

theorem tailTrace_28488 : CollatzResearch.WordTrace tailWord_28488 prefixEnd_28488 4334233151226599783405 := by
  unfold tailWord_28488
  simp only [CollatzResearch.WordTrace]
  refine ⟨519521360400158104079059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 692695147200210805438745 519521360400158104079059)
  ·
    refine ⟨779282040600237156118589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 519521360400158104079059 779282040600237156118589)
    ·
      refine ⟨292230765225088933544471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 779282040600237156118589 292230765225088933544471)
      ·
        refine ⟨438346147837633400316707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292230765225088933544471 438346147837633400316707)
        ·
          refine ⟨657519221756450100475061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438346147837633400316707 657519221756450100475061)
          ·
            refine ⟨61642427039667196919537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 657519221756450100475061 61642427039667196919537)
            ·
              refine ⟨46231820279750397689653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61642427039667196919537 46231820279750397689653)
              ·
                refine ⟨4334233151226599783405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46231820279750397689653 4334233151226599783405)
                ·
                  rfl

theorem cell20_28488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_28488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28488 prefixEnd_28488 := by exact prefixLift 28488
  have htrace : WordTrace (prefixWord ++ tailWord_28488) baseStart_28488 baseEnd_28488 := by
    simpa [prefixWord, tailWord_28488, baseEnd_28488] using wordTrace_append hprefix tailTrace_28488
  have hstable : (prefixWord ++ tailWord_28488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28488).length < 2 ^ (prefixWord ++ tailWord_28488).sum := by decide
  have hdescent : baseEnd_28488 < baseStart_28488 := by decide
  rcases family_descends (prefixWord ++ tailWord_28488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28526 : List Nat := [4, 1, 2, 3, 1, 9]
def baseStart_28526 : Nat := 118140960795 + 28526 * 2 ^ 59
def prefixEnd_28526 : Nat := 4983230072969 + 3 ^ 40 * 28526 * 2
def baseEnd_28526 : Nat := 482223840337798373459

theorem tailTrace_28526 : CollatzResearch.WordTrace tailWord_28526 prefixEnd_28526 482223840337798373459 := by
  unfold tailWord_28526
  simp only [CollatzResearch.WordTrace]
  refine ⟨130053586832831087255179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 693619129775099132027621 130053586832831087255179)
  ·
    refine ⟨195080380249246630882769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130053586832831087255179 195080380249246630882769)
    ·
      refine ⟨146310285186934973162077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195080380249246630882769 146310285186934973162077)
      ·
        refine ⟨54866356945100614935779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146310285186934973162077 54866356945100614935779)
        ·
          refine ⟨82299535417650922403669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54866356945100614935779 82299535417650922403669)
          ·
            refine ⟨482223840337798373459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 82299535417650922403669 482223840337798373459)
            ·
              rfl

theorem cell20_28526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 9].length) (baseStart_28526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28526 prefixEnd_28526 := by exact prefixLift 28526
  have htrace : WordTrace (prefixWord ++ tailWord_28526) baseStart_28526 baseEnd_28526 := by
    simpa [prefixWord, tailWord_28526, baseEnd_28526] using wordTrace_append hprefix tailTrace_28526
  have hstable : (prefixWord ++ tailWord_28526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28526).length < 2 ^ (prefixWord ++ tailWord_28526).sum := by decide
  have hdescent : baseEnd_28526 < baseStart_28526 := by decide
  rcases family_descends (prefixWord ++ tailWord_28526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28595 : List Nat := [1, 1, 1, 2, 3, 1, 3, 6, 2]
def baseStart_28595 : Nat := 118140960795 + 28595 * 2 ^ 59
def prefixEnd_28595 : Nat := 4983230072969 + 3 ^ 40 * 28595 * 2
def baseEnd_28595 : Nat := 13051537169262982783111

theorem tailTrace_28595 : CollatzResearch.WordTrace tailWord_28595 prefixEnd_28595 13051537169262982783111 := by
  unfold tailWord_28595
  simp only [CollatzResearch.WordTrace]
  refine ⟨1042945331412673482303239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 695296887608448988202159 1042945331412673482303239)
  ·
    refine ⟨1564417997119010223454859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1042945331412673482303239 1564417997119010223454859)
    ·
      refine ⟨2346626995678515335182289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1564417997119010223454859 2346626995678515335182289)
      ·
        refine ⟨1759970246758886501386717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2346626995678515335182289 1759970246758886501386717)
        ·
          refine ⟨659988842534582438020019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1759970246758886501386717 659988842534582438020019)
          ·
            refine ⟨989983263801873657030029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659988842534582438020019 989983263801873657030029)
            ·
              refine ⟨371243723925702621386261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 989983263801873657030029 371243723925702621386261)
              ·
                refine ⟨17402049559017310377481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 371243723925702621386261 17402049559017310377481)
                ·
                  refine ⟨13051537169262982783111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17402049559017310377481 13051537169262982783111)
                  ·
                    rfl

theorem cell20_28595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 2].length) (baseStart_28595 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28595 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28595 prefixEnd_28595 := by exact prefixLift 28595
  have htrace : WordTrace (prefixWord ++ tailWord_28595) baseStart_28595 baseEnd_28595 := by
    simpa [prefixWord, tailWord_28595, baseEnd_28595] using wordTrace_append hprefix tailTrace_28595
  have hstable : (prefixWord ++ tailWord_28595).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28595).length < 2 ^ (prefixWord ++ tailWord_28595).sum := by decide
  have hdescent : baseEnd_28595 < baseStart_28595 := by decide
  rcases family_descends (prefixWord ++ tailWord_28595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28605 : List Nat := [1, 4, 1, 2, 3, 2, 3, 1, 3]
def baseStart_28605 : Nat := 118140960795 + 28605 * 2 ^ 59
def prefixEnd_28605 : Nat := 4983230072969 + 3 ^ 40 * 28605 * 2
def baseEnd_28605 : Nat := 13056101441747392449737

theorem tailTrace_28605 : CollatzResearch.WordTrace tailWord_28605 prefixEnd_28605 13056101441747392449737 := by
  unfold tailWord_28605
  simp only [CollatzResearch.WordTrace]
  refine ⟨1043310061376445190167269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 695540040917630126778179 1043310061376445190167269)
  ·
    refine ⟨195620636508083473156363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1043310061376445190167269 195620636508083473156363)
    ·
      refine ⟨293430954762125209734545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195620636508083473156363 293430954762125209734545)
      ·
        refine ⟨220073216071593907300909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293430954762125209734545 220073216071593907300909)
        ·
          refine ⟨82527456026847715237841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220073216071593907300909 82527456026847715237841)
          ·
            refine ⟨61895592020135786428381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82527456026847715237841 61895592020135786428381)
            ·
              refine ⟨23210847007550919910643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61895592020135786428381 23210847007550919910643)
              ·
                refine ⟨34816270511326379865965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23210847007550919910643 34816270511326379865965)
                ·
                  refine ⟨13056101441747392449737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34816270511326379865965 13056101441747392449737)
                  ·
                    rfl

theorem cell20_28605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_28605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28605 prefixEnd_28605 := by exact prefixLift 28605
  have htrace : WordTrace (prefixWord ++ tailWord_28605) baseStart_28605 baseEnd_28605 := by
    simpa [prefixWord, tailWord_28605, baseEnd_28605] using wordTrace_append hprefix tailTrace_28605
  have hstable : (prefixWord ++ tailWord_28605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28605).length < 2 ^ (prefixWord ++ tailWord_28605).sum := by decide
  have hdescent : baseEnd_28605 < baseStart_28605 := by decide
  rcases family_descends (prefixWord ++ tailWord_28605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28623 : List Nat := [1, 1, 2, 1, 1, 5, 3, 6]
def baseStart_28623 : Nat := 118140960795 + 28623 * 2 ^ 59
def prefixEnd_28623 : Nat := 4983230072969 + 3 ^ 40 * 28623 * 2
def baseEnd_28623 : Nat := 4354772377406443283221

theorem tailTrace_28623 : CollatzResearch.WordTrace tailWord_28623 prefixEnd_28623 4354772377406443283221 := by
  unfold tailWord_28623
  simp only [CollatzResearch.WordTrace]
  refine ⟨1043966575311234264322523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 695977716874156176215015 1043966575311234264322523)
  ·
    refine ⟨1565949862966851396483785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1043966575311234264322523 1565949862966851396483785)
    ·
      refine ⟨1174462397225138547362839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1565949862966851396483785 1174462397225138547362839)
      ·
        refine ⟨1761693595837707821044259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1174462397225138547362839 1761693595837707821044259)
        ·
          refine ⟨2642540393756561731566389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1761693595837707821044259 2642540393756561731566389)
          ·
            refine ⟨247738161914677662334349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2642540393756561731566389 247738161914677662334349)
            ·
              refine ⟨92901810718004123375381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247738161914677662334349 92901810718004123375381)
              ·
                refine ⟨4354772377406443283221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92901810718004123375381 4354772377406443283221)
                ·
                  rfl

theorem cell20_28623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 6].length) (baseStart_28623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28623 prefixEnd_28623 := by exact prefixLift 28623
  have htrace : WordTrace (prefixWord ++ tailWord_28623) baseStart_28623 baseEnd_28623 := by
    simpa [prefixWord, tailWord_28623, baseEnd_28623] using wordTrace_append hprefix tailTrace_28623
  have hstable : (prefixWord ++ tailWord_28623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28623).length < 2 ^ (prefixWord ++ tailWord_28623).sum := by decide
  have hdescent : baseEnd_28623 < baseStart_28623 := by decide
  rcases family_descends (prefixWord ++ tailWord_28623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28629 : List Nat := [1, 3, 2, 3, 2, 3, 1, 3, 2]
def baseStart_28629 : Nat := 118140960795 + 28629 * 2 ^ 59
def prefixEnd_28629 : Nat := 4983230072969 + 3 ^ 40 * 28629 * 2
def baseEnd_28629 : Nat := 13067055695709975649639

theorem tailTrace_28629 : CollatzResearch.WordTrace tailWord_28629 prefixEnd_28629 13067055695709975649639 := by
  unfold tailWord_28629
  simp only [CollatzResearch.WordTrace]
  refine ⟨1044185413289497289040941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 696123608859664859360627 1044185413289497289040941)
  ·
    refine ⟨391569529983561483390353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1044185413289497289040941 391569529983561483390353)
    ·
      refine ⟨293677147487671112542765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391569529983561483390353 293677147487671112542765)
      ·
        refine ⟨110128930307876667203537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293677147487671112542765 110128930307876667203537)
        ·
          refine ⟨82596697730907500402653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110128930307876667203537 82596697730907500402653)
          ·
            refine ⟨30973761649090312650995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82596697730907500402653 30973761649090312650995)
            ·
              refine ⟨46460642473635468976493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30973761649090312650995 46460642473635468976493)
              ·
                refine ⟨17422740927613300866185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46460642473635468976493 17422740927613300866185)
                ·
                  refine ⟨13067055695709975649639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17422740927613300866185 13067055695709975649639)
                  ·
                    rfl

theorem cell20_28629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 2].length) (baseStart_28629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28629 prefixEnd_28629 := by exact prefixLift 28629
  have htrace : WordTrace (prefixWord ++ tailWord_28629) baseStart_28629 baseEnd_28629 := by
    simpa [prefixWord, tailWord_28629, baseEnd_28629] using wordTrace_append hprefix tailTrace_28629
  have hstable : (prefixWord ++ tailWord_28629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28629).length < 2 ^ (prefixWord ++ tailWord_28629).sum := by decide
  have hdescent : baseEnd_28629 < baseStart_28629 := by decide
  rcases family_descends (prefixWord ++ tailWord_28629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28664 : List Nat := [2, 1, 2, 1, 1, 3, 6, 1, 3]
def baseStart_28664 : Nat := 118140960795 + 28664 * 2 ^ 59
def prefixEnd_28664 : Nat := 4983230072969 + 3 ^ 40 * 28664 * 2
def baseEnd_28664 : Nat := 13083030649405409482829

theorem tailTrace_28664 : CollatzResearch.WordTrace tailWord_28664 prefixEnd_28664 13083030649405409482829 := by
  unfold tailWord_28664
  simp only [CollatzResearch.WordTrace]
  refine ⟨522730984081349133282523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 696974645441798844376697 522730984081349133282523)
  ·
    refine ⟨784096476122023699923785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 522730984081349133282523 784096476122023699923785)
    ·
      refine ⟨588072357091517774942839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 784096476122023699923785 588072357091517774942839)
      ·
        refine ⟨882108535637276662414259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588072357091517774942839 882108535637276662414259)
        ·
          refine ⟨1323162803455914993621389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882108535637276662414259 1323162803455914993621389)
          ·
            refine ⟨496186051295968122608021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1323162803455914993621389 496186051295968122608021)
            ·
              refine ⟨23258721154498505747251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 496186051295968122608021 23258721154498505747251)
              ·
                refine ⟨34888081731747758620877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23258721154498505747251 34888081731747758620877)
                ·
                  refine ⟨13083030649405409482829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34888081731747758620877 13083030649405409482829)
                  ·
                    rfl

theorem cell20_28664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 3].length) (baseStart_28664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28664 prefixEnd_28664 := by exact prefixLift 28664
  have htrace : WordTrace (prefixWord ++ tailWord_28664) baseStart_28664 baseEnd_28664 := by
    simpa [prefixWord, tailWord_28664, baseEnd_28664] using wordTrace_append hprefix tailTrace_28664
  have hstable : (prefixWord ++ tailWord_28664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28664).length < 2 ^ (prefixWord ++ tailWord_28664).sum := by decide
  have hdescent : baseEnd_28664 < baseStart_28664 := by decide
  rcases family_descends (prefixWord ++ tailWord_28664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28712 : List Nat := [2, 1, 5, 3, 1, 2, 1, 5]
def baseStart_28712 : Nat := 118140960795 + 28712 * 2 ^ 59
def prefixEnd_28712 : Nat := 4983230072969 + 3 ^ 40 * 28712 * 2
def baseEnd_28712 : Nat := 4368313052443525294211

theorem tailTrace_28712 : CollatzResearch.WordTrace tailWord_28712 prefixEnd_28712 4368313052443525294211 := by
  unfold tailWord_28712
  simp only [CollatzResearch.WordTrace]
  refine ⟨523606335994401232156195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 698141781325868309541593 523606335994401232156195)
  ·
    refine ⟨785409503991601848234293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 523606335994401232156195 785409503991601848234293)
    ·
      refine ⟨73632140999212673271965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 785409503991601848234293 73632140999212673271965)
      ·
        refine ⟨27612052874704752476987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73632140999212673271965 27612052874704752476987)
        ·
          refine ⟨41418079312057128715481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27612052874704752476987 41418079312057128715481)
          ·
            refine ⟨31063559484042846536611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41418079312057128715481 31063559484042846536611)
            ·
              refine ⟨46595339226064269804917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31063559484042846536611 46595339226064269804917)
              ·
                refine ⟨4368313052443525294211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46595339226064269804917 4368313052443525294211)
                ·
                  rfl

theorem cell20_28712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 5].length) (baseStart_28712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28712 prefixEnd_28712 := by exact prefixLift 28712
  have htrace : WordTrace (prefixWord ++ tailWord_28712) baseStart_28712 baseEnd_28712 := by
    simpa [prefixWord, tailWord_28712, baseEnd_28712] using wordTrace_append hprefix tailTrace_28712
  have hstable : (prefixWord ++ tailWord_28712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28712).length < 2 ^ (prefixWord ++ tailWord_28712).sum := by decide
  have hdescent : baseEnd_28712 < baseStart_28712 := by decide
  rcases family_descends (prefixWord ++ tailWord_28712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28723 : List Nat := [1, 1, 1, 2, 4, 1, 4, 3, 3]
def baseStart_28723 : Nat := 118140960795 + 28723 * 2 ^ 59
def prefixEnd_28723 : Nat := 4983230072969 + 3 ^ 40 * 28723 * 2
def baseEnd_28723 : Nat := 13109959857063426515921

theorem tailTrace_28723 : CollatzResearch.WordTrace tailWord_28723 prefixEnd_28723 13109959857063426515921 := by
  unfold tailWord_28723
  simp only [CollatzResearch.WordTrace]
  refine ⟨1047613874948951342962823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 698409249965967561975215 1047613874948951342962823)
  ·
    refine ⟨1571420812423427014444235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1047613874948951342962823 1571420812423427014444235)
    ·
      refine ⟨2357131218635140521666353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1571420812423427014444235 2357131218635140521666353)
      ·
        refine ⟨1767848413976355391249765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2357131218635140521666353 1767848413976355391249765)
        ·
          refine ⟨331471577620566635859331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1767848413976355391249765 331471577620566635859331)
          ·
            refine ⟨497207366430849953788997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331471577620566635859331 497207366430849953788997)
            ·
              refine ⟨93226381205784366335437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 497207366430849953788997 93226381205784366335437)
              ·
                refine ⟨34959892952169137375789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93226381205784366335437 34959892952169137375789)
                ·
                  refine ⟨13109959857063426515921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34959892952169137375789 13109959857063426515921)
                  ·
                    rfl

theorem cell20_28723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 3].length) (baseStart_28723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28723 prefixEnd_28723 := by exact prefixLift 28723
  have htrace : WordTrace (prefixWord ++ tailWord_28723) baseStart_28723 baseEnd_28723 := by
    simpa [prefixWord, tailWord_28723, baseEnd_28723] using wordTrace_append hprefix tailTrace_28723
  have hstable : (prefixWord ++ tailWord_28723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28723).length < 2 ^ (prefixWord ++ tailWord_28723).sum := by decide
  have hdescent : baseEnd_28723 < baseStart_28723 := by decide
  rcases family_descends (prefixWord ++ tailWord_28723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28754 : List Nat := [3, 2, 2, 1, 4, 1, 7]
def baseStart_28754 : Nat := 118140960795 + 28754 * 2 ^ 59
def prefixEnd_28754 : Nat := 4983230072969 + 3 ^ 40 * 28754 * 2
def baseEnd_28754 : Nat := 1458234344640566275829

theorem tailTrace_28754 : CollatzResearch.WordTrace tailWord_28754 prefixEnd_28754 1458234344640566275829 := by
  unfold tailWord_28754
  simp only [CollatzResearch.WordTrace]
  refine ⟨262186134459160909335329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 699163025224429091560877 262186134459160909335329)
  ·
    refine ⟨196639600844370682001497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262186134459160909335329 196639600844370682001497)
    ·
      refine ⟨147479700633278011501123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196639600844370682001497 147479700633278011501123)
      ·
        refine ⟨221219550949917017251685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147479700633278011501123 221219550949917017251685)
        ·
          refine ⟨41478665803109440734691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221219550949917017251685 41478665803109440734691)
          ·
            refine ⟨62217998704664161102037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41478665803109440734691 62217998704664161102037)
            ·
              refine ⟨1458234344640566275829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 62217998704664161102037 1458234344640566275829)
              ·
                rfl

theorem cell20_28754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 7].length) (baseStart_28754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28754 prefixEnd_28754 := by exact prefixLift 28754
  have htrace : WordTrace (prefixWord ++ tailWord_28754) baseStart_28754 baseEnd_28754 := by
    simpa [prefixWord, tailWord_28754, baseEnd_28754] using wordTrace_append hprefix tailTrace_28754
  have hstable : (prefixWord ++ tailWord_28754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28754).length < 2 ^ (prefixWord ++ tailWord_28754).sum := by decide
  have hdescent : baseEnd_28754 < baseStart_28754 := by decide
  rcases family_descends (prefixWord ++ tailWord_28754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28764 : List Nat := [2, 2, 4, 1, 1, 2, 2, 4, 2]
def baseStart_28764 : Nat := 118140960795 + 28764 * 2 ^ 59
def prefixEnd_28764 : Nat := 4983230072969 + 3 ^ 40 * 28764 * 2
def baseEnd_28764 : Nat := 13128673374249506149087

theorem tailTrace_28764 : CollatzResearch.WordTrace tailWord_28764 prefixEnd_28764 13128673374249506149087 := by
  unfold tailWord_28764
  simp only [CollatzResearch.WordTrace]
  refine ⟨524554633900207672602673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 699406178533610230136897 524554633900207672602673)
  ·
    refine ⟨393415975425155754452005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 524554633900207672602673 393415975425155754452005)
    ·
      refine ⟨73765495392216703959751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 393415975425155754452005 73765495392216703959751)
      ·
        refine ⟨110648243088325055939627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73765495392216703959751 110648243088325055939627)
        ·
          refine ⟨165972364632487583909441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110648243088325055939627 165972364632487583909441)
          ·
            refine ⟨124479273474365687932081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165972364632487583909441 124479273474365687932081)
            ·
              refine ⟨93359455105774265949061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124479273474365687932081 93359455105774265949061)
              ·
                refine ⟨17504897832332674865449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93359455105774265949061 17504897832332674865449)
                ·
                  refine ⟨13128673374249506149087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17504897832332674865449 13128673374249506149087)
                  ·
                    rfl

theorem cell20_28764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 2].length) (baseStart_28764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28764 prefixEnd_28764 := by exact prefixLift 28764
  have htrace : WordTrace (prefixWord ++ tailWord_28764) baseStart_28764 baseEnd_28764 := by
    simpa [prefixWord, tailWord_28764, baseEnd_28764] using wordTrace_append hprefix tailTrace_28764
  have hstable : (prefixWord ++ tailWord_28764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28764).length < 2 ^ (prefixWord ++ tailWord_28764).sum := by decide
  have hdescent : baseEnd_28764 < baseStart_28764 := by decide
  rcases family_descends (prefixWord ++ tailWord_28764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28768 : List Nat := [2, 1, 1, 3, 2, 3, 1, 3, 4]
def baseStart_28768 : Nat := 118140960795 + 28768 * 2 ^ 59
def prefixEnd_28768 : Nat := 4983230072969 + 3 ^ 40 * 28768 * 2
def baseEnd_28768 : Nat := 13130499083243270015737

theorem tailTrace_28768 : CollatzResearch.WordTrace tailWord_28768 prefixEnd_28768 13130499083243270015737 := by
  unfold tailWord_28768
  simp only [CollatzResearch.WordTrace]
  refine ⟨524627579892962014175479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 699503439857282685567305 524627579892962014175479)
  ·
    refine ⟨786941369839443021263219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 524627579892962014175479 786941369839443021263219)
    ·
      refine ⟨1180412054759164531894829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 786941369839443021263219 1180412054759164531894829)
      ·
        refine ⟨442654520534686699460561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1180412054759164531894829 442654520534686699460561)
        ·
          refine ⟨331990890401015024595421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442654520534686699460561 331990890401015024595421)
          ·
            refine ⟨124496583900380634223283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 331990890401015024595421 124496583900380634223283)
            ·
              refine ⟨186744875850570951334925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124496583900380634223283 186744875850570951334925)
              ·
                refine ⟨70029328443964106750597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186744875850570951334925 70029328443964106750597)
                ·
                  refine ⟨13130499083243270015737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70029328443964106750597 13130499083243270015737)
                  ·
                    rfl

theorem cell20_28768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_28768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28768 prefixEnd_28768 := by exact prefixLift 28768
  have htrace : WordTrace (prefixWord ++ tailWord_28768) baseStart_28768 baseEnd_28768 := by
    simpa [prefixWord, tailWord_28768, baseEnd_28768] using wordTrace_append hprefix tailTrace_28768
  have hstable : (prefixWord ++ tailWord_28768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28768).length < 2 ^ (prefixWord ++ tailWord_28768).sum := by decide
  have hdescent : baseEnd_28768 < baseStart_28768 := by decide
  rcases family_descends (prefixWord ++ tailWord_28768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28775 : List Nat := [1, 1, 5, 1, 1, 2, 2, 7]
def baseStart_28775 : Nat := 118140960795 + 28775 * 2 ^ 59
def prefixEnd_28775 : Nat := 4983230072969 + 3 ^ 40 * 28775 * 2
def baseEnd_28775 : Nat := 4377898024660785594125

theorem tailTrace_28775 : CollatzResearch.WordTrace tailWord_28775 prefixEnd_28775 4377898024660785594125 := by
  unfold tailWord_28775
  simp only [CollatzResearch.WordTrace]
  refine ⟨1049510470760564223855779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 699673647173709482570519 1049510470760564223855779)
  ·
    refine ⟨1574265706140846335783669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1049510470760564223855779 1574265706140846335783669)
    ·
      refine ⟨147587409950704343979719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1574265706140846335783669 147587409950704343979719)
      ·
        refine ⟨221381114926056515969579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147587409950704343979719 221381114926056515969579)
        ·
          refine ⟨332071672389084773954369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221381114926056515969579 332071672389084773954369)
          ·
            refine ⟨249053754291813580465777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332071672389084773954369 249053754291813580465777)
            ·
              refine ⟨186790315718860185349333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249053754291813580465777 186790315718860185349333)
              ·
                refine ⟨4377898024660785594125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 186790315718860185349333 4377898024660785594125)
                ·
                  rfl

theorem cell20_28775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 7].length) (baseStart_28775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28775 prefixEnd_28775 := by exact prefixLift 28775
  have htrace : WordTrace (prefixWord ++ tailWord_28775) baseStart_28775 baseEnd_28775 := by
    simpa [prefixWord, tailWord_28775, baseEnd_28775] using wordTrace_append hprefix tailTrace_28775
  have hstable : (prefixWord ++ tailWord_28775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28775).length < 2 ^ (prefixWord ++ tailWord_28775).sum := by decide
  have hdescent : baseEnd_28775 < baseStart_28775 := by decide
  rcases family_descends (prefixWord ++ tailWord_28775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28822 : List Nat := [5, 3, 2, 1, 1, 1, 2, 5]
def baseStart_28822 : Nat := 118140960795 + 28822 * 2 ^ 59
def prefixEnd_28822 : Nat := 4983230072969 + 3 ^ 40 * 28822 * 2
def baseEnd_28822 : Nat := 4385048718219694071839

theorem tailTrace_28822 : CollatzResearch.WordTrace tailWord_28822 prefixEnd_28822 4385048718219694071839 := by
  unfold tailWord_28822
  simp only [CollatzResearch.WordTrace]
  refine ⟨65701543849393203176045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 700816467726860833877813 65701543849393203176045)
  ·
    refine ⟨24638078943522451191017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65701543849393203176045 24638078943522451191017)
    ·
      refine ⟨18478559207641838393263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24638078943522451191017 18478559207641838393263)
      ·
        refine ⟨27717838811462757589895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18478559207641838393263 27717838811462757589895)
        ·
          refine ⟨41576758217194136384843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27717838811462757589895 41576758217194136384843)
          ·
            refine ⟨62365137325791204577265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41576758217194136384843 62365137325791204577265)
            ·
              refine ⟨46773852994343403432949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62365137325791204577265 46773852994343403432949)
              ·
                refine ⟨4385048718219694071839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46773852994343403432949 4385048718219694071839)
                ·
                  rfl

theorem cell20_28822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_28822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28822 prefixEnd_28822 := by exact prefixLift 28822
  have htrace : WordTrace (prefixWord ++ tailWord_28822) baseStart_28822 baseEnd_28822 := by
    simpa [prefixWord, tailWord_28822, baseEnd_28822] using wordTrace_append hprefix tailTrace_28822
  have hstable : (prefixWord ++ tailWord_28822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28822).length < 2 ^ (prefixWord ++ tailWord_28822).sum := by decide
  have hdescent : baseEnd_28822 < baseStart_28822 := by decide
  rcases family_descends (prefixWord ++ tailWord_28822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28827 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 8]
def baseStart_28827 : Nat := 118140960795 + 28827 * 2 ^ 59
def prefixEnd_28827 : Nat := 4983230072969 + 3 ^ 40 * 28827 * 2
def baseEnd_28827 : Nat := 13157428290901287048829

theorem tailTrace_28827 : CollatzResearch.WordTrace tailWord_28827 prefixEnd_28827 13157428290901287048829 := by
  unfold tailWord_28827
  simp only [CollatzResearch.WordTrace]
  refine ⟨1051407066572177104748735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 700938044381451403165823 1051407066572177104748735)
  ·
    refine ⟨1577110599858265657123103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1051407066572177104748735 1577110599858265657123103)
    ·
      refine ⟨2365665899787398485684655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1577110599858265657123103 2365665899787398485684655)
      ·
        refine ⟨3548498849681097728526983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2365665899787398485684655 3548498849681097728526983)
        ·
          refine ⟨5322748274521646592790475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3548498849681097728526983 5322748274521646592790475)
          ·
            refine ⟨7984122411782469889185713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5322748274521646592790475 7984122411782469889185713)
            ·
              refine ⟨5988091808836852416889285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7984122411782469889185713 5988091808836852416889285)
              ·
                refine ⟨1122767214156909828166741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5988091808836852416889285 1122767214156909828166741)
                ·
                  refine ⟨13157428290901287048829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1122767214156909828166741 13157428290901287048829)
                  ·
                    rfl

theorem cell20_28827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_28827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28827 prefixEnd_28827 := by exact prefixLift 28827
  have htrace : WordTrace (prefixWord ++ tailWord_28827) baseStart_28827 baseEnd_28827 := by
    simpa [prefixWord, tailWord_28827, baseEnd_28827] using wordTrace_append hprefix tailTrace_28827
  have hstable : (prefixWord ++ tailWord_28827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28827).length < 2 ^ (prefixWord ++ tailWord_28827).sum := by decide
  have hdescent : baseEnd_28827 < baseStart_28827 := by decide
  rcases family_descends (prefixWord ++ tailWord_28827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28833 : List Nat := [1, 2, 3, 3, 1, 4, 2, 1, 3]
def baseStart_28833 : Nat := 118140960795 + 28833 * 2 ^ 59
def prefixEnd_28833 : Nat := 4983230072969 + 3 ^ 40 * 28833 * 2
def baseEnd_28833 : Nat := 13160166854391932848805

theorem tailTrace_28833 : CollatzResearch.WordTrace tailWord_28833 prefixEnd_28833 13160166854391932848805 := by
  unfold tailWord_28833
  simp only [CollatzResearch.WordTrace]
  refine ⟨1051625904550440129467153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 701083936366960086311435 1051625904550440129467153)
  ·
    refine ⟨788719428412830097100365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1051625904550440129467153 788719428412830097100365)
    ·
      refine ⟨295769785654811286412637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 788719428412830097100365 295769785654811286412637)
      ·
        refine ⟨110913669620554232404739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295769785654811286412637 110913669620554232404739)
        ·
          refine ⟨166370504430831348607109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110913669620554232404739 166370504430831348607109)
          ·
            refine ⟨31194469580780877863833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166370504430831348607109 31194469580780877863833)
            ·
              refine ⟨23395852185585658397875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31194469580780877863833 23395852185585658397875)
              ·
                refine ⟨35093778278378487596813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23395852185585658397875 35093778278378487596813)
                ·
                  refine ⟨13160166854391932848805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35093778278378487596813 13160166854391932848805)
                  ·
                    rfl

theorem cell20_28833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 3].length) (baseStart_28833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28833 prefixEnd_28833 := by exact prefixLift 28833
  have htrace : WordTrace (prefixWord ++ tailWord_28833) baseStart_28833 baseEnd_28833 := by
    simpa [prefixWord, tailWord_28833, baseEnd_28833] using wordTrace_append hprefix tailTrace_28833
  have hstable : (prefixWord ++ tailWord_28833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28833).length < 2 ^ (prefixWord ++ tailWord_28833).sum := by decide
  have hdescent : baseEnd_28833 < baseStart_28833 := by decide
  rcases family_descends (prefixWord ++ tailWord_28833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28837 : List Nat := [1, 3, 1, 2, 1, 3, 3, 3, 3]
def baseStart_28837 : Nat := 118140960795 + 28837 * 2 ^ 59
def prefixEnd_28837 : Nat := 4983230072969 + 3 ^ 40 * 28837 * 2
def baseEnd_28837 : Nat := 13161992563385696715455

theorem tailTrace_28837 : CollatzResearch.WordTrace tailWord_28837 prefixEnd_28837 13161992563385696715455 := by
  unfold tailWord_28837
  simp only [CollatzResearch.WordTrace]
  refine ⟨1051771796535948812612765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 701181197690632541741843 1051771796535948812612765)
  ·
    refine ⟨394414423700980804729787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1051771796535948812612765 394414423700980804729787)
    ·
      refine ⟨591621635551471207094681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394414423700980804729787 591621635551471207094681)
      ·
        refine ⟨443716226663603405321011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591621635551471207094681 443716226663603405321011)
        ·
          refine ⟨665574339995405107981517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443716226663603405321011 665574339995405107981517)
          ·
            refine ⟨249590377498276915493069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 665574339995405107981517 249590377498276915493069)
            ·
              refine ⟨93596391561853843309901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249590377498276915493069 93596391561853843309901)
              ·
                refine ⟨35098646835695191241213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93596391561853843309901 35098646835695191241213)
                ·
                  refine ⟨13161992563385696715455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35098646835695191241213 13161992563385696715455)
                  ·
                    rfl

theorem cell20_28837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_28837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28837 prefixEnd_28837 := by exact prefixLift 28837
  have htrace : WordTrace (prefixWord ++ tailWord_28837) baseStart_28837 baseEnd_28837 := by
    simpa [prefixWord, tailWord_28837, baseEnd_28837] using wordTrace_append hprefix tailTrace_28837
  have hstable : (prefixWord ++ tailWord_28837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28837).length < 2 ^ (prefixWord ++ tailWord_28837).sum := by decide
  have hdescent : baseEnd_28837 < baseStart_28837 := by decide
  rcases family_descends (prefixWord ++ tailWord_28837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28858 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 7]
def baseStart_28858 : Nat := 118140960795 + 28858 * 2 ^ 59
def prefixEnd_28858 : Nat := 4983230072969 + 3 ^ 40 * 28858 * 2
def baseEnd_28858 : Nat := 13171577535602957015369

theorem tailTrace_28858 : CollatzResearch.WordTrace tailWord_28858 prefixEnd_28858 13171577535602957015369 := by
  unfold tailWord_28858
  simp only [CollatzResearch.WordTrace]
  refine ⟨263134432364967349781807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 701691819639912932751485 263134432364967349781807)
  ·
    refine ⟨394701648547451024672711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263134432364967349781807 394701648547451024672711)
    ·
      refine ⟨592052472821176537009067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394701648547451024672711 592052472821176537009067)
      ·
        refine ⟨888078709231764805513601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592052472821176537009067 888078709231764805513601)
        ·
          refine ⟨666059031923823604135201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 888078709231764805513601 666059031923823604135201)
          ·
            refine ⟨499544273942867703101401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 666059031923823604135201 499544273942867703101401)
            ·
              refine ⟨374658205457150777326051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499544273942867703101401 374658205457150777326051)
              ·
                refine ⟨561987308185726165989077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374658205457150777326051 561987308185726165989077)
                ·
                  refine ⟨13171577535602957015369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 561987308185726165989077 13171577535602957015369)
                  ·
                    rfl

theorem cell20_28858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_28858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28858 prefixEnd_28858 := by exact prefixLift 28858
  have htrace : WordTrace (prefixWord ++ tailWord_28858) baseStart_28858 baseEnd_28858 := by
    simpa [prefixWord, tailWord_28858, baseEnd_28858] using wordTrace_append hprefix tailTrace_28858
  have hstable : (prefixWord ++ tailWord_28858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28858).length < 2 ^ (prefixWord ++ tailWord_28858).sum := by decide
  have hdescent : baseEnd_28858 < baseStart_28858 := by decide
  rcases family_descends (prefixWord ++ tailWord_28858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28861 : List Nat := [1, 4, 1, 2, 1, 1, 1, 7, 2]
def baseStart_28861 : Nat := 118140960795 + 28861 * 2 ^ 59
def prefixEnd_28861 : Nat := 4983230072969 + 3 ^ 40 * 28861 * 2
def baseEnd_28861 : Nat := 13172946817348279915357

theorem tailTrace_28861 : CollatzResearch.WordTrace tailWord_28861 prefixEnd_28861 13172946817348279915357 := by
  unfold tailWord_28861
  simp only [CollatzResearch.WordTrace]
  refine ⟨1052647148449000911486437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 701764765632667274324291 1052647148449000911486437)
  ·
    refine ⟨197371340334187670903707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1052647148449000911486437 197371340334187670903707)
    ·
      refine ⟨296057010501281506355561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197371340334187670903707 296057010501281506355561)
      ·
        refine ⟨222042757875961129766671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296057010501281506355561 222042757875961129766671)
        ·
          refine ⟨333064136813941694650007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222042757875961129766671 333064136813941694650007)
          ·
            refine ⟨499596205220912541975011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333064136813941694650007 499596205220912541975011)
            ·
              refine ⟨749394307831368812962517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499596205220912541975011 749394307831368812962517)
              ·
                refine ⟨17563929089797706553809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 749394307831368812962517 17563929089797706553809)
                ·
                  refine ⟨13172946817348279915357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17563929089797706553809 13172946817348279915357)
                  ·
                    rfl

theorem cell20_28861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_28861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28861 prefixEnd_28861 := by exact prefixLift 28861
  have htrace : WordTrace (prefixWord ++ tailWord_28861) baseStart_28861 baseEnd_28861 := by
    simpa [prefixWord, tailWord_28861, baseEnd_28861] using wordTrace_append hprefix tailTrace_28861
  have hstable : (prefixWord ++ tailWord_28861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28861).length < 2 ^ (prefixWord ++ tailWord_28861).sum := by decide
  have hdescent : baseEnd_28861 < baseStart_28861 := by decide
  rcases family_descends (prefixWord ++ tailWord_28861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28875 : List Nat := [1, 1, 1, 1, 3, 2, 6, 2, 3]
def baseStart_28875 : Nat := 118140960795 + 28875 * 2 ^ 59
def prefixEnd_28875 : Nat := 4983230072969 + 3 ^ 40 * 28875 * 2
def baseEnd_28875 : Nat := 13179336798826453448633

theorem tailTrace_28875 : CollatzResearch.WordTrace tailWord_28875 prefixEnd_28875 13179336798826453448633 := by
  unfold tailWord_28875
  simp only [CollatzResearch.WordTrace]
  refine ⟨1053157770398281302496079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 702105180265520868330719 1053157770398281302496079)
  ·
    refine ⟨1579736655597421953744119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1053157770398281302496079 1579736655597421953744119)
    ·
      refine ⟨2369604983396132930616179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1579736655597421953744119 2369604983396132930616179)
      ·
        refine ⟨3554407475094199395924269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2369604983396132930616179 3554407475094199395924269)
        ·
          refine ⟨1332902803160324773471601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3554407475094199395924269 1332902803160324773471601)
          ·
            refine ⟨999677102370243580103701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1332902803160324773471601 999677102370243580103701)
            ·
              refine ⟨46859864173605167817361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 999677102370243580103701 46859864173605167817361)
              ·
                refine ⟨35144898130203875863021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46859864173605167817361 35144898130203875863021)
                ·
                  refine ⟨13179336798826453448633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35144898130203875863021 13179336798826453448633)
                  ·
                    rfl

theorem cell20_28875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 3].length) (baseStart_28875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28875 prefixEnd_28875 := by exact prefixLift 28875
  have htrace : WordTrace (prefixWord ++ tailWord_28875) baseStart_28875 baseEnd_28875 := by
    simpa [prefixWord, tailWord_28875, baseEnd_28875] using wordTrace_append hprefix tailTrace_28875
  have hstable : (prefixWord ++ tailWord_28875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28875).length < 2 ^ (prefixWord ++ tailWord_28875).sum := by decide
  have hdescent : baseEnd_28875 < baseStart_28875 := by decide
  rcases family_descends (prefixWord ++ tailWord_28875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28878 : List Nat := [4, 1, 1, 1, 4, 2, 1, 4, 2]
def baseStart_28878 : Nat := 118140960795 + 28878 * 2 ^ 59
def prefixEnd_28878 : Nat := 4983230072969 + 3 ^ 40 * 28878 * 2
def baseEnd_28878 : Nat := 13180706080571776348621

theorem tailTrace_28878 : CollatzResearch.WordTrace tailWord_28878 prefixEnd_28878 13180706080571776348621 := by
  unfold tailWord_28878
  simp only [CollatzResearch.WordTrace]
  refine ⟨131658398673426601856911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 702178126258275209903525 131658398673426601856911)
  ·
    refine ⟨197487598010139902785367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131658398673426601856911 197487598010139902785367)
    ·
      refine ⟨296231397015209854178051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197487598010139902785367 296231397015209854178051)
      ·
        refine ⟨444347095522814781267077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296231397015209854178051 444347095522814781267077)
        ·
          refine ⟨83315080410527771487577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 444347095522814781267077 83315080410527771487577)
          ·
            refine ⟨62486310307895828615683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83315080410527771487577 62486310307895828615683)
            ·
              refine ⟨93729465461843742923525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62486310307895828615683 93729465461843742923525)
              ·
                refine ⟨17574274774095701798161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93729465461843742923525 17574274774095701798161)
                ·
                  refine ⟨13180706080571776348621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17574274774095701798161 13180706080571776348621)
                  ·
                    rfl

theorem cell20_28878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_28878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28878 prefixEnd_28878 := by exact prefixLift 28878
  have htrace : WordTrace (prefixWord ++ tailWord_28878) baseStart_28878 baseEnd_28878 := by
    simpa [prefixWord, tailWord_28878, baseEnd_28878] using wordTrace_append hprefix tailTrace_28878
  have hstable : (prefixWord ++ tailWord_28878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28878).length < 2 ^ (prefixWord ++ tailWord_28878).sum := by decide
  have hdescent : baseEnd_28878 < baseStart_28878 := by decide
  rcases family_descends (prefixWord ++ tailWord_28878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28885 : List Nat := [1, 3, 2, 4, 2, 2, 1, 5]
def baseStart_28885 : Nat := 118140960795 + 28885 * 2 ^ 59
def prefixEnd_28885 : Nat := 4983230072969 + 3 ^ 40 * 28885 * 2
def baseEnd_28885 : Nat := 4394633690436954371753

theorem tailTrace_28885 : CollatzResearch.WordTrace tailWord_28885 prefixEnd_28885 4394633690436954371753 := by
  unfold tailWord_28885
  simp only [CollatzResearch.WordTrace]
  refine ⟨1053522500362053010360109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 702348333574702006906739 1053522500362053010360109)
  ·
    refine ⟨395070937635769878885041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1053522500362053010360109 395070937635769878885041)
    ·
      refine ⟨296303203226827409163781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395070937635769878885041 296303203226827409163781)
      ·
        refine ⟨55556850605030139218209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 296303203226827409163781 55556850605030139218209)
        ·
          refine ⟨41667637953772604413657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55556850605030139218209 41667637953772604413657)
          ·
            refine ⟨31250728465329453310243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41667637953772604413657 31250728465329453310243)
            ·
              refine ⟨46876092697994179965365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31250728465329453310243 46876092697994179965365)
              ·
                refine ⟨4394633690436954371753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46876092697994179965365 4394633690436954371753)
                ·
                  rfl

theorem cell20_28885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 5].length) (baseStart_28885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28885 prefixEnd_28885 := by exact prefixLift 28885
  have htrace : WordTrace (prefixWord ++ tailWord_28885) baseStart_28885 baseEnd_28885 := by
    simpa [prefixWord, tailWord_28885, baseEnd_28885] using wordTrace_append hprefix tailTrace_28885
  have hstable : (prefixWord ++ tailWord_28885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28885).length < 2 ^ (prefixWord ++ tailWord_28885).sum := by decide
  have hdescent : baseEnd_28885 < baseStart_28885 := by decide
  rcases family_descends (prefixWord ++ tailWord_28885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28889 : List Nat := [1, 2, 1, 2, 3, 1, 5, 5]
def baseStart_28889 : Nat := 118140960795 + 28889 * 2 ^ 59
def prefixEnd_28889 : Nat := 4983230072969 + 3 ^ 40 * 28889 * 2
def baseEnd_28889 : Nat := 4395242260101542327303

theorem tailTrace_28889 : CollatzResearch.WordTrace tailWord_28889 prefixEnd_28889 4395242260101542327303 := by
  unfold tailWord_28889
  simp only [CollatzResearch.WordTrace]
  refine ⟨1053668392347561693505721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 702445594898374462337147 1053668392347561693505721)
  ·
    refine ⟨790251294260671270129291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1053668392347561693505721 790251294260671270129291)
    ·
      refine ⟨1185376941391006905193937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 790251294260671270129291 1185376941391006905193937)
      ·
        refine ⟨889032706043255178895453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1185376941391006905193937 889032706043255178895453)
        ·
          refine ⟨333387264766220692085795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 889032706043255178895453 333387264766220692085795)
          ·
            refine ⟨500080897149331038128693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333387264766220692085795 500080897149331038128693)
            ·
              refine ⟨46882584107749784824565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 500080897149331038128693 46882584107749784824565)
              ·
                refine ⟨4395242260101542327303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46882584107749784824565 4395242260101542327303)
                ·
                  rfl

theorem cell20_28889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 5].length) (baseStart_28889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28889 prefixEnd_28889 := by exact prefixLift 28889
  have htrace : WordTrace (prefixWord ++ tailWord_28889) baseStart_28889 baseEnd_28889 := by
    simpa [prefixWord, tailWord_28889, baseEnd_28889] using wordTrace_append hprefix tailTrace_28889
  have hstable : (prefixWord ++ tailWord_28889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28889).length < 2 ^ (prefixWord ++ tailWord_28889).sum := by decide
  have hdescent : baseEnd_28889 < baseStart_28889 := by decide
  rcases family_descends (prefixWord ++ tailWord_28889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28906 : List Nat := [3, 1, 3, 1, 1, 2, 5, 4]
def baseStart_28906 : Nat := 118140960795 + 28906 * 2 ^ 59
def prefixEnd_28906 : Nat := 4983230072969 + 3 ^ 40 * 28906 * 2
def baseEnd_28906 : Nat := 4397828681176041138391

theorem tailTrace_28906 : CollatzResearch.WordTrace tailWord_28906 prefixEnd_28906 4397828681176041138391 := by
  unfold tailWord_28906
  simp only [CollatzResearch.WordTrace]
  refine ⟨263572108321493399218643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 702858955523982397916381 263572108321493399218643)
  ·
    refine ⟨395358162482240098827965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263572108321493399218643 395358162482240098827965)
    ·
      refine ⟨148259310930840037060487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395358162482240098827965 148259310930840037060487)
      ·
        refine ⟨222388966396260055590731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148259310930840037060487 222388966396260055590731)
        ·
          refine ⟨333583449594390083386097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222388966396260055590731 333583449594390083386097)
          ·
            refine ⟨250187587195792562539573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333583449594390083386097 250187587195792562539573)
            ·
              refine ⟨23455086299605552738085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 250187587195792562539573 23455086299605552738085)
              ·
                refine ⟨4397828681176041138391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23455086299605552738085 4397828681176041138391)
                ·
                  rfl

theorem cell20_28906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_28906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28906 prefixEnd_28906 := by exact prefixLift 28906
  have htrace : WordTrace (prefixWord ++ tailWord_28906) baseStart_28906 baseEnd_28906 := by
    simpa [prefixWord, tailWord_28906, baseEnd_28906] using wordTrace_append hprefix tailTrace_28906
  have hstable : (prefixWord ++ tailWord_28906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28906).length < 2 ^ (prefixWord ++ tailWord_28906).sum := by decide
  have hdescent : baseEnd_28906 < baseStart_28906 := by decide
  rcases family_descends (prefixWord ++ tailWord_28906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28930 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 5]
def baseStart_28930 : Nat := 118140960795 + 28930 * 2 ^ 59
def prefixEnd_28930 : Nat := 4983230072969 + 3 ^ 40 * 28930 * 2
def baseEnd_28930 : Nat := 13204440297490706615075

theorem tailTrace_28930 : CollatzResearch.WordTrace tailWord_28930 prefixEnd_28930 13204440297490706615075 := by
  unfold tailWord_28930
  simp only [CollatzResearch.WordTrace]
  refine ⟨263790946299756423937061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 703442523466017130498829 263790946299756423937061)
  ·
    refine ⟨49460802431204329488199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263790946299756423937061 49460802431204329488199)
    ·
      refine ⟨74191203646806494232299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49460802431204329488199 74191203646806494232299)
      ·
        refine ⟨111286805470209741348449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74191203646806494232299 111286805470209741348449)
        ·
          refine ⟨83465104102657306011337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111286805470209741348449 83465104102657306011337)
          ·
            refine ⟨62598828076992979508503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83465104102657306011337 62598828076992979508503)
            ·
              refine ⟨93898242115489469262755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62598828076992979508503 93898242115489469262755)
              ·
                refine ⟨140847363173234203894133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93898242115489469262755 140847363173234203894133)
                ·
                  refine ⟨13204440297490706615075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140847363173234203894133 13204440297490706615075)
                  ·
                    rfl

theorem cell20_28930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_28930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28930 prefixEnd_28930 := by exact prefixLift 28930
  have htrace : WordTrace (prefixWord ++ tailWord_28930) baseStart_28930 baseEnd_28930 := by
    simpa [prefixWord, tailWord_28930, baseEnd_28930] using wordTrace_append hprefix tailTrace_28930
  have hstable : (prefixWord ++ tailWord_28930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28930).length < 2 ^ (prefixWord ++ tailWord_28930).sum := by decide
  have hdescent : baseEnd_28930 < baseStart_28930 := by decide
  rcases family_descends (prefixWord ++ tailWord_28930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28937 : List Nat := [1, 2, 1, 1, 3, 4, 2, 4, 2]
def baseStart_28937 : Nat := 118140960795 + 28937 * 2 ^ 59
def prefixEnd_28937 : Nat := 4983230072969 + 3 ^ 40 * 28937 * 2
def baseEnd_28937 : Nat := 13207635288229793381713

theorem tailTrace_28937 : CollatzResearch.WordTrace tailWord_28937 prefixEnd_28937 13207635288229793381713 := by
  unfold tailWord_28937
  simp only [CollatzResearch.WordTrace]
  refine ⟨1055419096173665891253065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 703612730782443927502043 1055419096173665891253065)
  ·
    refine ⟨791564322130249418439799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1055419096173665891253065 791564322130249418439799)
    ·
      refine ⟨1187346483195374127659699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 791564322130249418439799 1187346483195374127659699)
      ·
        refine ⟨1781019724793061191489549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1187346483195374127659699 1781019724793061191489549)
        ·
          refine ⟨667882396797397946808581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1781019724793061191489549 667882396797397946808581)
          ·
            refine ⟨125227949399512115026609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 667882396797397946808581 125227949399512115026609)
            ·
              refine ⟨93920962049634086269957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125227949399512115026609 93920962049634086269957)
              ·
                refine ⟨17610180384306391175617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93920962049634086269957 17610180384306391175617)
                ·
                  refine ⟨13207635288229793381713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17610180384306391175617 13207635288229793381713)
                  ·
                    rfl

theorem cell20_28937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 2].length) (baseStart_28937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28937 prefixEnd_28937 := by exact prefixLift 28937
  have htrace : WordTrace (prefixWord ++ tailWord_28937) baseStart_28937 baseEnd_28937 := by
    simpa [prefixWord, tailWord_28937, baseEnd_28937] using wordTrace_append hprefix tailTrace_28937
  have hstable : (prefixWord ++ tailWord_28937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28937).length < 2 ^ (prefixWord ++ tailWord_28937).sum := by decide
  have hdescent : baseEnd_28937 < baseStart_28937 := by decide
  rcases family_descends (prefixWord ++ tailWord_28937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28967 : List Nat := [1, 1, 8, 1, 1, 2, 1, 3, 2]
def baseStart_28967 : Nat := 118140960795 + 28967 * 2 ^ 59
def prefixEnd_28967 : Nat := 4983230072969 + 3 ^ 40 * 28967 * 2
def baseEnd_28967 : Nat := 13221328105683022381591

theorem tailTrace_28967 : CollatzResearch.WordTrace tailWord_28967 prefixEnd_28967 13221328105683022381591 := by
  unfold tailWord_28967
  simp only [CollatzResearch.WordTrace]
  refine ⟨1056513286064981014845155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 704342190709987343230103 1056513286064981014845155)
  ·
    refine ⟨1584769929097471522267733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1056513286064981014845155 1584769929097471522267733)
    ·
      refine ⟨18571522606610994401575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 1584769929097471522267733 18571522606610994401575)
      ·
        refine ⟨27857283909916491602363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18571522606610994401575 27857283909916491602363)
        ·
          refine ⟨41785925864874737403545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27857283909916491602363 41785925864874737403545)
          ·
            refine ⟨31339444398656053052659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41785925864874737403545 31339444398656053052659)
            ·
              refine ⟨47009166597984079578989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31339444398656053052659 47009166597984079578989)
              ·
                refine ⟨17628437474244029842121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47009166597984079578989 17628437474244029842121)
                ·
                  refine ⟨13221328105683022381591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17628437474244029842121 13221328105683022381591)
                  ·
                    rfl

theorem cell20_28967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 2].length) (baseStart_28967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28967 prefixEnd_28967 := by exact prefixLift 28967
  have htrace : WordTrace (prefixWord ++ tailWord_28967) baseStart_28967 baseEnd_28967 := by
    simpa [prefixWord, tailWord_28967, baseEnd_28967] using wordTrace_append hprefix tailTrace_28967
  have hstable : (prefixWord ++ tailWord_28967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28967).length < 2 ^ (prefixWord ++ tailWord_28967).sum := by decide
  have hdescent : baseEnd_28967 < baseStart_28967 := by decide
  rcases family_descends (prefixWord ++ tailWord_28967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28972 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 5]
def baseStart_28972 : Nat := 118140960795 + 28972 * 2 ^ 59
def prefixEnd_28972 : Nat := 4983230072969 + 3 ^ 40 * 28972 * 2
def baseEnd_28972 : Nat := 13223610241925227214903

theorem tailTrace_28972 : CollatzResearch.WordTrace tailWord_28972 prefixEnd_28972 13223610241925227214903 := by
  unfold tailWord_28972
  simp only [CollatzResearch.WordTrace]
  refine ⟨528347825523433434388585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 704463767364577912518113 528347825523433434388585)
  ·
    refine ⟨396260869142575075791439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 528347825523433434388585 396260869142575075791439)
    ·
      refine ⟨594391303713862613687159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396260869142575075791439 594391303713862613687159)
      ·
        refine ⟨891586955570793920530739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594391303713862613687159 891586955570793920530739)
        ·
          refine ⟨1337380433356190880796109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 891586955570793920530739 1337380433356190880796109)
          ·
            refine ⟨501517662508571580298541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1337380433356190880796109 501517662508571580298541)
            ·
              refine ⟨188069123440714342611953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 501517662508571580298541 188069123440714342611953)
              ·
                refine ⟨141051842580535756958965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188069123440714342611953 141051842580535756958965)
                ·
                  refine ⟨13223610241925227214903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141051842580535756958965 13223610241925227214903)
                  ·
                    rfl

theorem cell20_28972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_28972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28972 prefixEnd_28972 := by exact prefixLift 28972
  have htrace : WordTrace (prefixWord ++ tailWord_28972) baseStart_28972 baseEnd_28972 := by
    simpa [prefixWord, tailWord_28972, baseEnd_28972] using wordTrace_append hprefix tailTrace_28972
  have hstable : (prefixWord ++ tailWord_28972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28972).length < 2 ^ (prefixWord ++ tailWord_28972).sum := by decide
  have hdescent : baseEnd_28972 < baseStart_28972 := by decide
  rcases family_descends (prefixWord ++ tailWord_28972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28975 : List Nat := [1, 1, 2, 1, 2, 1, 7, 3, 2]
def baseStart_28975 : Nat := 118140960795 + 28975 * 2 ^ 59
def prefixEnd_28975 : Nat := 4983230072969 + 3 ^ 40 * 28975 * 2
def baseEnd_28975 : Nat := 13224979523670550114891

theorem tailTrace_28975 : CollatzResearch.WordTrace tailWord_28975 prefixEnd_28975 13224979523670550114891 := by
  unfold tailWord_28975
  simp only [CollatzResearch.WordTrace]
  refine ⟨1056805070035998381136379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 704536713357332254090919 1056805070035998381136379)
  ·
    refine ⟨1585207605053997571704569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1056805070035998381136379 1585207605053997571704569)
    ·
      refine ⟨1188905703790498178778427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1585207605053997571704569 1188905703790498178778427)
      ·
        refine ⟨1783358555685747268167641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1188905703790498178778427 1783358555685747268167641)
        ·
          refine ⟨1337518916764310451125731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1783358555685747268167641 1337518916764310451125731)
          ·
            refine ⟨2006278375146465676688597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337518916764310451125731 2006278375146465676688597)
            ·
              refine ⟨47022149417495289297389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2006278375146465676688597 47022149417495289297389)
              ·
                refine ⟨17633306031560733486521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47022149417495289297389 17633306031560733486521)
                ·
                  refine ⟨13224979523670550114891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17633306031560733486521 13224979523670550114891)
                  ·
                    rfl

theorem cell20_28975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 2].length) (baseStart_28975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_28975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_28975 prefixEnd_28975 := by exact prefixLift 28975
  have htrace : WordTrace (prefixWord ++ tailWord_28975) baseStart_28975 baseEnd_28975 := by
    simpa [prefixWord, tailWord_28975, baseEnd_28975] using wordTrace_append hprefix tailTrace_28975
  have hstable : (prefixWord ++ tailWord_28975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28975).length < 2 ^ (prefixWord ++ tailWord_28975).sum := by decide
  have hdescent : baseEnd_28975 < baseStart_28975 := by decide
  rcases family_descends (prefixWord ++ tailWord_28975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29017 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 6]
def baseStart_29017 : Nat := 118140960795 + 29017 * 2 ^ 59
def prefixEnd_29017 : Nat := 4983230072969 + 3 ^ 40 * 29017 * 2
def baseEnd_29017 : Nat := 13244149468105070714719

theorem tailTrace_29017 : CollatzResearch.WordTrace tailWord_29017 prefixEnd_29017 13244149468105070714719 := by
  unfold tailWord_29017
  simp only [CollatzResearch.WordTrace]
  refine ⟨1058336935883839554165305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 705557957255893036110203 1058336935883839554165305)
  ·
    refine ⟨793752701912879665623979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1058336935883839554165305 793752701912879665623979)
    ·
      refine ⟨1190629052869319498435969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 793752701912879665623979 1190629052869319498435969)
      ·
        refine ⟨892971789651989623826977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1190629052869319498435969 892971789651989623826977)
        ·
          refine ⟨669728842238992217870233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 892971789651989623826977 669728842238992217870233)
          ·
            refine ⟨502296631679244163402675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 669728842238992217870233 502296631679244163402675)
            ·
              refine ⟨753444947518866245104013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502296631679244163402675 753444947518866245104013)
              ·
                refine ⟨282541855319574841914005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 753444947518866245104013 282541855319574841914005)
                ·
                  refine ⟨13244149468105070714719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 282541855319574841914005 13244149468105070714719)
                  ·
                    rfl

theorem cell20_29017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_29017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29017 prefixEnd_29017 := by exact prefixLift 29017
  have htrace : WordTrace (prefixWord ++ tailWord_29017) baseStart_29017 baseEnd_29017 := by
    simpa [prefixWord, tailWord_29017, baseEnd_29017] using wordTrace_append hprefix tailTrace_29017
  have hstable : (prefixWord ++ tailWord_29017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29017).length < 2 ^ (prefixWord ++ tailWord_29017).sum := by decide
  have hdescent : baseEnd_29017 < baseStart_29017 := by decide
  rcases family_descends (prefixWord ++ tailWord_29017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29051 : List Nat := [1, 1, 1, 1, 1, 8, 1, 4, 2]
def baseStart_29051 : Nat := 118140960795 + 29051 * 2 ^ 59
def prefixEnd_29051 : Nat := 4983230072969 + 3 ^ 40 * 29051 * 2
def baseEnd_29051 : Nat := 13259667994552063581247

theorem tailTrace_29051 : CollatzResearch.WordTrace tailWord_29051 prefixEnd_29051 13259667994552063581247 := by
  unfold tailWord_29051
  simp only [CollatzResearch.WordTrace]
  refine ⟨1059577017760663360903007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 706384678507108907268671 1059577017760663360903007)
  ·
    refine ⟨1589365526640995041354511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1059577017760663360903007 1589365526640995041354511)
    ·
      refine ⟨2384048289961492562031767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1589365526640995041354511 2384048289961492562031767)
      ·
        refine ⟨3576072434942238843047651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2384048289961492562031767 3576072434942238843047651)
        ·
          refine ⟨5364108652413358264571477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3576072434942238843047651 5364108652413358264571477)
          ·
            refine ⟨62860648270469042162947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 5364108652413358264571477 62860648270469042162947)
            ·
              refine ⟨94290972405703563244421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62860648270469042162947 94290972405703563244421)
              ·
                refine ⟨17679557326069418108329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94290972405703563244421 17679557326069418108329)
                ·
                  refine ⟨13259667994552063581247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17679557326069418108329 13259667994552063581247)
                  ·
                    rfl

theorem cell20_29051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 2].length) (baseStart_29051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29051 prefixEnd_29051 := by exact prefixLift 29051
  have htrace : WordTrace (prefixWord ++ tailWord_29051) baseStart_29051 baseEnd_29051 := by
    simpa [prefixWord, tailWord_29051, baseEnd_29051] using wordTrace_append hprefix tailTrace_29051
  have hstable : (prefixWord ++ tailWord_29051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29051).length < 2 ^ (prefixWord ++ tailWord_29051).sum := by decide
  have hdescent : baseEnd_29051 < baseStart_29051 := by decide
  rcases family_descends (prefixWord ++ tailWord_29051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29065 : List Nat := [1, 2, 1, 1, 6, 1, 2, 3, 3]
def baseStart_29065 : Nat := 118140960795 + 29065 * 2 ^ 59
def prefixEnd_29065 : Nat := 4983230072969 + 3 ^ 40 * 29065 * 2
def baseEnd_29065 : Nat := 13266057976030237114523

theorem tailTrace_29065 : CollatzResearch.WordTrace tailWord_29065 prefixEnd_29065 13266057976030237114523 := by
  unfold tailWord_29065
  simp only [CollatzResearch.WordTrace]
  refine ⟨1060087639709943751912649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 706725093139962501275099 1060087639709943751912649)
  ·
    refine ⟨795065729782457813934487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1060087639709943751912649 795065729782457813934487)
    ·
      refine ⟨1192598594673686720901731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 795065729782457813934487 1192598594673686720901731)
      ·
        refine ⟨1788897892010530081352597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1192598594673686720901731 1788897892010530081352597)
        ·
          refine ⟨83854588687993597563403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1788897892010530081352597 83854588687993597563403)
          ·
            refine ⟨125781883031990396345105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83854588687993597563403 125781883031990396345105)
            ·
              refine ⟨94336412273992797258829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125781883031990396345105 94336412273992797258829)
              ·
                refine ⟨35376154602747298972061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94336412273992797258829 35376154602747298972061)
                ·
                  refine ⟨13266057976030237114523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35376154602747298972061 13266057976030237114523)
                  ·
                    rfl

theorem cell20_29065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 3].length) (baseStart_29065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29065 prefixEnd_29065 := by exact prefixLift 29065
  have htrace : WordTrace (prefixWord ++ tailWord_29065) baseStart_29065 baseEnd_29065 := by
    simpa [prefixWord, tailWord_29065, baseEnd_29065] using wordTrace_append hprefix tailTrace_29065
  have hstable : (prefixWord ++ tailWord_29065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29065).length < 2 ^ (prefixWord ++ tailWord_29065).sum := by decide
  have hdescent : baseEnd_29065 < baseStart_29065 := by decide
  rcases family_descends (prefixWord ++ tailWord_29065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29093 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 6]
def baseStart_29093 : Nat := 118140960795 + 29093 * 2 ^ 59
def prefixEnd_29093 : Nat := 4983230072969 + 3 ^ 40 * 29093 * 2
def baseEnd_29093 : Nat := 13278837938986584181075

theorem tailTrace_29093 : CollatzResearch.WordTrace tailWord_29093 prefixEnd_29093 13278837938986584181075 := by
  unfold tailWord_29093
  simp only [CollatzResearch.WordTrace]
  refine ⟨1061108883608504533931933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 707405922405669689287955 1061108883608504533931933)
  ·
    refine ⟨397915831353189200224475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1061108883608504533931933 397915831353189200224475)
    ·
      refine ⟨596873747029783800336713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397915831353189200224475 596873747029783800336713)
      ·
        refine ⟨447655310272337850252535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 596873747029783800336713 447655310272337850252535)
        ·
          refine ⟨671482965408506775378803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447655310272337850252535 671482965408506775378803)
          ·
            refine ⟨1007224448112760163068205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671482965408506775378803 1007224448112760163068205)
            ·
              refine ⟨377709168042285061150577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1007224448112760163068205 377709168042285061150577)
              ·
                refine ⟨283281876031713795862933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 377709168042285061150577 283281876031713795862933)
                ·
                  refine ⟨13278837938986584181075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 283281876031713795862933 13278837938986584181075)
                  ·
                    rfl

theorem cell20_29093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_29093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29093 prefixEnd_29093 := by exact prefixLift 29093
  have htrace : WordTrace (prefixWord ++ tailWord_29093) baseStart_29093 baseEnd_29093 := by
    simpa [prefixWord, tailWord_29093, baseEnd_29093] using wordTrace_append hprefix tailTrace_29093
  have hstable : (prefixWord ++ tailWord_29093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29093).length < 2 ^ (prefixWord ++ tailWord_29093).sum := by decide
  have hdescent : baseEnd_29093 < baseStart_29093 := by decide
  rcases family_descends (prefixWord ++ tailWord_29093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29096 : List Nat := [2, 1, 6, 1, 1, 2, 7]
def baseStart_29096 : Nat := 118140960795 + 29096 * 2 ^ 59
def prefixEnd_29096 : Nat := 4983230072969 + 3 ^ 40 * 29096 * 2
def baseEnd_29096 : Nat := 1475578580081323009007

theorem tailTrace_29096 : CollatzResearch.WordTrace tailWord_29096 prefixEnd_29096 1475578580081323009007 := by
  unfold tailWord_29096
  simp only [CollatzResearch.WordTrace]
  refine ⟨530609151298818023145571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 707478868398424030860761 530609151298818023145571)
  ·
    refine ⟨795913726948227034718357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 530609151298818023145571 795913726948227034718357)
    ·
      refine ⟨37308455950698142252423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 795913726948227034718357 37308455950698142252423)
      ·
        refine ⟨55962683926047213378635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37308455950698142252423 55962683926047213378635)
        ·
          refine ⟨83944025889070820067953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55962683926047213378635 83944025889070820067953)
          ·
            refine ⟨62958019416803115050965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83944025889070820067953 62958019416803115050965)
            ·
              refine ⟨1475578580081323009007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 62958019416803115050965 1475578580081323009007)
              ·
                rfl

theorem cell20_29096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 7].length) (baseStart_29096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29096 prefixEnd_29096 := by exact prefixLift 29096
  have htrace : WordTrace (prefixWord ++ tailWord_29096) baseStart_29096 baseEnd_29096 := by
    simpa [prefixWord, tailWord_29096, baseEnd_29096] using wordTrace_append hprefix tailTrace_29096
  have hstable : (prefixWord ++ tailWord_29096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29096).length < 2 ^ (prefixWord ++ tailWord_29096).sum := by decide
  have hdescent : baseEnd_29096 < baseStart_29096 := by decide
  rcases family_descends (prefixWord ++ tailWord_29096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29165 : List Nat := [1, 5, 1, 3, 1, 1, 3, 1, 4]
def baseStart_29165 : Nat := 118140960795 + 29165 * 2 ^ 59
def prefixEnd_29165 : Nat := 4983230072969 + 3 ^ 40 * 29165 * 2
def baseEnd_29165 : Nat := 13311700700874333780781

theorem tailTrace_29165 : CollatzResearch.WordTrace tailWord_29165 prefixEnd_29165 13311700700874333780781 := by
  unfold tailWord_29165
  simp only [CollatzResearch.WordTrace]
  refine ⟨1063734939347660830552949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 709156626231773887035299 1063734939347660830552949)
  ·
    refine ⟨99725150563843202864339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1063734939347660830552949 99725150563843202864339)
    ·
      refine ⟨149587725845764804296509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99725150563843202864339 149587725845764804296509)
      ·
        refine ⟨56095397192161801611191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149587725845764804296509 56095397192161801611191)
        ·
          refine ⟨84143095788242702416787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56095397192161801611191 84143095788242702416787)
          ·
            refine ⟨126214643682364053625181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84143095788242702416787 126214643682364053625181)
            ·
              refine ⟨47330491380886520109443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126214643682364053625181 47330491380886520109443)
              ·
                refine ⟨70995737071329780164165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47330491380886520109443 70995737071329780164165)
                ·
                  refine ⟨13311700700874333780781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70995737071329780164165 13311700700874333780781)
                  ·
                    rfl

theorem cell20_29165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_29165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29165 prefixEnd_29165 := by exact prefixLift 29165
  have htrace : WordTrace (prefixWord ++ tailWord_29165) baseStart_29165 baseEnd_29165 := by
    simpa [prefixWord, tailWord_29165, baseEnd_29165] using wordTrace_append hprefix tailTrace_29165
  have hstable : (prefixWord ++ tailWord_29165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29165).length < 2 ^ (prefixWord ++ tailWord_29165).sum := by decide
  have hdescent : baseEnd_29165 < baseStart_29165 := by decide
  rcases family_descends (prefixWord ++ tailWord_29165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29216 : List Nat := [2, 1, 1, 6, 3, 1, 2, 2, 2]
def baseStart_29216 : Nat := 118140960795 + 29216 * 2 ^ 59
def prefixEnd_29216 : Nat := 4983230072969 + 3 ^ 40 * 29216 * 2
def baseEnd_29216 : Nat := 13334978490544823080573

theorem tailTrace_29216 : CollatzResearch.WordTrace tailWord_29216 prefixEnd_29216 13334978490544823080573 := by
  unfold tailWord_29216
  simp only [CollatzResearch.WordTrace]
  refine ⟨532797531081448270329751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 710396708108597693773001 532797531081448270329751)
  ·
    refine ⟨799196296622172405494627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 532797531081448270329751 799196296622172405494627)
    ·
      refine ⟨1198794444933258608241941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 799196296622172405494627 1198794444933258608241941)
      ·
        refine ⟨56193489606246497261341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1198794444933258608241941 56193489606246497261341)
        ·
          refine ⟨21072558602342436473003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56193489606246497261341 21072558602342436473003)
          ·
            refine ⟨31608837903513654709505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21072558602342436473003 31608837903513654709505)
            ·
              refine ⟨23706628427635241032129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31608837903513654709505 23706628427635241032129)
              ·
                refine ⟨17779971320726430774097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23706628427635241032129 17779971320726430774097)
                ·
                  refine ⟨13334978490544823080573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17779971320726430774097 13334978490544823080573)
                  ·
                    rfl

theorem cell20_29216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 2].length) (baseStart_29216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29216 prefixEnd_29216 := by exact prefixLift 29216
  have htrace : WordTrace (prefixWord ++ tailWord_29216) baseStart_29216 baseEnd_29216 := by
    simpa [prefixWord, tailWord_29216, baseEnd_29216] using wordTrace_append hprefix tailTrace_29216
  have hstable : (prefixWord ++ tailWord_29216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29216).length < 2 ^ (prefixWord ++ tailWord_29216).sum := by decide
  have hdescent : baseEnd_29216 < baseStart_29216 := by decide
  rcases family_descends (prefixWord ++ tailWord_29216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29217 : List Nat := [1, 2, 3, 2, 2, 1, 4, 2, 3]
def baseStart_29217 : Nat := 118140960795 + 29217 * 2 ^ 59
def prefixEnd_29217 : Nat := 4983230072969 + 3 ^ 40 * 29217 * 2
def baseEnd_29217 : Nat := 13335434917793264047235

theorem tailTrace_29217 : CollatzResearch.WordTrace tailWord_29217 prefixEnd_29217 13335434917793264047235 := by
  unfold tailWord_29217
  simp only [CollatzResearch.WordTrace]
  refine ⟨1065631535159273711445905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 710421023439515807630603 1065631535159273711445905)
  ·
    refine ⟨799223651369455283584429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1065631535159273711445905 799223651369455283584429)
    ·
      refine ⟨299708869263545731344161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 799223651369455283584429 299708869263545731344161)
      ·
        refine ⟨224781651947659298508121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299708869263545731344161 224781651947659298508121)
        ·
          refine ⟨168586238960744473881091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224781651947659298508121 168586238960744473881091)
          ·
            refine ⟨252879358441116710821637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168586238960744473881091 252879358441116710821637)
            ·
              refine ⟨47414879707709383279057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 252879358441116710821637 47414879707709383279057)
              ·
                refine ⟨35561159780782037459293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47414879707709383279057 35561159780782037459293)
                ·
                  refine ⟨13335434917793264047235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35561159780782037459293 13335434917793264047235)
                  ·
                    rfl

theorem cell20_29217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 3].length) (baseStart_29217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29217 prefixEnd_29217 := by exact prefixLift 29217
  have htrace : WordTrace (prefixWord ++ tailWord_29217) baseStart_29217 baseEnd_29217 := by
    simpa [prefixWord, tailWord_29217, baseEnd_29217] using wordTrace_append hprefix tailTrace_29217
  have hstable : (prefixWord ++ tailWord_29217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29217).length < 2 ^ (prefixWord ++ tailWord_29217).sum := by decide
  have hdescent : baseEnd_29217 < baseStart_29217 := by decide
  rcases family_descends (prefixWord ++ tailWord_29217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29317 : List Nat := [1, 3, 1, 1, 4, 2, 3, 3, 2]
def baseStart_29317 : Nat := 118140960795 + 29317 * 2 ^ 59
def prefixEnd_29317 : Nat := 4983230072969 + 3 ^ 40 * 29317 * 2
def baseEnd_29317 : Nat := 13381077642637360713493

theorem tailTrace_29317 : CollatzResearch.WordTrace tailWord_29317 prefixEnd_29317 13381077642637360713493 := by
  unfold tailWord_29317
  simp only [CollatzResearch.WordTrace]
  refine ⟨1069278834796990790086205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 712852556531327193390803 1069278834796990790086205)
  ·
    refine ⟨400979563048871546282327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1069278834796990790086205 400979563048871546282327)
    ·
      refine ⟨601469344573307319423491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400979563048871546282327 601469344573307319423491)
      ·
        refine ⟨902204016859960979135237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601469344573307319423491 902204016859960979135237)
        ·
          refine ⟨169163253161242683587857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 902204016859960979135237 169163253161242683587857)
          ·
            refine ⟨126872439870932012690893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169163253161242683587857 126872439870932012690893)
            ·
              refine ⟨47577164951599504759085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126872439870932012690893 47577164951599504759085)
              ·
                refine ⟨17841436856849814284657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47577164951599504759085 17841436856849814284657)
                ·
                  refine ⟨13381077642637360713493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17841436856849814284657 13381077642637360713493)
                  ·
                    rfl

theorem cell20_29317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 2].length) (baseStart_29317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29317 prefixEnd_29317 := by exact prefixLift 29317
  have htrace : WordTrace (prefixWord ++ tailWord_29317) baseStart_29317 baseEnd_29317 := by
    simpa [prefixWord, tailWord_29317, baseEnd_29317] using wordTrace_append hprefix tailTrace_29317
  have hstable : (prefixWord ++ tailWord_29317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29317).length < 2 ^ (prefixWord ++ tailWord_29317).sum := by decide
  have hdescent : baseEnd_29317 < baseStart_29317 := by decide
  rcases family_descends (prefixWord ++ tailWord_29317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29382 : List Nat := [6, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_29382 : Nat := 118140960795 + 29382 * 2 ^ 59
def prefixEnd_29382 : Nat := 4983230072969 + 3 ^ 40 * 29382 * 2
def baseEnd_29382 : Nat := 13410745413786023546561

theorem tailTrace_29382 : CollatzResearch.WordTrace tailWord_29382 prefixEnd_29382 13410745413786023546561 := by
  unfold tailWord_29382
  simp only [CollatzResearch.WordTrace]
  refine ⟨33489049361297090350075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 714433053041004594134933 33489049361297090350075)
  ·
    refine ⟨50233574041945635525113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33489049361297090350075 50233574041945635525113)
    ·
      refine ⟨37675180531459226643835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50233574041945635525113 37675180531459226643835)
      ·
        refine ⟨56512770797188839965753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37675180531459226643835 56512770797188839965753)
        ·
          refine ⟨42384578097891629974315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56512770797188839965753 42384578097891629974315)
          ·
            refine ⟨63576867146837444961473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42384578097891629974315 63576867146837444961473)
            ·
              refine ⟨47682650360128083721105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63576867146837444961473 47682650360128083721105)
              ·
                refine ⟨35761987770096062790829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47682650360128083721105 35761987770096062790829)
                ·
                  refine ⟨13410745413786023546561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35761987770096062790829 13410745413786023546561)
                  ·
                    rfl

theorem cell20_29382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_29382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29382 prefixEnd_29382 := by exact prefixLift 29382
  have htrace : WordTrace (prefixWord ++ tailWord_29382) baseStart_29382 baseEnd_29382 := by
    simpa [prefixWord, tailWord_29382, baseEnd_29382] using wordTrace_append hprefix tailTrace_29382
  have hstable : (prefixWord ++ tailWord_29382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29382).length < 2 ^ (prefixWord ++ tailWord_29382).sum := by decide
  have hdescent : baseEnd_29382 < baseStart_29382 := by decide
  rcases family_descends (prefixWord ++ tailWord_29382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29389 : List Nat := [1, 6, 2, 1, 2, 1, 1, 4, 2]
def baseStart_29389 : Nat := 118140960795 + 29389 * 2 ^ 59
def prefixEnd_29389 : Nat := 4983230072969 + 3 ^ 40 * 29389 * 2
def baseEnd_29389 : Nat := 13413940404525110313199

theorem tailTrace_29389 : CollatzResearch.WordTrace tailWord_29389 prefixEnd_29389 13413940404525110313199 := by
  unfold tailWord_29389
  simp only [CollatzResearch.WordTrace]
  refine ⟨1071904890536147086707221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 714603260357431391138147 1071904890536147086707221)
  ·
    refine ⟨50245541743881894689401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1071904890536147086707221 50245541743881894689401)
    ·
      refine ⟨37684156307911421017051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50245541743881894689401 37684156307911421017051)
      ·
        refine ⟨56526234461867131525577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37684156307911421017051 56526234461867131525577)
        ·
          refine ⟨42394675846400348644183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56526234461867131525577 42394675846400348644183)
          ·
            refine ⟨63592013769600522966275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42394675846400348644183 63592013769600522966275)
            ·
              refine ⟨95388020654400784449413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63592013769600522966275 95388020654400784449413)
              ·
                refine ⟨17885253872700147084265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95388020654400784449413 17885253872700147084265)
                ·
                  refine ⟨13413940404525110313199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17885253872700147084265 13413940404525110313199)
                  ·
                    rfl

theorem cell20_29389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_29389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29389 prefixEnd_29389 := by exact prefixLift 29389
  have htrace : WordTrace (prefixWord ++ tailWord_29389) baseStart_29389 baseEnd_29389 := by
    simpa [prefixWord, tailWord_29389, baseEnd_29389] using wordTrace_append hprefix tailTrace_29389
  have hstable : (prefixWord ++ tailWord_29389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29389).length < 2 ^ (prefixWord ++ tailWord_29389).sum := by decide
  have hdescent : baseEnd_29389 < baseStart_29389 := by decide
  rcases family_descends (prefixWord ++ tailWord_29389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29473 : List Nat := [1, 2, 3, 2, 1, 2, 1, 4, 4]
def baseStart_29473 : Nat := 118140960795 + 29473 * 2 ^ 59
def prefixEnd_29473 : Nat := 4983230072969 + 3 ^ 40 * 29473 * 2
def baseEnd_29473 : Nat := 13452280293394151512855

theorem tailTrace_29473 : CollatzResearch.WordTrace tailWord_29473 prefixEnd_29473 13452280293394151512855 := by
  unfold tailWord_29473
  simp only [CollatzResearch.WordTrace]
  refine ⟨1074968622231829432765073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 716645748154552955176715 1074968622231829432765073)
  ·
    refine ⟨806226466673872074573805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1074968622231829432765073 806226466673872074573805)
    ·
      refine ⟨302334925002702027965177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 806226466673872074573805 302334925002702027965177)
      ·
        refine ⟨226751193752026520973883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302334925002702027965177 226751193752026520973883)
        ·
          refine ⟨340126790628039781460825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226751193752026520973883 340126790628039781460825)
          ·
            refine ⟨255095092971029836095619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340126790628039781460825 255095092971029836095619)
            ·
              refine ⟨382642639456544754143429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255095092971029836095619 382642639456544754143429)
              ·
                refine ⟨71745494898102141401893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 382642639456544754143429 71745494898102141401893)
                ·
                  refine ⟨13452280293394151512855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71745494898102141401893 13452280293394151512855)
                  ·
                    rfl

theorem cell20_29473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_29473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29473 prefixEnd_29473 := by exact prefixLift 29473
  have htrace : WordTrace (prefixWord ++ tailWord_29473) baseStart_29473 baseEnd_29473 := by
    simpa [prefixWord, tailWord_29473, baseEnd_29473] using wordTrace_append hprefix tailTrace_29473
  have hstable : (prefixWord ++ tailWord_29473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29473).length < 2 ^ (prefixWord ++ tailWord_29473).sum := by decide
  have hdescent : baseEnd_29473 < baseStart_29473 := by decide
  rcases family_descends (prefixWord ++ tailWord_29473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29482 : List Nat := [3, 1, 4, 3, 2, 1, 1, 3, 2]
def baseStart_29482 : Nat := 118140960795 + 29482 * 2 ^ 59
def prefixEnd_29482 : Nat := 4983230072969 + 3 ^ 40 * 29482 * 2
def baseEnd_29482 : Nat := 13456388138630120212819

theorem tailTrace_29482 : CollatzResearch.WordTrace tailWord_29482 prefixEnd_29482 13456388138630120212819 := by
  unfold tailWord_29482
  simp only [CollatzResearch.WordTrace]
  refine ⟨268824219799805992460675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 716864586132815979895133 268824219799805992460675)
  ·
    refine ⟨403236329699708988691013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268824219799805992460675 403236329699708988691013)
    ·
      refine ⟨75606811818695435379565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 403236329699708988691013 75606811818695435379565)
      ·
        refine ⟨28352554432010788267337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75606811818695435379565 28352554432010788267337)
        ·
          refine ⟨21264415824008091200503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28352554432010788267337 21264415824008091200503)
          ·
            refine ⟨31896623736012136800755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21264415824008091200503 31896623736012136800755)
            ·
              refine ⟨47844935604018205201133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31896623736012136800755 47844935604018205201133)
              ·
                refine ⟨17941850851506826950425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47844935604018205201133 17941850851506826950425)
                ·
                  refine ⟨13456388138630120212819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17941850851506826950425 13456388138630120212819)
                  ·
                    rfl

theorem cell20_29482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 2].length) (baseStart_29482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29482 prefixEnd_29482 := by exact prefixLift 29482
  have htrace : WordTrace (prefixWord ++ tailWord_29482) baseStart_29482 baseEnd_29482 := by
    simpa [prefixWord, tailWord_29482, baseEnd_29482] using wordTrace_append hprefix tailTrace_29482
  have hstable : (prefixWord ++ tailWord_29482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29482).length < 2 ^ (prefixWord ++ tailWord_29482).sum := by decide
  have hdescent : baseEnd_29482 < baseStart_29482 := by decide
  rcases family_descends (prefixWord ++ tailWord_29482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29486 : List Nat := [4, 1, 3, 2, 1, 1, 3, 3, 2]
def baseStart_29486 : Nat := 118140960795 + 29486 * 2 ^ 59
def prefixEnd_29486 : Nat := 4983230072969 + 3 ^ 40 * 29486 * 2
def baseEnd_29486 : Nat := 13458213847623884079469

theorem tailTrace_29486 : CollatzResearch.WordTrace tailWord_29486 prefixEnd_29486 13458213847623884079469 := by
  unfold tailWord_29486
  simp only [CollatzResearch.WordTrace]
  refine ⟨134430346398091581623539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 716961847456488435325541 134430346398091581623539)
  ·
    refine ⟨201645519597137372435309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134430346398091581623539 201645519597137372435309)
    ·
      refine ⟨75617069848926514663241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201645519597137372435309 75617069848926514663241)
      ·
        refine ⟨56712802386694885997431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75617069848926514663241 56712802386694885997431)
        ·
          refine ⟨85069203580042328996147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56712802386694885997431 85069203580042328996147)
          ·
            refine ⟨127603805370063493494221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85069203580042328996147 127603805370063493494221)
            ·
              refine ⟨47851427013773810060333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127603805370063493494221 47851427013773810060333)
              ·
                refine ⟨17944285130165178772625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47851427013773810060333 17944285130165178772625)
                ·
                  refine ⟨13458213847623884079469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17944285130165178772625 13458213847623884079469)
                  ·
                    rfl

theorem cell20_29486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_29486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29486 prefixEnd_29486 := by exact prefixLift 29486
  have htrace : WordTrace (prefixWord ++ tailWord_29486) baseStart_29486 baseEnd_29486 := by
    simpa [prefixWord, tailWord_29486, baseEnd_29486] using wordTrace_append hprefix tailTrace_29486
  have hstable : (prefixWord ++ tailWord_29486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29486).length < 2 ^ (prefixWord ++ tailWord_29486).sum := by decide
  have hdescent : baseEnd_29486 < baseStart_29486 := by decide
  rcases family_descends (prefixWord ++ tailWord_29486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29507 : List Nat := [1, 1, 1, 3, 1, 4, 5, 2, 2]
def baseStart_29507 : Nat := 118140960795 + 29507 * 2 ^ 59
def prefixEnd_29507 : Nat := 4983230072969 + 3 ^ 40 * 29507 * 2
def baseEnd_29507 : Nat := 13467798819841144379383

theorem tailTrace_29507 : CollatzResearch.WordTrace tailWord_29507 prefixEnd_29507 13467798819841144379383 := by
  unfold tailWord_29507
  simp only [CollatzResearch.WordTrace]
  refine ⟨1076208704108653239502775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 717472469405768826335183 1076208704108653239502775)
  ·
    refine ⟨1614313056162979859254163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1076208704108653239502775 1614313056162979859254163)
    ·
      refine ⟨2421469584244469788881245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1614313056162979859254163 2421469584244469788881245)
      ·
        refine ⟨908051094091676170830467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2421469584244469788881245 908051094091676170830467)
        ·
          refine ⟨1362076641137514256245701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908051094091676170830467 1362076641137514256245701)
          ·
            refine ⟨255389370213283923046069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1362076641137514256245701 255389370213283923046069)
            ·
              refine ⟨23942753457495367785569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 255389370213283923046069 23942753457495367785569)
              ·
                refine ⟨17957065093121525839177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23942753457495367785569 17957065093121525839177)
                ·
                  refine ⟨13467798819841144379383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17957065093121525839177 13467798819841144379383)
                  ·
                    rfl

theorem cell20_29507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 2].length) (baseStart_29507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29507 prefixEnd_29507 := by exact prefixLift 29507
  have htrace : WordTrace (prefixWord ++ tailWord_29507) baseStart_29507 baseEnd_29507 := by
    simpa [prefixWord, tailWord_29507, baseEnd_29507] using wordTrace_append hprefix tailTrace_29507
  have hstable : (prefixWord ++ tailWord_29507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29507).length < 2 ^ (prefixWord ++ tailWord_29507).sum := by decide
  have hdescent : baseEnd_29507 < baseStart_29507 := by decide
  rcases family_descends (prefixWord ++ tailWord_29507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29521 : List Nat := [1, 2, 2, 1, 6, 1, 1, 3, 3]
def baseStart_29521 : Nat := 118140960795 + 29521 * 2 ^ 59
def prefixEnd_29521 : Nat := 4983230072969 + 3 ^ 40 * 29521 * 2
def baseEnd_29521 : Nat := 13474188801319317912659

theorem tailTrace_29521 : CollatzResearch.WordTrace tailWord_29521 prefixEnd_29521 13474188801319317912659 := by
  unfold tailWord_29521
  simp only [CollatzResearch.WordTrace]
  refine ⟨1076719326057933630512417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 717812884038622420341611 1076719326057933630512417)
  ·
    refine ⟨807539494543450222884313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1076719326057933630512417 807539494543450222884313)
    ·
      refine ⟨605654620907587667163235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 807539494543450222884313 605654620907587667163235)
      ·
        refine ⟨908481931361381500744853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605654620907587667163235 908481931361381500744853)
        ·
          refine ⟨42585090532564757847415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 908481931361381500744853 42585090532564757847415)
          ·
            refine ⟨63877635798847136771123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42585090532564757847415 63877635798847136771123)
            ·
              refine ⟨95816453698270705156685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63877635798847136771123 95816453698270705156685)
              ·
                refine ⟨35931170136851514433757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95816453698270705156685 35931170136851514433757)
                ·
                  refine ⟨13474188801319317912659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35931170136851514433757 13474188801319317912659)
                  ·
                    rfl

theorem cell20_29521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 3].length) (baseStart_29521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29521 prefixEnd_29521 := by exact prefixLift 29521
  have htrace : WordTrace (prefixWord ++ tailWord_29521) baseStart_29521 baseEnd_29521 := by
    simpa [prefixWord, tailWord_29521, baseEnd_29521] using wordTrace_append hprefix tailTrace_29521
  have hstable : (prefixWord ++ tailWord_29521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29521).length < 2 ^ (prefixWord ++ tailWord_29521).sum := by decide
  have hdescent : baseEnd_29521 < baseStart_29521 := by decide
  rcases family_descends (prefixWord ++ tailWord_29521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29563 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 5]
def baseStart_29563 : Nat := 118140960795 + 29563 * 2 ^ 59
def prefixEnd_29563 : Nat := 4983230072969 + 3 ^ 40 * 29563 * 2
def baseEnd_29563 : Nat := 13493358745753838512487

theorem tailTrace_29563 : CollatzResearch.WordTrace tailWord_29563 prefixEnd_29563 13493358745753838512487 := by
  unfold tailWord_29563
  simp only [CollatzResearch.WordTrace]
  refine ⟨1078251191905774803541343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 718834127937183202360895 1078251191905774803541343)
  ·
    refine ⟨1617376787858662205312015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1078251191905774803541343 1617376787858662205312015)
    ·
      refine ⟨2426065181787993307968023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1617376787858662205312015 2426065181787993307968023)
      ·
        refine ⟨3639097772681989961952035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2426065181787993307968023 3639097772681989961952035)
        ·
          refine ⟨5458646659022984942928053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3639097772681989961952035 5458646659022984942928053)
          ·
            refine ⟨511748124283404838399505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5458646659022984942928053 511748124283404838399505)
            ·
              refine ⟨383811093212553628799629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511748124283404838399505 383811093212553628799629)
              ·
                refine ⟨143929159954707610799861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383811093212553628799629 143929159954707610799861)
                ·
                  refine ⟨13493358745753838512487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143929159954707610799861 13493358745753838512487)
                  ·
                    rfl

theorem cell20_29563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_29563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29563 prefixEnd_29563 := by exact prefixLift 29563
  have htrace : WordTrace (prefixWord ++ tailWord_29563) baseStart_29563 baseEnd_29563 := by
    simpa [prefixWord, tailWord_29563, baseEnd_29563] using wordTrace_append hprefix tailTrace_29563
  have hstable : (prefixWord ++ tailWord_29563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29563).length < 2 ^ (prefixWord ++ tailWord_29563).sum := by decide
  have hdescent : baseEnd_29563 < baseStart_29563 := by decide
  rcases family_descends (prefixWord ++ tailWord_29563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29573 : List Nat := [1, 3, 1, 1, 3, 5, 1, 5]
def baseStart_29573 : Nat := 118140960795 + 29573 * 2 ^ 59
def prefixEnd_29573 : Nat := 4983230072969 + 3 ^ 40 * 29573 * 2
def baseEnd_29573 : Nat := 4499307672746082726371

theorem tailTrace_29573 : CollatzResearch.WordTrace tailWord_29573 prefixEnd_29573 4499307672746082726371 := by
  unfold tailWord_29573
  simp only [CollatzResearch.WordTrace]
  refine ⟨1078615921869546511405373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 719077281246364340936915 1078615921869546511405373)
  ·
    refine ⟨404480970701079941777015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1078615921869546511405373 404480970701079941777015)
    ·
      refine ⟨606721456051619912665523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404480970701079941777015 606721456051619912665523)
      ·
        refine ⟨910082184077429868998285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606721456051619912665523 910082184077429868998285)
        ·
          refine ⟨341280819029036200874357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 910082184077429868998285 341280819029036200874357)
          ·
            refine ⟨31995076783972143831971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 341280819029036200874357 31995076783972143831971)
            ·
              refine ⟨47992615175958215747957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31995076783972143831971 47992615175958215747957)
              ·
                refine ⟨4499307672746082726371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47992615175958215747957 4499307672746082726371)
                ·
                  rfl

theorem cell20_29573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 5].length) (baseStart_29573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29573 prefixEnd_29573 := by exact prefixLift 29573
  have htrace : WordTrace (prefixWord ++ tailWord_29573) baseStart_29573 baseEnd_29573 := by
    simpa [prefixWord, tailWord_29573, baseEnd_29573] using wordTrace_append hprefix tailTrace_29573
  have hstable : (prefixWord ++ tailWord_29573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29573).length < 2 ^ (prefixWord ++ tailWord_29573).sum := by decide
  have hdescent : baseEnd_29573 < baseStart_29573 := by decide
  rcases family_descends (prefixWord ++ tailWord_29573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29580 : List Nat := [2, 2, 1, 2, 1, 2, 4, 3, 3]
def baseStart_29580 : Nat := 118140960795 + 29580 * 2 ^ 59
def prefixEnd_29580 : Nat := 4983230072969 + 3 ^ 40 * 29580 * 2
def baseEnd_29580 : Nat := 13501118008977334945751

theorem tailTrace_29580 : CollatzResearch.WordTrace tailWord_29580 prefixEnd_29580 13501118008977334945751 := by
  unfold tailWord_29580
  simp only [CollatzResearch.WordTrace]
  refine ⟨539435616422093353455097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 719247488562791137940129 539435616422093353455097)
  ·
    refine ⟨404576712316570015091323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 539435616422093353455097 404576712316570015091323)
    ·
      refine ⟨606865068474855022636985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404576712316570015091323 606865068474855022636985)
      ·
        refine ⟨455148801356141266977739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 606865068474855022636985 455148801356141266977739)
        ·
          refine ⟨682723202034211900466609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455148801356141266977739 682723202034211900466609)
          ·
            refine ⟨512042401525658925349957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682723202034211900466609 512042401525658925349957)
            ·
              refine ⟨96007950286061048503117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 512042401525658925349957 96007950286061048503117)
              ·
                refine ⟨36002981357272893188669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96007950286061048503117 36002981357272893188669)
                ·
                  refine ⟨13501118008977334945751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36002981357272893188669 13501118008977334945751)
                  ·
                    rfl

theorem cell20_29580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_29580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29580 prefixEnd_29580 := by exact prefixLift 29580
  have htrace : WordTrace (prefixWord ++ tailWord_29580) baseStart_29580 baseEnd_29580 := by
    simpa [prefixWord, tailWord_29580, baseEnd_29580] using wordTrace_append hprefix tailTrace_29580
  have hstable : (prefixWord ++ tailWord_29580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29580).length < 2 ^ (prefixWord ++ tailWord_29580).sum := by decide
  have hdescent : baseEnd_29580 < baseStart_29580 := by decide
  rcases family_descends (prefixWord ++ tailWord_29580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29625 : List Nat := [1, 2, 1, 4, 2, 2, 1, 3, 4]
def baseStart_29625 : Nat := 118140960795 + 29625 * 2 ^ 59
def prefixEnd_29625 : Nat := 4983230072969 + 3 ^ 40 * 29625 * 2
def baseEnd_29625 : Nat := 13521657235157178445567

theorem tailTrace_29625 : CollatzResearch.WordTrace tailWord_29625 prefixEnd_29625 13521657235157178445567 := by
  unfold tailWord_29625
  simp only [CollatzResearch.WordTrace]
  refine ⟨1080512517681159392298329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 720341678454106261532219 1080512517681159392298329)
  ·
    refine ⟨810384388260869544223747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1080512517681159392298329 810384388260869544223747)
    ·
      refine ⟨1215576582391304316335621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 810384388260869544223747 1215576582391304316335621)
      ·
        refine ⟨227920609198369559312929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1215576582391304316335621 227920609198369559312929)
        ·
          refine ⟨170940456898777169484697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227920609198369559312929 170940456898777169484697)
          ·
            refine ⟨128205342674082877113523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170940456898777169484697 128205342674082877113523)
            ·
              refine ⟨192308014011124315670285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128205342674082877113523 192308014011124315670285)
              ·
                refine ⟨72115505254171618376357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192308014011124315670285 72115505254171618376357)
                ·
                  refine ⟨13521657235157178445567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72115505254171618376357 13521657235157178445567)
                  ·
                    rfl

theorem cell20_29625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_29625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29625 prefixEnd_29625 := by exact prefixLift 29625
  have htrace : WordTrace (prefixWord ++ tailWord_29625) baseStart_29625 baseEnd_29625 := by
    simpa [prefixWord, tailWord_29625, baseEnd_29625] using wordTrace_append hprefix tailTrace_29625
  have hstable : (prefixWord ++ tailWord_29625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29625).length < 2 ^ (prefixWord ++ tailWord_29625).sum := by decide
  have hdescent : baseEnd_29625 < baseStart_29625 := by decide
  rcases family_descends (prefixWord ++ tailWord_29625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29666 : List Nat := [3, 3, 3, 1, 1, 3, 6]
def baseStart_29666 : Nat := 118140960795 + 29666 * 2 ^ 59
def prefixEnd_29666 : Nat := 4983230072969 + 3 ^ 40 * 29666 * 2
def baseEnd_29666 : Nat := 1504485639149250897637

theorem tailTrace_29666 : CollatzResearch.WordTrace tailWord_29666 prefixEnd_29666 1504485639149250897637 := by
  unfold tailWord_29666
  simp only [CollatzResearch.WordTrace]
  refine ⟨270501977633155848635213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 721338607021748929693901 270501977633155848635213)
  ·
    refine ⟨101438241612433443238205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270501977633155848635213 101438241612433443238205)
    ·
      refine ⟨38039340604662541214327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101438241612433443238205 38039340604662541214327)
      ·
        refine ⟨57059010906993811821491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38039340604662541214327 57059010906993811821491)
        ·
          refine ⟨85588516360490717732237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57059010906993811821491 85588516360490717732237)
          ·
            refine ⟨32095693635184019149589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85588516360490717732237 32095693635184019149589)
            ·
              refine ⟨1504485639149250897637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32095693635184019149589 1504485639149250897637)
              ·
                rfl

theorem cell20_29666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 6].length) (baseStart_29666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29666 prefixEnd_29666 := by exact prefixLift 29666
  have htrace : WordTrace (prefixWord ++ tailWord_29666) baseStart_29666 baseEnd_29666 := by
    simpa [prefixWord, tailWord_29666, baseEnd_29666] using wordTrace_append hprefix tailTrace_29666
  have hstable : (prefixWord ++ tailWord_29666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29666).length < 2 ^ (prefixWord ++ tailWord_29666).sum := by decide
  have hdescent : baseEnd_29666 < baseStart_29666 := by decide
  rcases family_descends (prefixWord ++ tailWord_29666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29708 : List Nat := [2, 2, 1, 2, 3, 2, 2, 6]
def baseStart_29708 : Nat := 118140960795 + 29708 * 2 ^ 59
def prefixEnd_29708 : Nat := 4983230072969 + 3 ^ 40 * 29708 * 2
def baseEnd_29708 : Nat := 4519846898925926226187

theorem tailTrace_29708 : CollatzResearch.WordTrace tailWord_29708 prefixEnd_29708 4519846898925926226187 := by
  unfold tailWord_29708
  simp only [CollatzResearch.WordTrace]
  refine ⟨541769888190232283784889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 722359850920309711713185 541769888190232283784889)
  ·
    refine ⟨406327416142674212838667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 541769888190232283784889 406327416142674212838667)
    ·
      refine ⟨609491124214011319258001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406327416142674212838667 609491124214011319258001)
      ·
        refine ⟨457118343160508489443501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 609491124214011319258001 457118343160508489443501)
        ·
          refine ⟨171419378685190683541313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 457118343160508489443501 171419378685190683541313)
          ·
            refine ⟨128564534013893012655985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171419378685190683541313 128564534013893012655985)
            ·
              refine ⟨96423400510419759491989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128564534013893012655985 96423400510419759491989)
              ·
                refine ⟨4519846898925926226187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96423400510419759491989 4519846898925926226187)
                ·
                  rfl

theorem cell20_29708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_29708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29708 prefixEnd_29708 := by exact prefixLift 29708
  have htrace : WordTrace (prefixWord ++ tailWord_29708) baseStart_29708 baseEnd_29708 := by
    simpa [prefixWord, tailWord_29708, baseEnd_29708] using wordTrace_append hprefix tailTrace_29708
  have hstable : (prefixWord ++ tailWord_29708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29708).length < 2 ^ (prefixWord ++ tailWord_29708).sum := by decide
  have hdescent : baseEnd_29708 < baseStart_29708 := by decide
  rcases family_descends (prefixWord ++ tailWord_29708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29725 : List Nat := [1, 4, 2, 2, 4, 7]
def baseStart_29725 : Nat := 118140960795 + 29725 * 2 ^ 59
def prefixEnd_29725 : Nat := 4983230072969 + 3 ^ 40 * 29725 * 2
def baseEnd_29725 : Nat := 502492591111158337475

theorem tailTrace_29725 : CollatzResearch.WordTrace tailWord_29725 prefixEnd_29725 502492591111158337475 := by
  unfold tailWord_29725
  simp only [CollatzResearch.WordTrace]
  refine ⟨1084159817318876470938629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 722773211545917647292419 1084159817318876470938629)
  ·
    refine ⟨203279965747289338300993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1084159817318876470938629 203279965747289338300993)
    ·
      refine ⟨152459974310467003725745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203279965747289338300993 152459974310467003725745)
      ·
        refine ⟨114344980732850252794309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152459974310467003725745 114344980732850252794309)
        ·
          refine ⟨21439683887409422398933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114344980732850252794309 21439683887409422398933)
          ·
            refine ⟨502492591111158337475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 21439683887409422398933 502492591111158337475)
            ·
              rfl

theorem cell20_29725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 7].length) (baseStart_29725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29725 prefixEnd_29725 := by exact prefixLift 29725
  have htrace : WordTrace (prefixWord ++ tailWord_29725) baseStart_29725 baseEnd_29725 := by
    simpa [prefixWord, tailWord_29725, baseEnd_29725] using wordTrace_append hprefix tailTrace_29725
  have hstable : (prefixWord ++ tailWord_29725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29725).length < 2 ^ (prefixWord ++ tailWord_29725).sum := by decide
  have hdescent : baseEnd_29725 < baseStart_29725 := by decide
  rcases family_descends (prefixWord ++ tailWord_29725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29728 : List Nat := [2, 1, 1, 7, 1, 1, 2, 2, 3]
def baseStart_29728 : Nat := 118140960795 + 29728 * 2 ^ 59
def prefixEnd_29728 : Nat := 4983230072969 + 3 ^ 40 * 29728 * 2
def baseEnd_29728 : Nat := 13568669241746598011813

theorem tailTrace_29728 : CollatzResearch.WordTrace tailWord_29728 prefixEnd_29728 13568669241746598011813 := by
  unfold tailWord_29728
  simp only [CollatzResearch.WordTrace]
  refine ⟨542134618154003991648919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 722846157538671988865225 542134618154003991648919)
  ·
    refine ⟨813201927231005987473379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 542134618154003991648919 813201927231005987473379)
    ·
      refine ⟨1219802890846508981210069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 813201927231005987473379 1219802890846508981210069)
      ·
        refine ⟨28589130254215054247111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 1219802890846508981210069 28589130254215054247111)
        ·
          refine ⟨42883695381322581370667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28589130254215054247111 42883695381322581370667)
          ·
            refine ⟨64325543071983872056001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42883695381322581370667 64325543071983872056001)
            ·
              refine ⟨48244157303987904042001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64325543071983872056001 48244157303987904042001)
              ·
                refine ⟨36183117977990928031501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48244157303987904042001 36183117977990928031501)
                ·
                  refine ⟨13568669241746598011813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36183117977990928031501 13568669241746598011813)
                  ·
                    rfl

theorem cell20_29728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 3].length) (baseStart_29728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29728 prefixEnd_29728 := by exact prefixLift 29728
  have htrace : WordTrace (prefixWord ++ tailWord_29728) baseStart_29728 baseEnd_29728 := by
    simpa [prefixWord, tailWord_29728, baseEnd_29728] using wordTrace_append hprefix tailTrace_29728
  have hstable : (prefixWord ++ tailWord_29728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29728).length < 2 ^ (prefixWord ++ tailWord_29728).sum := by decide
  have hdescent : baseEnd_29728 < baseStart_29728 := by decide
  rcases family_descends (prefixWord ++ tailWord_29728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29773 : List Nat := [1, 6, 1, 1, 1, 2, 1, 5, 2]
def baseStart_29773 : Nat := 118140960795 + 29773 * 2 ^ 59
def prefixEnd_29773 : Nat := 4983230072969 + 3 ^ 40 * 29773 * 2
def baseEnd_29773 : Nat := 13589208467926441511629

theorem tailTrace_29773 : CollatzResearch.WordTrace tailWord_29773 prefixEnd_29773 13589208467926441511629 := by
  unfold tailWord_29773
  simp only [CollatzResearch.WordTrace]
  refine ⟨1085910521144980668685973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 723940347429987112457315 1085910521144980668685973)
  ·
    refine ⟨50902055678670968844655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1085910521144980668685973 50902055678670968844655)
    ·
      refine ⟨76353083518006453266983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50902055678670968844655 76353083518006453266983)
      ·
        refine ⟨114529625277009679900475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76353083518006453266983 114529625277009679900475)
        ·
          refine ⟨171794437915514519850713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114529625277009679900475 171794437915514519850713)
          ·
            refine ⟨128845828436635889888035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171794437915514519850713 128845828436635889888035)
            ·
              refine ⟨193268742654953834832053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128845828436635889888035 193268742654953834832053)
              ·
                refine ⟨18118944623901922015505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193268742654953834832053 18118944623901922015505)
                ·
                  refine ⟨13589208467926441511629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18118944623901922015505 13589208467926441511629)
                  ·
                    rfl

theorem cell20_29773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_29773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29773 prefixEnd_29773 := by exact prefixLift 29773
  have htrace : WordTrace (prefixWord ++ tailWord_29773) baseStart_29773 baseEnd_29773 := by
    simpa [prefixWord, tailWord_29773, baseEnd_29773] using wordTrace_append hprefix tailTrace_29773
  have hstable : (prefixWord ++ tailWord_29773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29773).length < 2 ^ (prefixWord ++ tailWord_29773).sum := by decide
  have hdescent : baseEnd_29773 < baseStart_29773 := by decide
  rcases family_descends (prefixWord ++ tailWord_29773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
