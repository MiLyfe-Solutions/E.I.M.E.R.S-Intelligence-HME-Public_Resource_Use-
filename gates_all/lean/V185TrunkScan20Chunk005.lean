import V185TrunkScan20Chunk004

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_29790 : List Nat := [4, 4, 1, 1, 1, 2, 2, 1, 4]
def baseStart_29790 : Nat := 118140960795 + 29790 * 2 ^ 59
def prefixEnd_29790 : Nat := 4983230072969 + 3 ^ 40 * 29790 * 2
def baseEnd_29790 : Nat := 13596967731149937944893

theorem tailTrace_29790 : CollatzResearch.WordTrace tailWord_29790 prefixEnd_29790 13596967731149937944893 := by
  unfold tailWord_29790
  simp only [CollatzResearch.WordTrace]
  refine ⟨135816320260424071506853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 724353708055595048036549 135816320260424071506853)
  ·
    refine ⟨25465560048829513407535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135816320260424071506853 25465560048829513407535)
    ·
      refine ⟨38198340073244270111303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25465560048829513407535 38198340073244270111303)
      ·
        refine ⟨57297510109866405166955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38198340073244270111303 57297510109866405166955)
        ·
          refine ⟨85946265164799607750433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57297510109866405166955 85946265164799607750433)
          ·
            refine ⟨64459698873599705812825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85946265164799607750433 64459698873599705812825)
            ·
              refine ⟨48344774155199779359619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64459698873599705812825 48344774155199779359619)
              ·
                refine ⟨72517161232799669039429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48344774155199779359619 72517161232799669039429)
                ·
                  refine ⟨13596967731149937944893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72517161232799669039429 13596967731149937944893)
                  ·
                    rfl

theorem cell20_29790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_29790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29790 prefixEnd_29790 := by exact prefixLift 29790
  have htrace : WordTrace (prefixWord ++ tailWord_29790) baseStart_29790 baseEnd_29790 := by
    simpa [prefixWord, tailWord_29790, baseEnd_29790] using wordTrace_append hprefix tailTrace_29790
  have hstable : (prefixWord ++ tailWord_29790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29790).length < 2 ^ (prefixWord ++ tailWord_29790).sum := by decide
  have hdescent : baseEnd_29790 < baseStart_29790 := by decide
  rcases family_descends (prefixWord ++ tailWord_29790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29791 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 5]
def baseStart_29791 : Nat := 118140960795 + 29791 * 2 ^ 59
def prefixEnd_29791 : Nat := 4983230072969 + 3 ^ 40 * 29791 * 2
def baseEnd_29791 : Nat := 13597424158398378911555

theorem tailTrace_29791 : CollatzResearch.WordTrace tailWord_29791 prefixEnd_29791 13597424158398378911555 := by
  unfold tailWord_29791
  simp only [CollatzResearch.WordTrace]
  refine ⟨1086567035079769742841227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 724378023386513161894151 1086567035079769742841227)
  ·
    refine ⟨1629850552619654614261841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1086567035079769742841227 1629850552619654614261841)
    ·
      refine ⟨1222387914464740960696381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1629850552619654614261841 1222387914464740960696381)
      ·
        refine ⟨458395467924277860261143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1222387914464740960696381 458395467924277860261143)
        ·
          refine ⟨687593201886416790391715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458395467924277860261143 687593201886416790391715)
          ·
            refine ⟨1031389802829625185587573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687593201886416790391715 1031389802829625185587573)
            ·
              refine ⟨96692794015277361148835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1031389802829625185587573 96692794015277361148835)
              ·
                refine ⟨145039191022916041723253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96692794015277361148835 145039191022916041723253)
                ·
                  refine ⟨13597424158398378911555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145039191022916041723253 13597424158398378911555)
                  ·
                    rfl

theorem cell20_29791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 5].length) (baseStart_29791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29791 prefixEnd_29791 := by exact prefixLift 29791
  have htrace : WordTrace (prefixWord ++ tailWord_29791) baseStart_29791 baseEnd_29791 := by
    simpa [prefixWord, tailWord_29791, baseEnd_29791] using wordTrace_append hprefix tailTrace_29791
  have hstable : (prefixWord ++ tailWord_29791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29791).length < 2 ^ (prefixWord ++ tailWord_29791).sum := by decide
  have hdescent : baseEnd_29791 < baseStart_29791 := by decide
  rcases family_descends (prefixWord ++ tailWord_29791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29794 : List Nat := [3, 3, 2, 2, 1, 1, 1, 3, 4]
def baseStart_29794 : Nat := 118140960795 + 29794 * 2 ^ 59
def prefixEnd_29794 : Nat := 4983230072969 + 3 ^ 40 * 29794 * 2
def baseEnd_29794 : Nat := 13598793440143701811543

theorem tailTrace_29794 : CollatzResearch.WordTrace tailWord_29794 prefixEnd_29794 13598793440143701811543 := by
  unfold tailWord_29794
  simp only [CollatzResearch.WordTrace]
  refine ⟨271669113517225313800109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 724450969379267503466957 271669113517225313800109)
  ·
    refine ⟨101875917568959492675041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271669113517225313800109 101875917568959492675041)
    ·
      refine ⟨76406938176719619506281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101875917568959492675041 76406938176719619506281)
      ·
        refine ⟨57305203632539714629711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76406938176719619506281 57305203632539714629711)
        ·
          refine ⟨85957805448809571944567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57305203632539714629711 85957805448809571944567)
          ·
            refine ⟨128936708173214357916851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85957805448809571944567 128936708173214357916851)
            ·
              refine ⟨193405062259821536875277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128936708173214357916851 193405062259821536875277)
              ·
                refine ⟨72526898347433076328229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193405062259821536875277 72526898347433076328229)
                ·
                  refine ⟨13598793440143701811543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72526898347433076328229 13598793440143701811543)
                  ·
                    rfl

theorem cell20_29794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_29794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29794 prefixEnd_29794 := by exact prefixLift 29794
  have htrace : WordTrace (prefixWord ++ tailWord_29794) baseStart_29794 baseEnd_29794 := by
    simpa [prefixWord, tailWord_29794, baseEnd_29794] using wordTrace_append hprefix tailTrace_29794
  have hstable : (prefixWord ++ tailWord_29794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29794).length < 2 ^ (prefixWord ++ tailWord_29794).sum := by decide
  have hdescent : baseEnd_29794 < baseStart_29794 := by decide
  rcases family_descends (prefixWord ++ tailWord_29794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29836 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 6]
def baseStart_29836 : Nat := 118140960795 + 29836 * 2 ^ 59
def prefixEnd_29836 : Nat := 4983230072969 + 3 ^ 40 * 29836 * 2
def baseEnd_29836 : Nat := 13617963384578222411371

theorem tailTrace_29836 : CollatzResearch.WordTrace tailWord_29836 prefixEnd_29836 13617963384578222411371 := by
  unfold tailWord_29836
  simp only [CollatzResearch.WordTrace]
  refine ⟨544104159958371214114681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 725472213277828285486241 544104159958371214114681)
  ·
    refine ⟨408078119968778410586011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 544104159958371214114681 408078119968778410586011)
    ·
      refine ⟨612117179953167615879017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408078119968778410586011 612117179953167615879017)
      ·
        refine ⟨459087884964875711909263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 612117179953167615879017 459087884964875711909263)
        ·
          refine ⟨688631827447313567863895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459087884964875711909263 688631827447313567863895)
          ·
            refine ⟨1032947741170970351795843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688631827447313567863895 1032947741170970351795843)
            ·
              refine ⟨1549421611756455527693765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1032947741170970351795843 1549421611756455527693765)
              ·
                refine ⟨290516552204335411442581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1549421611756455527693765 290516552204335411442581)
                ·
                  refine ⟨13617963384578222411371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 290516552204335411442581 13617963384578222411371)
                  ·
                    rfl

theorem cell20_29836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_29836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29836 prefixEnd_29836 := by exact prefixLift 29836
  have htrace : WordTrace (prefixWord ++ tailWord_29836) baseStart_29836 baseEnd_29836 := by
    simpa [prefixWord, tailWord_29836, baseEnd_29836] using wordTrace_append hprefix tailTrace_29836
  have hstable : (prefixWord ++ tailWord_29836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29836).length < 2 ^ (prefixWord ++ tailWord_29836).sum := by decide
  have hdescent : baseEnd_29836 < baseStart_29836 := by decide
  rcases family_descends (prefixWord ++ tailWord_29836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29843 : List Nat := [1, 1, 1, 2, 1, 2, 12]
def baseStart_29843 : Nat := 118140960795 + 29843 * 2 ^ 59
def prefixEnd_29843 : Nat := 4983230072969 + 3 ^ 40 * 29843 * 2
def baseEnd_29843 : Nat := 1513462041701923242001

theorem tailTrace_29843 : CollatzResearch.WordTrace tailWord_29843 prefixEnd_29843 1513462041701923242001 := by
  unfold tailWord_29843
  simp only [CollatzResearch.WordTrace]
  refine ⟨1088463630891382623734183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 725642420594255082489455 1088463630891382623734183)
  ·
    refine ⟨1632695446337073935601275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1088463630891382623734183 1632695446337073935601275)
    ·
      refine ⟨2449043169505610903401913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1632695446337073935601275 2449043169505610903401913)
      ·
        refine ⟨1836782377129208177551435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2449043169505610903401913 1836782377129208177551435)
        ·
          refine ⟨2755173565693812266327153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1836782377129208177551435 2755173565693812266327153)
          ·
            refine ⟨2066380174270359199745365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2755173565693812266327153 2066380174270359199745365)
            ·
              refine ⟨1513462041701923242001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 2066380174270359199745365 1513462041701923242001)
              ·
                rfl

theorem cell20_29843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 12].length) (baseStart_29843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29843 prefixEnd_29843 := by exact prefixLift 29843
  have htrace : WordTrace (prefixWord ++ tailWord_29843) baseStart_29843 baseEnd_29843 := by
    simpa [prefixWord, tailWord_29843, baseEnd_29843] using wordTrace_append hprefix tailTrace_29843
  have hstable : (prefixWord ++ tailWord_29843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29843).length < 2 ^ (prefixWord ++ tailWord_29843).sum := by decide
  have hdescent : baseEnd_29843 < baseStart_29843 := by decide
  rcases family_descends (prefixWord ++ tailWord_29843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29860 : List Nat := [2, 3, 1, 2, 3, 1, 1, 7]
def baseStart_29860 : Nat := 118140960795 + 29860 * 2 ^ 59
def prefixEnd_29860 : Nat := 4983230072969 + 3 ^ 40 * 29860 * 2
def baseEnd_29860 : Nat := 4542972546180268537091

theorem tailTrace_29860 : CollatzResearch.WordTrace tailWord_29860 prefixEnd_29860 4542972546180268537091 := by
  unfold tailWord_29860
  simp only [CollatzResearch.WordTrace]
  refine ⟨544541835914897263551517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 726055781219863018068689 544541835914897263551517)
  ·
    refine ⟨204203188468086473831819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 544541835914897263551517 204203188468086473831819)
    ·
      refine ⟨306304782702129710747729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204203188468086473831819 306304782702129710747729)
      ·
        refine ⟨229728587026597283060797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306304782702129710747729 229728587026597283060797)
        ·
          refine ⟨86148220134973981147799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229728587026597283060797 86148220134973981147799)
          ·
            refine ⟨129222330202460971721699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86148220134973981147799 129222330202460971721699)
            ·
              refine ⟨193833495303691457582549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129222330202460971721699 193833495303691457582549)
              ·
                refine ⟨4542972546180268537091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 193833495303691457582549 4542972546180268537091)
                ·
                  rfl

theorem cell20_29860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_29860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29860 prefixEnd_29860 := by exact prefixLift 29860
  have htrace : WordTrace (prefixWord ++ tailWord_29860) baseStart_29860 baseEnd_29860 := by
    simpa [prefixWord, tailWord_29860, baseEnd_29860] using wordTrace_append hprefix tailTrace_29860
  have hstable : (prefixWord ++ tailWord_29860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29860).length < 2 ^ (prefixWord ++ tailWord_29860).sum := by decide
  have hdescent : baseEnd_29860 < baseStart_29860 := by decide
  rcases family_descends (prefixWord ++ tailWord_29860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29863 : List Nat := [1, 1, 6, 2, 1, 2, 1, 3, 3]
def baseStart_29863 : Nat := 118140960795 + 29863 * 2 ^ 59
def prefixEnd_29863 : Nat := 4983230072969 + 3 ^ 40 * 29863 * 2
def baseEnd_29863 : Nat := 13630286920286128511261

theorem tailTrace_29863 : CollatzResearch.WordTrace tailWord_29863 prefixEnd_29863 13630286920286128511261 := by
  unfold tailWord_29863
  simp only [CollatzResearch.WordTrace]
  refine ⟨1089193090818926039462243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 726128727212617359641495 1089193090818926039462243)
  ·
    refine ⟨1633789636228389059193365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1089193090818926039462243 1633789636228389059193365)
    ·
      refine ⟨76583889198205737149689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1633789636228389059193365 76583889198205737149689)
      ·
        refine ⟨57437916898654302862267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76583889198205737149689 57437916898654302862267)
        ·
          refine ⟨86156875347981454293401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57437916898654302862267 86156875347981454293401)
          ·
            refine ⟨64617656510986090720051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86156875347981454293401 64617656510986090720051)
            ·
              refine ⟨96926484766479136080077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64617656510986090720051 96926484766479136080077)
              ·
                refine ⟨36347431787429676030029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96926484766479136080077 36347431787429676030029)
                ·
                  refine ⟨13630286920286128511261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36347431787429676030029 13630286920286128511261)
                  ·
                    rfl

theorem cell20_29863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 3].length) (baseStart_29863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29863 prefixEnd_29863 := by exact prefixLift 29863
  have htrace : WordTrace (prefixWord ++ tailWord_29863) baseStart_29863 baseEnd_29863 := by
    simpa [prefixWord, tailWord_29863, baseEnd_29863] using wordTrace_append hprefix tailTrace_29863
  have hstable : (prefixWord ++ tailWord_29863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29863).length < 2 ^ (prefixWord ++ tailWord_29863).sum := by decide
  have hdescent : baseEnd_29863 < baseStart_29863 := by decide
  rcases family_descends (prefixWord ++ tailWord_29863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29894 : List Nat := [6, 1, 2, 2, 9]
def baseStart_29894 : Nat := 118140960795 + 29894 * 2 ^ 59
def prefixEnd_29894 : Nat := 4983230072969 + 3 ^ 40 * 29894 * 2
def baseEnd_29894 : Nat := 168449829197380228121

theorem tailTrace_29894 : CollatzResearch.WordTrace tailWord_29894 prefixEnd_29894 168449829197380228121 := by
  unfold tailWord_29894
  simp only [CollatzResearch.WordTrace]
  refine ⟨34072617303331822932523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 726882502471078889227157 34072617303331822932523)
  ·
    refine ⟨51108925954997734398785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34072617303331822932523 51108925954997734398785)
    ·
      refine ⟨38331694466248300799089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51108925954997734398785 38331694466248300799089)
      ·
        refine ⟨28748770849686225599317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38331694466248300799089 28748770849686225599317)
        ·
          refine ⟨168449829197380228121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 28748770849686225599317 168449829197380228121)
          ·
            rfl

theorem cell20_29894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 9].length) (baseStart_29894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29894 prefixEnd_29894 := by exact prefixLift 29894
  have htrace : WordTrace (prefixWord ++ tailWord_29894) baseStart_29894 baseEnd_29894 := by
    simpa [prefixWord, tailWord_29894, baseEnd_29894] using wordTrace_append hprefix tailTrace_29894
  have hstable : (prefixWord ++ tailWord_29894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29894).length < 2 ^ (prefixWord ++ tailWord_29894).sum := by decide
  have hdescent : baseEnd_29894 < baseStart_29894 := by decide
  rcases family_descends (prefixWord ++ tailWord_29894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29946 : List Nat := [3, 1, 1, 1, 1, 4, 4, 3, 2]
def baseStart_29946 : Nat := 118140960795 + 29946 * 2 ^ 59
def prefixEnd_29946 : Nat := 4983230072969 + 3 ^ 40 * 29946 * 2
def baseEnd_29946 : Nat := 13668170381906728744255

theorem tailTrace_29946 : CollatzResearch.WordTrace tailWord_29946 prefixEnd_29946 13668170381906728744255 := by
  unfold tailWord_29946
  simp only [CollatzResearch.WordTrace]
  refine ⟨273055087379557803683423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 728146899678820809822461 273055087379557803683423)
  ·
    refine ⟨409582631069336705525135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273055087379557803683423 409582631069336705525135)
    ·
      refine ⟨614373946604005058287703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409582631069336705525135 614373946604005058287703)
      ·
        refine ⟨921560919906007587431555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614373946604005058287703 921560919906007587431555)
        ·
          refine ⟨1382341379859011381147333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 921560919906007587431555 1382341379859011381147333)
          ·
            refine ⟨259189008723564633965125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1382341379859011381147333 259189008723564633965125)
            ·
              refine ⟨48597939135668368868461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259189008723564633965125 48597939135668368868461)
              ·
                refine ⟨18224227175875638325673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48597939135668368868461 18224227175875638325673)
                ·
                  refine ⟨13668170381906728744255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18224227175875638325673 13668170381906728744255)
                  ·
                    rfl

theorem cell20_29946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 2].length) (baseStart_29946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29946 prefixEnd_29946 := by exact prefixLift 29946
  have htrace : WordTrace (prefixWord ++ tailWord_29946) baseStart_29946 baseEnd_29946 := by
    simpa [prefixWord, tailWord_29946, baseEnd_29946] using wordTrace_append hprefix tailTrace_29946
  have hstable : (prefixWord ++ tailWord_29946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29946).length < 2 ^ (prefixWord ++ tailWord_29946).sum := by decide
  have hdescent : baseEnd_29946 < baseStart_29946 := by decide
  rcases family_descends (prefixWord ++ tailWord_29946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29957 : List Nat := [1, 3, 1, 1, 2, 1, 11]
def baseStart_29957 : Nat := 118140960795 + 29957 * 2 ^ 59
def prefixEnd_29957 : Nat := 4983230072969 + 3 ^ 40 * 29957 * 2
def baseEnd_29957 : Nat := 1519243453515508819727

theorem tailTrace_29957 : CollatzResearch.WordTrace tailWord_29957 prefixEnd_29957 1519243453515508819727 := by
  unfold tailWord_29957
  simp only [CollatzResearch.WordTrace]
  refine ⟨1092621552478380093384125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 728414368318920062256083 1092621552478380093384125)
  ·
    refine ⟨409733082179392535019047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1092621552478380093384125 409733082179392535019047)
    ·
      refine ⟨614599623269088802528571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409733082179392535019047 614599623269088802528571)
      ·
        refine ⟨921899434903633203792857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614599623269088802528571 921899434903633203792857)
        ·
          refine ⟨691424576177724902844643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 921899434903633203792857 691424576177724902844643)
          ·
            refine ⟨1037136864266587354266965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691424576177724902844643 1037136864266587354266965)
            ·
              refine ⟨1519243453515508819727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1037136864266587354266965 1519243453515508819727)
              ·
                rfl

theorem cell20_29957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 11].length) (baseStart_29957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29957 prefixEnd_29957 := by exact prefixLift 29957
  have htrace : WordTrace (prefixWord ++ tailWord_29957) baseStart_29957 baseEnd_29957 := by
    simpa [prefixWord, tailWord_29957, baseEnd_29957] using wordTrace_append hprefix tailTrace_29957
  have hstable : (prefixWord ++ tailWord_29957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29957).length < 2 ^ (prefixWord ++ tailWord_29957).sum := by decide
  have hdescent : baseEnd_29957 < baseStart_29957 := by decide
  rcases family_descends (prefixWord ++ tailWord_29957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29960 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 5]
def baseStart_29960 : Nat := 118140960795 + 29960 * 2 ^ 59
def prefixEnd_29960 : Nat := 4983230072969 + 3 ^ 40 * 29960 * 2
def baseEnd_29960 : Nat := 13674560363384902277531

theorem tailTrace_29960 : CollatzResearch.WordTrace tailWord_29960 prefixEnd_29960 13674560363384902277531 := by
  unfold tailWord_29960
  simp only [CollatzResearch.WordTrace]
  refine ⟨546365485733755802871667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 728487314311674403828889 546365485733755802871667)
  ·
    refine ⟨819548228600633704307501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 546365485733755802871667 819548228600633704307501)
    ·
      refine ⟨307330585725237639115313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 819548228600633704307501 307330585725237639115313)
      ·
        refine ⟨230497939293928229336485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307330585725237639115313 230497939293928229336485)
        ·
          refine ⟨43218363617611543000591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230497939293928229336485 43218363617611543000591)
          ·
            refine ⟨64827545426417314500887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43218363617611543000591 64827545426417314500887)
            ·
              refine ⟨97241318139625971751331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64827545426417314500887 97241318139625971751331)
              ·
                refine ⟨145861977209438957626997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97241318139625971751331 145861977209438957626997)
                ·
                  refine ⟨13674560363384902277531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145861977209438957626997 13674560363384902277531)
                  ·
                    rfl

theorem cell20_29960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 5].length) (baseStart_29960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_29960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_29960 prefixEnd_29960 := by exact prefixLift 29960
  have htrace : WordTrace (prefixWord ++ tailWord_29960) baseStart_29960 baseEnd_29960 := by
    simpa [prefixWord, tailWord_29960, baseEnd_29960] using wordTrace_append hprefix tailTrace_29960
  have hstable : (prefixWord ++ tailWord_29960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29960).length < 2 ^ (prefixWord ++ tailWord_29960).sum := by decide
  have hdescent : baseEnd_29960 < baseStart_29960 := by decide
  rcases family_descends (prefixWord ++ tailWord_29960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30001 : List Nat := [1, 2, 2, 3, 3, 3, 1, 3, 2]
def baseStart_30001 : Nat := 118140960795 + 30001 * 2 ^ 59
def prefixEnd_30001 : Nat := 4983230072969 + 3 ^ 40 * 30001 * 2
def baseEnd_30001 : Nat := 13693273880570981910697

theorem tailTrace_30001 : CollatzResearch.WordTrace tailWord_30001 prefixEnd_30001 13693273880570981910697 := by
  unfold tailWord_30001
  simp only [CollatzResearch.WordTrace]
  refine ⟨1094226364318975607985857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 729484242879317071990571 1094226364318975607985857)
  ·
    refine ⟨820669773239231705989393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1094226364318975607985857 820669773239231705989393)
    ·
      refine ⟨615502329929423779492045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 820669773239231705989393 615502329929423779492045)
      ·
        refine ⟨230813373723533917309517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 615502329929423779492045 230813373723533917309517)
        ·
          refine ⟨86555015146325218991069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230813373723533917309517 86555015146325218991069)
          ·
            refine ⟨32458130679871957121651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86555015146325218991069 32458130679871957121651)
            ·
              refine ⟨48687196019807935682477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32458130679871957121651 48687196019807935682477)
              ·
                refine ⟨18257698507427975880929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48687196019807935682477 18257698507427975880929)
                ·
                  refine ⟨13693273880570981910697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18257698507427975880929 13693273880570981910697)
                  ·
                    rfl

theorem cell20_30001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 2].length) (baseStart_30001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30001 prefixEnd_30001 := by exact prefixLift 30001
  have htrace : WordTrace (prefixWord ++ tailWord_30001) baseStart_30001 baseEnd_30001 := by
    simpa [prefixWord, tailWord_30001, baseEnd_30001] using wordTrace_append hprefix tailTrace_30001
  have hstable : (prefixWord ++ tailWord_30001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30001).length < 2 ^ (prefixWord ++ tailWord_30001).sum := by decide
  have hdescent : baseEnd_30001 < baseStart_30001 := by decide
  rcases family_descends (prefixWord ++ tailWord_30001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30012 : List Nat := [2, 2, 2, 2, 1, 5, 6]
def baseStart_30012 : Nat := 118140960795 + 30012 * 2 ^ 59
def prefixEnd_30012 : Nat := 4983230072969 + 3 ^ 40 * 30012 * 2
def baseEnd_30012 : Nat := 1522032731144870282665

theorem tailTrace_30012 : CollatzResearch.WordTrace tailWord_30012 prefixEnd_30012 1522032731144870282665 := by
  unfold tailWord_30012
  simp only [CollatzResearch.WordTrace]
  refine ⟨547313783639562243318145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 729751711519416324424193 547313783639562243318145)
  ·
    refine ⟨410485337729671682488609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 547313783639562243318145 410485337729671682488609)
    ·
      refine ⟨307864003297253761866457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410485337729671682488609 307864003297253761866457)
      ·
        refine ⟨230898002472940321399843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307864003297253761866457 230898002472940321399843)
        ·
          refine ⟨346347003709410482099765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230898002472940321399843 346347003709410482099765)
          ·
            refine ⟨32470031597757232696853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 346347003709410482099765 32470031597757232696853)
            ·
              refine ⟨1522032731144870282665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32470031597757232696853 1522032731144870282665)
              ·
                rfl

theorem cell20_30012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 6].length) (baseStart_30012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30012 prefixEnd_30012 := by exact prefixLift 30012
  have htrace : WordTrace (prefixWord ++ tailWord_30012) baseStart_30012 baseEnd_30012 := by
    simpa [prefixWord, tailWord_30012, baseEnd_30012] using wordTrace_append hprefix tailTrace_30012
  have hstable : (prefixWord ++ tailWord_30012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30012).length < 2 ^ (prefixWord ++ tailWord_30012).sum := by decide
  have hdescent : baseEnd_30012 < baseStart_30012 := by decide
  rcases family_descends (prefixWord ++ tailWord_30012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30019 : List Nat := [1, 1, 1, 3, 1, 3, 1, 6, 3]
def baseStart_30019 : Nat := 118140960795 + 30019 * 2 ^ 59
def prefixEnd_30019 : Nat := 4983230072969 + 3 ^ 40 * 30019 * 2
def baseEnd_30019 : Nat := 13701489571042919310623

theorem tailTrace_30019 : CollatzResearch.WordTrace tailWord_30019 prefixEnd_30019 13701489571042919310623 := by
  unfold tailWord_30019
  simp only [CollatzResearch.WordTrace]
  refine ⟨1094882878253764682141111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 729921918835843121427407 1094882878253764682141111)
  ·
    refine ⟨1642324317380647023211667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1094882878253764682141111 1642324317380647023211667)
    ·
      refine ⟨2463486476070970534817501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1642324317380647023211667 2463486476070970534817501)
      ·
        refine ⟨923807428526613950556563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2463486476070970534817501 923807428526613950556563)
        ·
          refine ⟨1385711142789920925834845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923807428526613950556563 1385711142789920925834845)
          ·
            refine ⟨519641678546220347188067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1385711142789920925834845 519641678546220347188067)
            ·
              refine ⟨779462517819330520782101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519641678546220347188067 779462517819330520782101)
              ·
                refine ⟨36537305522781118161661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 779462517819330520782101 36537305522781118161661)
                ·
                  refine ⟨13701489571042919310623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36537305522781118161661 13701489571042919310623)
                  ·
                    rfl

theorem cell20_30019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 3].length) (baseStart_30019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30019 prefixEnd_30019 := by exact prefixLift 30019
  have htrace : WordTrace (prefixWord ++ tailWord_30019) baseStart_30019 baseEnd_30019 := by
    simpa [prefixWord, tailWord_30019, baseEnd_30019] using wordTrace_append hprefix tailTrace_30019
  have hstable : (prefixWord ++ tailWord_30019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30019).length < 2 ^ (prefixWord ++ tailWord_30019).sum := by decide
  have hdescent : baseEnd_30019 < baseStart_30019 := by decide
  rcases family_descends (prefixWord ++ tailWord_30019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30036 : List Nat := [2, 4, 1, 1, 2, 1, 3, 3, 3]
def baseStart_30036 : Nat := 118140960795 + 30036 * 2 ^ 59
def prefixEnd_30036 : Nat := 4983230072969 + 3 ^ 40 * 30036 * 2
def baseEnd_30036 : Nat := 13709248834266415743887

theorem tailTrace_30036 : CollatzResearch.WordTrace tailWord_30036 prefixEnd_30036 13709248834266415743887 := by
  unfold tailWord_30036
  simp only [CollatzResearch.WordTrace]
  refine ⟨547751459596088292754981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 730335279461451057006641 547751459596088292754981)
  ·
    refine ⟨102703398674266554891559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 547751459596088292754981 102703398674266554891559)
    ·
      refine ⟨154055098011399832337339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102703398674266554891559 154055098011399832337339)
      ·
        refine ⟨231082647017099748506009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154055098011399832337339 231082647017099748506009)
        ·
          refine ⟨173311985262824811379507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231082647017099748506009 173311985262824811379507)
          ·
            refine ⟨259967977894237217069261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173311985262824811379507 259967977894237217069261)
            ·
              refine ⟨97487991710338956400973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259967977894237217069261 97487991710338956400973)
              ·
                refine ⟨36557996891377108650365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97487991710338956400973 36557996891377108650365)
                ·
                  refine ⟨13709248834266415743887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36557996891377108650365 13709248834266415743887)
                  ·
                    rfl

theorem cell20_30036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_30036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30036 prefixEnd_30036 := by exact prefixLift 30036
  have htrace : WordTrace (prefixWord ++ tailWord_30036) baseStart_30036 baseEnd_30036 := by
    simpa [prefixWord, tailWord_30036, baseEnd_30036] using wordTrace_append hprefix tailTrace_30036
  have hstable : (prefixWord ++ tailWord_30036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30036).length < 2 ^ (prefixWord ++ tailWord_30036).sum := by decide
  have hdescent : baseEnd_30036 < baseStart_30036 := by decide
  rcases family_descends (prefixWord ++ tailWord_30036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30050 : List Nat := [3, 3, 2, 1, 1, 1, 1, 8]
def baseStart_30050 : Nat := 118140960795 + 30050 * 2 ^ 59
def prefixEnd_30050 : Nat := 4983230072969 + 3 ^ 40 * 30050 * 2
def baseEnd_30050 : Nat := 4571879605248196425721

theorem tailTrace_30050 : CollatzResearch.WordTrace tailWord_30050 prefixEnd_30050 4571879605248196425721 := by
  unfold tailWord_30050
  simp only [CollatzResearch.WordTrace]
  refine ⟨274003385285364244129901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 730675694094304651013069 274003385285364244129901)
  ·
    refine ⟨102751269482011591548713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274003385285364244129901 102751269482011591548713)
    ·
      refine ⟨77063452111508693661535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102751269482011591548713 77063452111508693661535)
      ·
        refine ⟨115595178167263040492303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77063452111508693661535 115595178167263040492303)
        ·
          refine ⟨173392767250894560738455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115595178167263040492303 173392767250894560738455)
          ·
            refine ⟨260089150876341841107683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173392767250894560738455 260089150876341841107683)
            ·
              refine ⟨390133726314512761661525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260089150876341841107683 390133726314512761661525)
              ·
                refine ⟨4571879605248196425721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 390133726314512761661525 4571879605248196425721)
                ·
                  rfl

theorem cell20_30050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_30050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30050 prefixEnd_30050 := by exact prefixLift 30050
  have htrace : WordTrace (prefixWord ++ tailWord_30050) baseStart_30050 baseEnd_30050 := by
    simpa [prefixWord, tailWord_30050, baseEnd_30050] using wordTrace_append hprefix tailTrace_30050
  have hstable : (prefixWord ++ tailWord_30050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30050).length < 2 ^ (prefixWord ++ tailWord_30050).sum := by decide
  have hdescent : baseEnd_30050 < baseStart_30050 := by decide
  rcases family_descends (prefixWord ++ tailWord_30050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30088 : List Nat := [2, 1, 3, 3, 1, 2, 3, 5]
def baseStart_30088 : Nat := 118140960795 + 30088 * 2 ^ 59
def prefixEnd_30088 : Nat := 4983230072969 + 3 ^ 40 * 30088 * 2
def baseEnd_30088 : Nat := 4577661017061782003447

theorem tailTrace_30088 : CollatzResearch.WordTrace tailWord_30088 prefixEnd_30088 4577661017061782003447 := by
  unfold tailWord_30088
  simp only [CollatzResearch.WordTrace]
  refine ⟨548699757501894733201459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 731599676669192977601945 548699757501894733201459)
  ·
    refine ⟨823049636252842099802189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 548699757501894733201459 823049636252842099802189)
    ·
      refine ⟨308643613594815787425821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 823049636252842099802189 308643613594815787425821)
      ·
        refine ⟨115741355098055920284683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308643613594815787425821 115741355098055920284683)
        ·
          refine ⟨173612032647083880427025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115741355098055920284683 173612032647083880427025)
          ·
            refine ⟨130209024485312910320269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173612032647083880427025 130209024485312910320269)
            ·
              refine ⟨48828384181992341370101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130209024485312910320269 48828384181992341370101)
              ·
                refine ⟨4577661017061782003447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48828384181992341370101 4577661017061782003447)
                ·
                  rfl

theorem cell20_30088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_30088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30088 prefixEnd_30088 := by exact prefixLift 30088
  have htrace : WordTrace (prefixWord ++ tailWord_30088) baseStart_30088 baseEnd_30088 := by
    simpa [prefixWord, tailWord_30088, baseEnd_30088] using wordTrace_append hprefix tailTrace_30088
  have hstable : (prefixWord ++ tailWord_30088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30088).length < 2 ^ (prefixWord ++ tailWord_30088).sum := by decide
  have hdescent : baseEnd_30088 < baseStart_30088 := by decide
  rcases family_descends (prefixWord ++ tailWord_30088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30205 : List Nat := [1, 4, 1, 1, 1, 6, 2, 1, 3]
def baseStart_30205 : Nat := 118140960795 + 30205 * 2 ^ 59
def prefixEnd_30205 : Nat := 4983230072969 + 3 ^ 40 * 30205 * 2
def baseEnd_30205 : Nat := 13786385039252939109863

theorem tailTrace_30205 : CollatzResearch.WordTrace tailWord_30205 prefixEnd_30205 13786385039252939109863 := by
  unfold tailWord_30205
  simp only [CollatzResearch.WordTrace]
  refine ⟨1101666855579918448412069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 734444570386612298941379 1101666855579918448412069)
  ·
    refine ⟨206562535421234709077263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1101666855579918448412069 206562535421234709077263)
    ·
      refine ⟨309843803131852063615895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206562535421234709077263 309843803131852063615895)
      ·
        refine ⟨464765704697778095423843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309843803131852063615895 464765704697778095423843)
        ·
          refine ⟨697148557046667143135765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464765704697778095423843 697148557046667143135765)
          ·
            refine ⟨32678838611562522334489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 697148557046667143135765 32678838611562522334489)
            ·
              refine ⟨24509128958671891750867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32678838611562522334489 24509128958671891750867)
              ·
                refine ⟨36763693438007837626301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24509128958671891750867 36763693438007837626301)
                ·
                  refine ⟨13786385039252939109863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36763693438007837626301 13786385039252939109863)
                  ·
                    rfl

theorem cell20_30205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_30205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30205 prefixEnd_30205 := by exact prefixLift 30205
  have htrace : WordTrace (prefixWord ++ tailWord_30205) baseStart_30205 baseEnd_30205 := by
    simpa [prefixWord, tailWord_30205, baseEnd_30205] using wordTrace_append hprefix tailTrace_30205
  have hstable : (prefixWord ++ tailWord_30205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30205).length < 2 ^ (prefixWord ++ tailWord_30205).sum := by decide
  have hdescent : baseEnd_30205 < baseStart_30205 := by decide
  rcases family_descends (prefixWord ++ tailWord_30205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30216 : List Nat := [2, 1, 3, 2, 1, 1, 2, 4, 4]
def baseStart_30216 : Nat := 118140960795 + 30216 * 2 ^ 59
def prefixEnd_30216 : Nat := 4983230072969 + 3 ^ 40 * 30216 * 2
def baseEnd_30216 : Nat := 13791405738985789743151

theorem tailTrace_30216 : CollatzResearch.WordTrace tailWord_30216 prefixEnd_30216 13791405738985789743151 := by
  unfold tailWord_30216
  simp only [CollatzResearch.WordTrace]
  refine ⟨551034029270033663531251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 734712039026711551375001 551034029270033663531251)
  ·
    refine ⟨826551043905050495296877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 551034029270033663531251 826551043905050495296877)
    ·
      refine ⟨309956641464393935736329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 826551043905050495296877 309956641464393935736329)
      ·
        refine ⟨232467481098295451802247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309956641464393935736329 232467481098295451802247)
        ·
          refine ⟨348701221647443177703371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232467481098295451802247 348701221647443177703371)
          ·
            refine ⟨523051832471164766555057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348701221647443177703371 523051832471164766555057)
            ·
              refine ⟨392288874353373574916293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 523051832471164766555057 392288874353373574916293)
              ·
                refine ⟨73554163941257545296805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 392288874353373574916293 73554163941257545296805)
                ·
                  refine ⟨13791405738985789743151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73554163941257545296805 13791405738985789743151)
                  ·
                    rfl

theorem cell20_30216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_30216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30216 prefixEnd_30216 := by exact prefixLift 30216
  have htrace : WordTrace (prefixWord ++ tailWord_30216) baseStart_30216 baseEnd_30216 := by
    simpa [prefixWord, tailWord_30216, baseEnd_30216] using wordTrace_append hprefix tailTrace_30216
  have hstable : (prefixWord ++ tailWord_30216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30216).length < 2 ^ (prefixWord ++ tailWord_30216).sum := by decide
  have hdescent : baseEnd_30216 < baseStart_30216 := by decide
  rcases family_descends (prefixWord ++ tailWord_30216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30250 : List Nat := [3, 1, 4, 1, 1, 1, 3, 4, 2]
def baseStart_30250 : Nat := 118140960795 + 30250 * 2 ^ 59
def prefixEnd_30250 : Nat := 4983230072969 + 3 ^ 40 * 30250 * 2
def baseEnd_30250 : Nat := 13806924265432782609679

theorem tailTrace_30250 : CollatzResearch.WordTrace tailWord_30250 prefixEnd_30250 13806924265432782609679 := by
  unfold tailWord_30250
  simp only [CollatzResearch.WordTrace]
  refine ⟨275827035104222783450051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 735538760277927422533469 275827035104222783450051)
  ·
    refine ⟨413740552656334175175077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275827035104222783450051 413740552656334175175077)
    ·
      refine ⟨77576353623062657845327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 413740552656334175175077 77576353623062657845327)
      ·
        refine ⟨116364530434593986767991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77576353623062657845327 116364530434593986767991)
        ·
          refine ⟨174546795651890980151987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116364530434593986767991 174546795651890980151987)
          ·
            refine ⟨261820193477836470227981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174546795651890980151987 261820193477836470227981)
            ·
              refine ⟨98182572554188676335493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261820193477836470227981 98182572554188676335493)
              ·
                refine ⟨18409232353910376812905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98182572554188676335493 18409232353910376812905)
                ·
                  refine ⟨13806924265432782609679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18409232353910376812905 13806924265432782609679)
                  ·
                    rfl

theorem cell20_30250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 2].length) (baseStart_30250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30250 prefixEnd_30250 := by exact prefixLift 30250
  have htrace : WordTrace (prefixWord ++ tailWord_30250) baseStart_30250 baseEnd_30250 := by
    simpa [prefixWord, tailWord_30250, baseEnd_30250] using wordTrace_append hprefix tailTrace_30250
  have hstable : (prefixWord ++ tailWord_30250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30250).length < 2 ^ (prefixWord ++ tailWord_30250).sum := by decide
  have hdescent : baseEnd_30250 < baseStart_30250 := by decide
  rcases family_descends (prefixWord ++ tailWord_30250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30292 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 6]
def baseStart_30292 : Nat := 118140960795 + 30292 * 2 ^ 59
def prefixEnd_30292 : Nat := 4983230072969 + 3 ^ 40 * 30292 * 2
def baseEnd_30292 : Nat := 13826094209867303209507

theorem tailTrace_30292 : CollatzResearch.WordTrace tailWord_30292 prefixEnd_30292 13826094209867303209507 := by
  unfold tailWord_30292
  simp only [CollatzResearch.WordTrace]
  refine ⟨552420003132366153414565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 736560004176488204552753 552420003132366153414565)
  ·
    refine ⟨103578750587318653765231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 552420003132366153414565 103578750587318653765231)
    ·
      refine ⟨155368125880977980647847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103578750587318653765231 155368125880977980647847)
      ·
        refine ⟨233052188821466970971771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155368125880977980647847 233052188821466970971771)
        ·
          refine ⟨349578283232200456457657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233052188821466970971771 349578283232200456457657)
          ·
            refine ⟨262183712424150342343243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349578283232200456457657 262183712424150342343243)
            ·
              refine ⟨393275568636225513514865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262183712424150342343243 393275568636225513514865)
              ·
                refine ⟨294956676477169135136149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393275568636225513514865 294956676477169135136149)
                ·
                  refine ⟨13826094209867303209507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 294956676477169135136149 13826094209867303209507)
                  ·
                    rfl

theorem cell20_30292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_30292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30292 prefixEnd_30292 := by exact prefixLift 30292
  have htrace : WordTrace (prefixWord ++ tailWord_30292) baseStart_30292 baseEnd_30292 := by
    simpa [prefixWord, tailWord_30292, baseEnd_30292] using wordTrace_append hprefix tailTrace_30292
  have hstable : (prefixWord ++ tailWord_30292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30292).length < 2 ^ (prefixWord ++ tailWord_30292).sum := by decide
  have hdescent : baseEnd_30292 < baseStart_30292 := by decide
  rcases family_descends (prefixWord ++ tailWord_30292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30294 : List Nat := [5, 2, 2, 2, 2, 1, 1, 2, 3]
def baseStart_30294 : Nat := 118140960795 + 30294 * 2 ^ 59
def prefixEnd_30294 : Nat := 4983230072969 + 3 ^ 40 * 30294 * 2
def baseEnd_30294 : Nat := 13827007064364185142833

theorem tailTrace_30294 : CollatzResearch.WordTrace tailWord_30294 prefixEnd_30294 13827007064364185142833 := by
  unfold tailWord_30294
  simp only [CollatzResearch.WordTrace]
  refine ⟨69057059516092915525121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 736608634838324432267957 69057059516092915525121)
  ·
    refine ⟨51792794637069686643841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69057059516092915525121 51792794637069686643841)
    ·
      refine ⟨38844595977802264982881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51792794637069686643841 38844595977802264982881)
      ·
        refine ⟨29133446983351698737161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38844595977802264982881 29133446983351698737161)
        ·
          refine ⟨21850085237513774052871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29133446983351698737161 21850085237513774052871)
          ·
            refine ⟨32775127856270661079307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21850085237513774052871 32775127856270661079307)
            ·
              refine ⟨49162691784405991618961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32775127856270661079307 49162691784405991618961)
              ·
                refine ⟨36872018838304493714221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49162691784405991618961 36872018838304493714221)
                ·
                  refine ⟨13827007064364185142833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36872018838304493714221 13827007064364185142833)
                  ·
                    rfl

theorem cell20_30294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_30294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30294 prefixEnd_30294 := by exact prefixLift 30294
  have htrace : WordTrace (prefixWord ++ tailWord_30294) baseStart_30294 baseEnd_30294 := by
    simpa [prefixWord, tailWord_30294, baseEnd_30294] using wordTrace_append hprefix tailTrace_30294
  have hstable : (prefixWord ++ tailWord_30294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30294).length < 2 ^ (prefixWord ++ tailWord_30294).sum := by decide
  have hdescent : baseEnd_30294 < baseStart_30294 := by decide
  rcases family_descends (prefixWord ++ tailWord_30294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30309 : List Nat := [1, 3, 1, 3, 3, 2, 2, 1, 4]
def baseStart_30309 : Nat := 118140960795 + 30309 * 2 ^ 59
def prefixEnd_30309 : Nat := 4983230072969 + 3 ^ 40 * 30309 * 2
def baseEnd_30309 : Nat := 13833853473090799642771

theorem tailTrace_30309 : CollatzResearch.WordTrace tailWord_30309 prefixEnd_30309 13833853473090799642771 := by
  unfold tailWord_30309
  simp only [CollatzResearch.WordTrace]
  refine ⟨1105460047203144210197981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 736973364802096140131987 1105460047203144210197981)
  ·
    refine ⟨414547517701179078824243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1105460047203144210197981 414547517701179078824243)
    ·
      refine ⟨621821276551768618236365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414547517701179078824243 621821276551768618236365)
      ·
        refine ⟨233182978706913231838637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 621821276551768618236365 233182978706913231838637)
        ·
          refine ⟨87443617015092461939489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233182978706913231838637 87443617015092461939489)
          ·
            refine ⟨65582712761319346454617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87443617015092461939489 65582712761319346454617)
            ·
              refine ⟨49187034570989509840963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65582712761319346454617 49187034570989509840963)
              ·
                refine ⟨73780551856484264761445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49187034570989509840963 73780551856484264761445)
                ·
                  refine ⟨13833853473090799642771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73780551856484264761445 13833853473090799642771)
                  ·
                    rfl

theorem cell20_30309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_30309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30309 prefixEnd_30309 := by exact prefixLift 30309
  have htrace : WordTrace (prefixWord ++ tailWord_30309) baseStart_30309 baseEnd_30309 := by
    simpa [prefixWord, tailWord_30309, baseEnd_30309] using wordTrace_append hprefix tailTrace_30309
  have hstable : (prefixWord ++ tailWord_30309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30309).length < 2 ^ (prefixWord ++ tailWord_30309).sum := by decide
  have hdescent : baseEnd_30309 < baseStart_30309 := by decide
  rcases family_descends (prefixWord ++ tailWord_30309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30333 : List Nat := [1, 4, 1, 1, 4, 3, 2, 4]
def baseStart_30333 : Nat := 118140960795 + 30333 * 2 ^ 59
def prefixEnd_30333 : Nat := 4983230072969 + 3 ^ 40 * 30333 * 2
def baseEnd_30333 : Nat := 4614935909017794280891

theorem tailTrace_30333 : CollatzResearch.WordTrace tailWord_30333 prefixEnd_30333 4614935909017794280891 := by
  unfold tailWord_30333
  simp only [CollatzResearch.WordTrace]
  refine ⟨1106335399116196309071653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 737556932744130872714435 1106335399116196309071653)
  ·
    refine ⟨207437887334286807950935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1106335399116196309071653 207437887334286807950935)
    ·
      refine ⟨311156831001430211926403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207437887334286807950935 311156831001430211926403)
      ·
        refine ⟨466735246502145317889605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311156831001430211926403 466735246502145317889605)
        ·
          refine ⟨87512858719152247104301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 466735246502145317889605 87512858719152247104301)
          ·
            refine ⟨32817322019682092664113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87512858719152247104301 32817322019682092664113)
            ·
              refine ⟨24612991514761569498085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32817322019682092664113 24612991514761569498085)
              ·
                refine ⟨4614935909017794280891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24612991514761569498085 4614935909017794280891)
                ·
                  rfl

theorem cell20_30333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 4].length) (baseStart_30333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30333 prefixEnd_30333 := by exact prefixLift 30333
  have htrace : WordTrace (prefixWord ++ tailWord_30333) baseStart_30333 baseEnd_30333 := by
    simpa [prefixWord, tailWord_30333, baseEnd_30333] using wordTrace_append hprefix tailTrace_30333
  have hstable : (prefixWord ++ tailWord_30333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30333).length < 2 ^ (prefixWord ++ tailWord_30333).sum := by decide
  have hdescent : baseEnd_30333 < baseStart_30333 := by decide
  rcases family_descends (prefixWord ++ tailWord_30333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30364 : List Nat := [2, 2, 3, 2, 3, 2, 1, 1, 4]
def baseStart_30364 : Nat := 118140960795 + 30364 * 2 ^ 59
def prefixEnd_30364 : Nat := 4983230072969 + 3 ^ 40 * 30364 * 2
def baseEnd_30364 : Nat := 13858956971755052809213

theorem tailTrace_30364 : CollatzResearch.WordTrace tailWord_30364 prefixEnd_30364 13858956971755052809213 := by
  unfold tailWord_30364
  simp only [CollatzResearch.WordTrace]
  refine ⟨553733031001944301725073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 738310708002592402300097 553733031001944301725073)
  ·
    refine ⟨415299773251458226293805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 553733031001944301725073 415299773251458226293805)
    ·
      refine ⟨155737414969296834860177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415299773251458226293805 155737414969296834860177)
      ·
        refine ⟨116803061226972626145133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155737414969296834860177 116803061226972626145133)
        ·
          refine ⟨43801147960114734804425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116803061226972626145133 43801147960114734804425)
          ·
            refine ⟨32850860970086051103319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43801147960114734804425 32850860970086051103319)
            ·
              refine ⟨49276291455129076654979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32850860970086051103319 49276291455129076654979)
              ·
                refine ⟨73914437182693614982469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49276291455129076654979 73914437182693614982469)
                ·
                  refine ⟨13858956971755052809213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73914437182693614982469 13858956971755052809213)
                  ·
                    rfl

theorem cell20_30364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_30364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30364 prefixEnd_30364 := by exact prefixLift 30364
  have htrace : WordTrace (prefixWord ++ tailWord_30364) baseStart_30364 baseEnd_30364 := by
    simpa [prefixWord, tailWord_30364, baseEnd_30364] using wordTrace_append hprefix tailTrace_30364
  have hstable : (prefixWord ++ tailWord_30364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30364).length < 2 ^ (prefixWord ++ tailWord_30364).sum := by decide
  have hdescent : baseEnd_30364 < baseStart_30364 := by decide
  rcases family_descends (prefixWord ++ tailWord_30364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30423 : List Nat := [1, 1, 3, 2, 1, 3, 3, 4, 2]
def baseStart_30423 : Nat := 118140960795 + 30423 * 2 ^ 59
def prefixEnd_30423 : Nat := 4983230072969 + 3 ^ 40 * 30423 * 2
def baseEnd_30423 : Nat := 13885886179413069842305

theorem tailTrace_30423 : CollatzResearch.WordTrace tailWord_30423 prefixEnd_30423 13885886179413069842305 := by
  unfold tailWord_30423
  simp only [CollatzResearch.WordTrace]
  refine ⟨1109617968790141679847923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 739745312526761119898615 1109617968790141679847923)
  ·
    refine ⟨1664426953185212519771885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1109617968790141679847923 1664426953185212519771885)
    ·
      refine ⟨624160107444454694914457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1664426953185212519771885 624160107444454694914457)
      ·
        refine ⟨468120080583341021185843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 624160107444454694914457 468120080583341021185843)
        ·
          refine ⟨702180120875011531778765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468120080583341021185843 702180120875011531778765)
          ·
            refine ⟨263317545328129324417037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 702180120875011531778765 263317545328129324417037)
            ·
              refine ⟨98744079498048496656389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263317545328129324417037 98744079498048496656389)
              ·
                refine ⟨18514514905884093123073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98744079498048496656389 18514514905884093123073)
                ·
                  refine ⟨13885886179413069842305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18514514905884093123073 13885886179413069842305)
                  ·
                    rfl

theorem cell20_30423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 2].length) (baseStart_30423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30423 prefixEnd_30423 := by exact prefixLift 30423
  have htrace : WordTrace (prefixWord ++ tailWord_30423) baseStart_30423 baseEnd_30423 := by
    simpa [prefixWord, tailWord_30423, baseEnd_30423] using wordTrace_append hprefix tailTrace_30423
  have hstable : (prefixWord ++ tailWord_30423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30423).length < 2 ^ (prefixWord ++ tailWord_30423).sum := by decide
  have hdescent : baseEnd_30423 < baseStart_30423 := by decide
  rcases family_descends (prefixWord ++ tailWord_30423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30437 : List Nat := [1, 3, 1, 4, 1, 1, 1, 5, 3]
def baseStart_30437 : Nat := 118140960795 + 30437 * 2 ^ 59
def prefixEnd_30437 : Nat := 4983230072969 + 3 ^ 40 * 30437 * 2
def baseEnd_30437 : Nat := 13892276160891243375581

theorem tailTrace_30437 : CollatzResearch.WordTrace tailWord_30437 prefixEnd_30437 13892276160891243375581 := by
  unfold tailWord_30437
  simp only [CollatzResearch.WordTrace]
  refine ⟨1110128590739422070857565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 740085727159614713905043 1110128590739422070857565)
  ·
    refine ⟨416298221527283276571587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1110128590739422070857565 416298221527283276571587)
    ·
      refine ⟨624447332290924914857381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416298221527283276571587 624447332290924914857381)
      ·
        refine ⟨117083874804548421535759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 624447332290924914857381 117083874804548421535759)
        ·
          refine ⟨175625812206822632303639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117083874804548421535759 175625812206822632303639)
          ·
            refine ⟨263438718310233948455459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175625812206822632303639 263438718310233948455459)
            ·
              refine ⟨395158077465350922683189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263438718310233948455459 395158077465350922683189)
              ·
                refine ⟨37046069762376649001549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 395158077465350922683189 37046069762376649001549)
                ·
                  refine ⟨13892276160891243375581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37046069762376649001549 13892276160891243375581)
                  ·
                    rfl

theorem cell20_30437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_30437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30437 prefixEnd_30437 := by exact prefixLift 30437
  have htrace : WordTrace (prefixWord ++ tailWord_30437) baseStart_30437 baseEnd_30437 := by
    simpa [prefixWord, tailWord_30437, baseEnd_30437] using wordTrace_append hprefix tailTrace_30437
  have hstable : (prefixWord ++ tailWord_30437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30437).length < 2 ^ (prefixWord ++ tailWord_30437).sum := by decide
  have hdescent : baseEnd_30437 < baseStart_30437 := by decide
  rcases family_descends (prefixWord ++ tailWord_30437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30458 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 5]
def baseStart_30458 : Nat := 118140960795 + 30458 * 2 ^ 59
def prefixEnd_30458 : Nat := 4983230072969 + 3 ^ 40 * 30458 * 2
def baseEnd_30458 : Nat := 13901861133108503675495

theorem tailTrace_30458 : CollatzResearch.WordTrace tailWord_30458 prefixEnd_30458 13901861133108503675495 := by
  unfold tailWord_30458
  simp only [CollatzResearch.WordTrace]
  refine ⟨277723630915835664343007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 740596349108895104914685 277723630915835664343007)
  ·
    refine ⟨416585446373753496514511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277723630915835664343007 416585446373753496514511)
    ·
      refine ⟨624878169560630244771767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416585446373753496514511 624878169560630244771767)
      ·
        refine ⟨937317254340945367157651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624878169560630244771767 937317254340945367157651)
        ·
          refine ⟨1405975881511418050736477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 937317254340945367157651 1405975881511418050736477)
          ·
            refine ⟨527240955566781769026179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1405975881511418050736477 527240955566781769026179)
            ·
              refine ⟨790861433350172653539269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527240955566781769026179 790861433350172653539269)
              ·
                refine ⟨148286518753157372538613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 790861433350172653539269 148286518753157372538613)
                ·
                  refine ⟨13901861133108503675495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 148286518753157372538613 13901861133108503675495)
                  ·
                    rfl

theorem cell20_30458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_30458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30458 prefixEnd_30458 := by exact prefixLift 30458
  have htrace : WordTrace (prefixWord ++ tailWord_30458) baseStart_30458 baseEnd_30458 := by
    simpa [prefixWord, tailWord_30458, baseEnd_30458] using wordTrace_append hprefix tailTrace_30458
  have hstable : (prefixWord ++ tailWord_30458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30458).length < 2 ^ (prefixWord ++ tailWord_30458).sum := by decide
  have hdescent : baseEnd_30458 < baseStart_30458 := by decide
  rcases family_descends (prefixWord ++ tailWord_30458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30471 : List Nat := [1, 1, 4, 4, 2, 2, 1, 2, 3]
def baseStart_30471 : Nat := 118140960795 + 30471 * 2 ^ 59
def prefixEnd_30471 : Nat := 4983230072969 + 3 ^ 40 * 30471 * 2
def baseEnd_30471 : Nat := 13907794687338236242109

theorem tailTrace_30471 : CollatzResearch.WordTrace tailWord_30471 prefixEnd_30471 13907794687338236242109 := by
  unfold tailWord_30471
  simp only [CollatzResearch.WordTrace]
  refine ⟨1111368672616245877595267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 740912448410830585063511 1111368672616245877595267)
  ·
    refine ⟨1667053008924368816392901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1111368672616245877595267 1667053008924368816392901)
    ·
      refine ⟨312572439173319153073669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1667053008924368816392901 312572439173319153073669)
      ·
        refine ⟨58607332344997341201313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312572439173319153073669 58607332344997341201313)
        ·
          refine ⟨43955499258748005900985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58607332344997341201313 43955499258748005900985)
          ·
            refine ⟨32966624444061004425739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43955499258748005900985 32966624444061004425739)
            ·
              refine ⟨49449936666091506638609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32966624444061004425739 49449936666091506638609)
              ·
                refine ⟨37087452499568629978957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49449936666091506638609 37087452499568629978957)
                ·
                  refine ⟨13907794687338236242109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37087452499568629978957 13907794687338236242109)
                  ·
                    rfl

theorem cell20_30471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 3].length) (baseStart_30471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30471 prefixEnd_30471 := by exact prefixLift 30471
  have htrace : WordTrace (prefixWord ++ tailWord_30471) baseStart_30471 baseEnd_30471 := by
    simpa [prefixWord, tailWord_30471, baseEnd_30471] using wordTrace_append hprefix tailTrace_30471
  have hstable : (prefixWord ++ tailWord_30471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30471).length < 2 ^ (prefixWord ++ tailWord_30471).sum := by decide
  have hdescent : baseEnd_30471 < baseStart_30471 := by decide
  rcases family_descends (prefixWord ++ tailWord_30471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30475 : List Nat := [1, 1, 1, 1, 5, 1, 5, 2, 3]
def baseStart_30475 : Nat := 118140960795 + 30475 * 2 ^ 59
def prefixEnd_30475 : Nat := 4983230072969 + 3 ^ 40 * 30475 * 2
def baseEnd_30475 : Nat := 13909620396332000108759

theorem tailTrace_30475 : CollatzResearch.WordTrace tailWord_30475 prefixEnd_30475 13909620396332000108759 := by
  unfold tailWord_30475
  simp only [CollatzResearch.WordTrace]
  refine ⟨1111514564601754560740879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 741009709734503040493919 1111514564601754560740879)
  ·
    refine ⟨1667271846902631841111319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1111514564601754560740879 1667271846902631841111319)
    ·
      refine ⟨2500907770353947761666979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1667271846902631841111319 2500907770353947761666979)
      ·
        refine ⟨3751361655530921642500469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2500907770353947761666979 3751361655530921642500469)
        ·
          refine ⟨351690155206023903984419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3751361655530921642500469 351690155206023903984419)
          ·
            refine ⟨527535232809035855976629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351690155206023903984419 527535232809035855976629)
            ·
              refine ⟨49456428075847111497809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 527535232809035855976629 49456428075847111497809)
              ·
                refine ⟨37092321056885333623357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49456428075847111497809 37092321056885333623357)
                ·
                  refine ⟨13909620396332000108759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37092321056885333623357 13909620396332000108759)
                  ·
                    rfl

theorem cell20_30475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 3].length) (baseStart_30475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30475 prefixEnd_30475 := by exact prefixLift 30475
  have htrace : WordTrace (prefixWord ++ tailWord_30475) baseStart_30475 baseEnd_30475 := by
    simpa [prefixWord, tailWord_30475, baseEnd_30475] using wordTrace_append hprefix tailTrace_30475
  have hstable : (prefixWord ++ tailWord_30475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30475).length < 2 ^ (prefixWord ++ tailWord_30475).sum := by decide
  have hdescent : baseEnd_30475 < baseStart_30475 := by decide
  rcases family_descends (prefixWord ++ tailWord_30475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30492 : List Nat := [2, 2, 3, 1, 1, 2, 5, 1, 3]
def baseStart_30492 : Nat := 118140960795 + 30492 * 2 ^ 59
def prefixEnd_30492 : Nat := 4983230072969 + 3 ^ 40 * 30492 * 2
def baseEnd_30492 : Nat := 13917379659555496542023

theorem tailTrace_30492 : CollatzResearch.WordTrace tailWord_30492 prefixEnd_30492 13917379659555496542023 := by
  unfold tailWord_30492
  simp only [CollatzResearch.WordTrace]
  refine ⟨556067302770083232054865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 741423070360110976073153 556067302770083232054865)
  ·
    refine ⟨417050477077562424041149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 556067302770083232054865 417050477077562424041149)
    ·
      refine ⟨156393928904085909015431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417050477077562424041149 156393928904085909015431)
      ·
        refine ⟨234590893356128863523147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156393928904085909015431 234590893356128863523147)
        ·
          refine ⟨351886340034193295284721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234590893356128863523147 351886340034193295284721)
          ·
            refine ⟨263914755025644971463541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351886340034193295284721 263914755025644971463541)
            ·
              refine ⟨24742008283654216074707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 263914755025644971463541 24742008283654216074707)
              ·
                refine ⟨37113012425481324112061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24742008283654216074707 37113012425481324112061)
                ·
                  refine ⟨13917379659555496542023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37113012425481324112061 13917379659555496542023)
                  ·
                    rfl

theorem cell20_30492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_30492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30492 prefixEnd_30492 := by exact prefixLift 30492
  have htrace : WordTrace (prefixWord ++ tailWord_30492) baseStart_30492 baseEnd_30492 := by
    simpa [prefixWord, tailWord_30492, baseEnd_30492] using wordTrace_append hprefix tailTrace_30492
  have hstable : (prefixWord ++ tailWord_30492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30492).length < 2 ^ (prefixWord ++ tailWord_30492).sum := by decide
  have hdescent : baseEnd_30492 < baseStart_30492 := by decide
  rcases family_descends (prefixWord ++ tailWord_30492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30582 : List Nat := [5, 1, 1, 3, 2, 8]
def baseStart_30582 : Nat := 118140960795 + 30582 * 2 ^ 59
def prefixEnd_30582 : Nat := 4983230072969 + 3 ^ 40 * 30582 * 2
def baseEnd_30582 : Nat := 516979930070932723765

theorem tailTrace_30582 : CollatzResearch.WordTrace tailWord_30582 prefixEnd_30582 516979930070932723765 := by
  unfold tailWord_30582
  simp only [CollatzResearch.WordTrace]
  refine ⟨69713573450881989680375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 743611450142741223257333 69713573450881989680375)
  ·
    refine ⟨104570360176322984520563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69713573450881989680375 104570360176322984520563)
    ·
      refine ⟨156855540264484476780845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104570360176322984520563 156855540264484476780845)
      ·
        refine ⟨58820827599181678792817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156855540264484476780845 58820827599181678792817)
        ·
          refine ⟨44115620699386259094613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58820827599181678792817 44115620699386259094613)
          ·
            refine ⟨516979930070932723765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 44115620699386259094613 516979930070932723765)
            ·
              rfl

theorem cell20_30582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 8].length) (baseStart_30582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30582 prefixEnd_30582 := by exact prefixLift 30582
  have htrace : WordTrace (prefixWord ++ tailWord_30582) baseStart_30582 baseEnd_30582 := by
    simpa [prefixWord, tailWord_30582, baseEnd_30582] using wordTrace_append hprefix tailTrace_30582
  have hstable : (prefixWord ++ tailWord_30582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30582).length < 2 ^ (prefixWord ++ tailWord_30582).sum := by decide
  have hdescent : baseEnd_30582 < baseStart_30582 := by decide
  rcases family_descends (prefixWord ++ tailWord_30582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30599 : List Nat := [1, 1, 4, 2, 5, 1, 1, 5]
def baseStart_30599 : Nat := 118140960795 + 30599 * 2 ^ 59
def prefixEnd_30599 : Nat := 4983230072969 + 3 ^ 40 * 30599 * 2
def baseEnd_30599 : Nat := 4655405791712893324973

theorem tailTrace_30599 : CollatzResearch.WordTrace tailWord_30599 prefixEnd_30599 4655405791712893324973 := by
  unfold tailWord_30599
  simp only [CollatzResearch.WordTrace]
  refine ⟨1116037216152523738254851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 744024810768349158836567 1116037216152523738254851)
  ·
    refine ⟨1674055824228785607382277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1116037216152523738254851 1674055824228785607382277)
    ·
      refine ⟨313885467042897301384177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1674055824228785607382277 313885467042897301384177)
      ·
        refine ⟨235414100282172976038133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313885467042897301384177 235414100282172976038133)
        ·
          refine ⟨22070071901453716503575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 235414100282172976038133 22070071901453716503575)
          ·
            refine ⟨33105107852180574755363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22070071901453716503575 33105107852180574755363)
            ·
              refine ⟨49657661778270862133045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33105107852180574755363 49657661778270862133045)
              ·
                refine ⟨4655405791712893324973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49657661778270862133045 4655405791712893324973)
                ·
                  rfl

theorem cell20_30599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 5].length) (baseStart_30599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30599 prefixEnd_30599 := by exact prefixLift 30599
  have htrace : WordTrace (prefixWord ++ tailWord_30599) baseStart_30599 baseEnd_30599 := by
    simpa [prefixWord, tailWord_30599, baseEnd_30599] using wordTrace_append hprefix tailTrace_30599
  have hstable : (prefixWord ++ tailWord_30599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30599).length < 2 ^ (prefixWord ++ tailWord_30599).sum := by decide
  have hdescent : baseEnd_30599 < baseStart_30599 := by decide
  rcases family_descends (prefixWord ++ tailWord_30599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30617 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 6]
def baseStart_30617 : Nat := 118140960795 + 30617 * 2 ^ 59
def prefixEnd_30617 : Nat := 4983230072969 + 3 ^ 40 * 30617 * 2
def baseEnd_30617 : Nat := 13974433065610617374845

theorem tailTrace_30617 : CollatzResearch.WordTrace tailWord_30617 prefixEnd_30617 13974433065610617374845 := by
  unfold tailWord_30617
  simp only [CollatzResearch.WordTrace]
  refine ⟨1116693730087312812410105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 744462486724875208273403 1116693730087312812410105)
  ·
    refine ⟨837520297565484609307579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1116693730087312812410105 837520297565484609307579)
    ·
      refine ⟨1256280446348226913961369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 837520297565484609307579 1256280446348226913961369)
      ·
        refine ⟨942210334761170185471027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1256280446348226913961369 942210334761170185471027)
        ·
          refine ⟨1413315502141755278206541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 942210334761170185471027 1413315502141755278206541)
          ·
            refine ⟨529993313303158229327453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1413315502141755278206541 529993313303158229327453)
            ·
              refine ⟨198747492488684335997795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 529993313303158229327453 198747492488684335997795)
              ·
                refine ⟨298121238733026503996693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198747492488684335997795 298121238733026503996693)
                ·
                  refine ⟨13974433065610617374845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 298121238733026503996693 13974433065610617374845)
                  ·
                    rfl

theorem cell20_30617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_30617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30617 prefixEnd_30617 := by exact prefixLift 30617
  have htrace : WordTrace (prefixWord ++ tailWord_30617) baseStart_30617 baseEnd_30617 := by
    simpa [prefixWord, tailWord_30617, baseEnd_30617] using wordTrace_append hprefix tailTrace_30617
  have hstable : (prefixWord ++ tailWord_30617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30617).length < 2 ^ (prefixWord ++ tailWord_30617).sum := by decide
  have hdescent : baseEnd_30617 < baseStart_30617 := by decide
  rcases family_descends (prefixWord ++ tailWord_30617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30641 : List Nat := [1, 2, 2, 4, 2, 2, 7]
def baseStart_30641 : Nat := 118140960795 + 30641 * 2 ^ 59
def prefixEnd_30641 : Nat := 4983230072969 + 3 ^ 40 * 30641 * 2
def baseEnd_30641 : Nat := 1553931924397022286083

theorem tailTrace_30641 : CollatzResearch.WordTrace tailWord_30641 prefixEnd_30641 1553931924397022286083 := by
  unfold tailWord_30641
  simp only [CollatzResearch.WordTrace]
  refine ⟨1117569082000364911283777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 745046054666909940855851 1117569082000364911283777)
  ·
    refine ⟨838176811500273683462833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1117569082000364911283777 838176811500273683462833)
    ·
      refine ⟨628632608625205262597125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 838176811500273683462833 628632608625205262597125)
      ·
        refine ⟨117868614117225986736961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 628632608625205262597125 117868614117225986736961)
        ·
          refine ⟨88401460587919490052721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117868614117225986736961 88401460587919490052721)
          ·
            refine ⟨66301095440939617539541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88401460587919490052721 66301095440939617539541)
            ·
              refine ⟨1553931924397022286083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 66301095440939617539541 1553931924397022286083)
              ·
                rfl

theorem cell20_30641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 7].length) (baseStart_30641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30641 prefixEnd_30641 := by exact prefixLift 30641
  have htrace : WordTrace (prefixWord ++ tailWord_30641) baseStart_30641 baseEnd_30641 := by
    simpa [prefixWord, tailWord_30641, baseEnd_30641] using wordTrace_append hprefix tailTrace_30641
  have hstable : (prefixWord ++ tailWord_30641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30641).length < 2 ^ (prefixWord ++ tailWord_30641).sum := by decide
  have hdescent : baseEnd_30641 < baseStart_30641 := by decide
  rcases family_descends (prefixWord ++ tailWord_30641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30648 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 5]
def baseStart_30648 : Nat := 118140960795 + 30648 * 2 ^ 59
def prefixEnd_30648 : Nat := 4983230072969 + 3 ^ 40 * 30648 * 2
def baseEnd_30648 : Nat := 13988582310312287341385

theorem tailTrace_30648 : CollatzResearch.WordTrace tailWord_30648 prefixEnd_30648 13988582310312287341385 := by
  unfold tailWord_30648
  simp only [CollatzResearch.WordTrace]
  refine ⟨558912196487502553394299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 745216261983336737859065 558912196487502553394299)
  ·
    refine ⟨838368294731253830091449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 558912196487502553394299 838368294731253830091449)
    ·
      refine ⟨628776221048440372568587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 838368294731253830091449 628776221048440372568587)
      ·
        refine ⟨943164331572660558852881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628776221048440372568587 943164331572660558852881)
        ·
          refine ⟨707373248679495419139661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 943164331572660558852881 707373248679495419139661)
          ·
            refine ⟨265264968254810782177373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 707373248679495419139661 265264968254810782177373)
            ·
              refine ⟨99474363095554043316515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265264968254810782177373 99474363095554043316515)
              ·
                refine ⟨149211544643331064974773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99474363095554043316515 149211544643331064974773)
                ·
                  refine ⟨13988582310312287341385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149211544643331064974773 13988582310312287341385)
                  ·
                    rfl

theorem cell20_30648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_30648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30648 prefixEnd_30648 := by exact prefixLift 30648
  have htrace : WordTrace (prefixWord ++ tailWord_30648) baseStart_30648 baseEnd_30648 := by
    simpa [prefixWord, tailWord_30648, baseEnd_30648] using wordTrace_append hprefix tailTrace_30648
  have hstable : (prefixWord ++ tailWord_30648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30648).length < 2 ^ (prefixWord ++ tailWord_30648).sum := by decide
  have hdescent : baseEnd_30648 < baseStart_30648 := by decide
  rcases family_descends (prefixWord ++ tailWord_30648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30685 : List Nat := [1, 4, 3, 1, 3, 2, 1, 3, 2]
def baseStart_30685 : Nat := 118140960795 + 30685 * 2 ^ 59
def prefixEnd_30685 : Nat := 4983230072969 + 3 ^ 40 * 30685 * 2
def baseEnd_30685 : Nat := 14005470118504603107901

theorem tailTrace_30685 : CollatzResearch.WordTrace tailWord_30685 prefixEnd_30685 14005470118504603107901 := by
  unfold tailWord_30685
  simp only [CollatzResearch.WordTrace]
  refine ⟨1119173893840960425885509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 746115929227306950590339 1119173893840960425885509)
  ·
    refine ⟨209845105095180079853533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1119173893840960425885509 209845105095180079853533)
    ·
      refine ⟨78691914410692529945075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209845105095180079853533 78691914410692529945075)
      ·
        refine ⟨118037871616038794917613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78691914410692529945075 118037871616038794917613)
        ·
          refine ⟨44264201856014548094105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118037871616038794917613 44264201856014548094105)
          ·
            refine ⟨33198151392010911070579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44264201856014548094105 33198151392010911070579)
            ·
              refine ⟨49797227088016366605869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33198151392010911070579 49797227088016366605869)
              ·
                refine ⟨18673960158006137477201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49797227088016366605869 18673960158006137477201)
                ·
                  refine ⟨14005470118504603107901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18673960158006137477201 14005470118504603107901)
                  ·
                    rfl

theorem cell20_30685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_30685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30685 prefixEnd_30685 := by exact prefixLift 30685
  have htrace : WordTrace (prefixWord ++ tailWord_30685) baseStart_30685 baseEnd_30685 := by
    simpa [prefixWord, tailWord_30685, baseEnd_30685] using wordTrace_append hprefix tailTrace_30685
  have hstable : (prefixWord ++ tailWord_30685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30685).length < 2 ^ (prefixWord ++ tailWord_30685).sum := by decide
  have hdescent : baseEnd_30685 < baseStart_30685 := by decide
  rcases family_descends (prefixWord ++ tailWord_30685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30689 : List Nat := [1, 2, 3, 1, 2, 1, 5, 3, 2]
def baseStart_30689 : Nat := 118140960795 + 30689 * 2 ^ 59
def prefixEnd_30689 : Nat := 4983230072969 + 3 ^ 40 * 30689 * 2
def baseEnd_30689 : Nat := 14007295827498366974551

theorem tailTrace_30689 : CollatzResearch.WordTrace tailWord_30689 prefixEnd_30689 14007295827498366974551 := by
  unfold tailWord_30689
  simp only [CollatzResearch.WordTrace]
  refine ⟨1119319785826469109031121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 746213190550979406020747 1119319785826469109031121)
  ·
    refine ⟨839489839369851831773341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1119319785826469109031121 839489839369851831773341)
    ·
      refine ⟨314808689763694436915003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 839489839369851831773341 314808689763694436915003)
      ·
        refine ⟨472213034645541655372505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314808689763694436915003 472213034645541655372505)
        ·
          refine ⟨354159775984156241529379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472213034645541655372505 354159775984156241529379)
          ·
            refine ⟨531239663976234362294069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354159775984156241529379 531239663976234362294069)
            ·
              refine ⟨49803718497771971465069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 531239663976234362294069 49803718497771971465069)
              ·
                refine ⟨18676394436664489299401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49803718497771971465069 18676394436664489299401)
                ·
                  refine ⟨14007295827498366974551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18676394436664489299401 14007295827498366974551)
                  ·
                    rfl

theorem cell20_30689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 2].length) (baseStart_30689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30689 prefixEnd_30689 := by exact prefixLift 30689
  have htrace : WordTrace (prefixWord ++ tailWord_30689) baseStart_30689 baseEnd_30689 := by
    simpa [prefixWord, tailWord_30689, baseEnd_30689] using wordTrace_append hprefix tailTrace_30689
  have hstable : (prefixWord ++ tailWord_30689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30689).length < 2 ^ (prefixWord ++ tailWord_30689).sum := by decide
  have hdescent : baseEnd_30689 < baseStart_30689 := by decide
  rcases family_descends (prefixWord ++ tailWord_30689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30731 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 6]
def baseStart_30731 : Nat := 118140960795 + 30731 * 2 ^ 59
def prefixEnd_30731 : Nat := 4983230072969 + 3 ^ 40 * 30731 * 2
def baseEnd_30731 : Nat := 14026465771932887574379

theorem tailTrace_30731 : CollatzResearch.WordTrace tailWord_30731 prefixEnd_30731 14026465771932887574379 := by
  unfold tailWord_30731
  simp only [CollatzResearch.WordTrace]
  refine ⟨1120851651674310282060047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 747234434449540188040031 1120851651674310282060047)
  ·
    refine ⟨1681277477511465423090071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1120851651674310282060047 1681277477511465423090071)
    ·
      refine ⟨2521916216267198134635107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1681277477511465423090071 2521916216267198134635107)
      ·
        refine ⟨3782874324400797201952661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2521916216267198134635107 3782874324400797201952661)
        ·
          refine ⟨177322233956287368841531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3782874324400797201952661 177322233956287368841531)
          ·
            refine ⟨265983350934431053262297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177322233956287368841531 265983350934431053262297)
            ·
              refine ⟨199487513200823289946723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265983350934431053262297 199487513200823289946723)
              ·
                refine ⟨299231269801234934920085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199487513200823289946723 299231269801234934920085)
                ·
                  refine ⟨14026465771932887574379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 299231269801234934920085 14026465771932887574379)
                  ·
                    rfl

theorem cell20_30731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_30731 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30731 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30731 prefixEnd_30731 := by exact prefixLift 30731
  have htrace : WordTrace (prefixWord ++ tailWord_30731) baseStart_30731 baseEnd_30731 := by
    simpa [prefixWord, tailWord_30731, baseEnd_30731] using wordTrace_append hprefix tailTrace_30731
  have hstable : (prefixWord ++ tailWord_30731).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30731).length < 2 ^ (prefixWord ++ tailWord_30731).sum := by decide
  have hdescent : baseEnd_30731 < baseStart_30731 := by decide
  rcases family_descends (prefixWord ++ tailWord_30731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30793 : List Nat := [1, 2, 1, 1, 2, 2, 7, 4]
def baseStart_30793 : Nat := 118140960795 + 30793 * 2 ^ 59
def prefixEnd_30793 : Nat := 4983230072969 + 3 ^ 40 * 30793 * 2
def baseEnd_30793 : Nat := 4684921420445409169153

theorem tailTrace_30793 : CollatzResearch.WordTrace tailWord_30793 prefixEnd_30793 4684921420445409169153 := by
  unfold tailWord_30793
  simp only [CollatzResearch.WordTrace]
  refine ⟨1123112977449694870817033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 748741984966463247211355 1123112977449694870817033)
  ·
    refine ⟨842334733087271153112775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1123112977449694870817033 842334733087271153112775)
    ·
      refine ⟨1263502099630906729669163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 842334733087271153112775 1263502099630906729669163)
      ·
        refine ⟨1895253149446360094503745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1263502099630906729669163 1895253149446360094503745)
        ·
          refine ⟨1421439862084770070877809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1895253149446360094503745 1421439862084770070877809)
          ·
            refine ⟨1066079896563577553158357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1421439862084770070877809 1066079896563577553158357)
            ·
              refine ⟨24986247575708848902149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1066079896563577553158357 24986247575708848902149)
              ·
                refine ⟨4684921420445409169153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24986247575708848902149 4684921420445409169153)
                ·
                  rfl

theorem cell20_30793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 4].length) (baseStart_30793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30793 prefixEnd_30793 := by exact prefixLift 30793
  have htrace : WordTrace (prefixWord ++ tailWord_30793) baseStart_30793 baseEnd_30793 := by
    simpa [prefixWord, tailWord_30793, baseEnd_30793] using wordTrace_append hprefix tailTrace_30793
  have hstable : (prefixWord ++ tailWord_30793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30793).length < 2 ^ (prefixWord ++ tailWord_30793).sum := by decide
  have hdescent : baseEnd_30793 < baseStart_30793 := by decide
  rcases family_descends (prefixWord ++ tailWord_30793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30813 : List Nat := [1, 4, 4, 1, 1, 3, 1, 2, 3]
def baseStart_30813 : Nat := 118140960795 + 30813 * 2 ^ 59
def prefixEnd_30813 : Nat := 4983230072969 + 3 ^ 40 * 30813 * 2
def baseEnd_30813 : Nat := 14063892806305046840711

theorem tailTrace_30813 : CollatzResearch.WordTrace tailWord_30813 prefixEnd_30813 14063892806305046840711 := by
  unfold tailWord_30813
  simp only [CollatzResearch.WordTrace]
  refine ⟨1123842437377238286545093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 749228291584825524363395 1123842437377238286545093)
  ·
    refine ⟨210720457008232178727205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1123842437377238286545093 210720457008232178727205)
    ·
      refine ⟨39510085689043533511351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210720457008232178727205 39510085689043533511351)
      ·
        refine ⟨59265128533565300267027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39510085689043533511351 59265128533565300267027)
        ·
          refine ⟨88897692800347950400541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59265128533565300267027 88897692800347950400541)
          ·
            refine ⟨33336634800130481400203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88897692800347950400541 33336634800130481400203)
            ·
              refine ⟨50004952200195722100305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33336634800130481400203 50004952200195722100305)
              ·
                refine ⟨37503714150146791575229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50004952200195722100305 37503714150146791575229)
                ·
                  refine ⟨14063892806305046840711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37503714150146791575229 14063892806305046840711)
                  ·
                    rfl

theorem cell20_30813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_30813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30813 prefixEnd_30813 := by exact prefixLift 30813
  have htrace : WordTrace (prefixWord ++ tailWord_30813) baseStart_30813 baseEnd_30813 := by
    simpa [prefixWord, tailWord_30813, baseEnd_30813] using wordTrace_append hprefix tailTrace_30813
  have hstable : (prefixWord ++ tailWord_30813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30813).length < 2 ^ (prefixWord ++ tailWord_30813).sum := by decide
  have hdescent : baseEnd_30813 < baseStart_30813 := by decide
  rcases family_descends (prefixWord ++ tailWord_30813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30834 : List Nat := [3, 2, 1, 2, 2, 3, 3, 1, 3]
def baseStart_30834 : Nat := 118140960795 + 30834 * 2 ^ 59
def prefixEnd_30834 : Nat := 4983230072969 + 3 ^ 40 * 30834 * 2
def baseEnd_30834 : Nat := 14073477778522307140625

theorem tailTrace_30834 : CollatzResearch.WordTrace tailWord_30834 prefixEnd_30834 14073477778522307140625 := by
  unfold tailWord_30834
  simp only [CollatzResearch.WordTrace]
  refine ⟨281152092575289718264889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 749738913534105915373037 281152092575289718264889)
  ·
    refine ⟨210864069431467288698667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281152092575289718264889 210864069431467288698667)
    ·
      refine ⟨316296104147200933048001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210864069431467288698667 316296104147200933048001)
      ·
        refine ⟨237222078110400699786001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316296104147200933048001 237222078110400699786001)
        ·
          refine ⟨177916558582800524839501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237222078110400699786001 177916558582800524839501)
          ·
            refine ⟨66718709468550196814813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177916558582800524839501 66718709468550196814813)
            ·
              refine ⟨25019516050706323805555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66718709468550196814813 25019516050706323805555)
              ·
                refine ⟨37529274076059485708333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25019516050706323805555 37529274076059485708333)
                ·
                  refine ⟨14073477778522307140625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37529274076059485708333 14073477778522307140625)
                  ·
                    rfl

theorem cell20_30834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_30834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30834 prefixEnd_30834 := by exact prefixLift 30834
  have htrace : WordTrace (prefixWord ++ tailWord_30834) baseStart_30834 baseEnd_30834 := by
    simpa [prefixWord, tailWord_30834, baseEnd_30834] using wordTrace_append hprefix tailTrace_30834
  have hstable : (prefixWord ++ tailWord_30834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30834).length < 2 ^ (prefixWord ++ tailWord_30834).sum := by decide
  have hdescent : baseEnd_30834 < baseStart_30834 := by decide
  rcases family_descends (prefixWord ++ tailWord_30834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30858 : List Nat := [3, 1, 2, 3, 1, 4, 1, 3, 2]
def baseStart_30858 : Nat := 118140960795 + 30858 * 2 ^ 59
def prefixEnd_30858 : Nat := 4983230072969 + 3 ^ 40 * 30858 * 2
def baseEnd_30858 : Nat := 14084432032484890340527

theorem tailTrace_30858 : CollatzResearch.WordTrace tailWord_30858 prefixEnd_30858 14084432032484890340527 := by
  unfold tailWord_30858
  simp only [CollatzResearch.WordTrace]
  refine ⟨281370930553552742983307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 750322481476140647955485 281370930553552742983307)
  ·
    refine ⟨422056395830329114474961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281370930553552742983307 422056395830329114474961)
    ·
      refine ⟨316542296872746835856221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422056395830329114474961 316542296872746835856221)
      ·
        refine ⟨118703361327280063446083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316542296872746835856221 118703361327280063446083)
        ·
          refine ⟨178055041990920095169125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118703361327280063446083 178055041990920095169125)
          ·
            refine ⟨33385320373297517844211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178055041990920095169125 33385320373297517844211)
            ·
              refine ⟨50077980559946276766317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33385320373297517844211 50077980559946276766317)
              ·
                refine ⟨18779242709979853787369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50077980559946276766317 18779242709979853787369)
                ·
                  refine ⟨14084432032484890340527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18779242709979853787369 14084432032484890340527)
                  ·
                    rfl

theorem cell20_30858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 2].length) (baseStart_30858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30858 prefixEnd_30858 := by exact prefixLift 30858
  have htrace : WordTrace (prefixWord ++ tailWord_30858) baseStart_30858 baseEnd_30858 := by
    simpa [prefixWord, tailWord_30858, baseEnd_30858] using wordTrace_append hprefix tailTrace_30858
  have hstable : (prefixWord ++ tailWord_30858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30858).length < 2 ^ (prefixWord ++ tailWord_30858).sum := by decide
  have hdescent : baseEnd_30858 < baseStart_30858 := by decide
  rcases family_descends (prefixWord ++ tailWord_30858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30876 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 5]
def baseStart_30876 : Nat := 118140960795 + 30876 * 2 ^ 59
def prefixEnd_30876 : Nat := 4983230072969 + 3 ^ 40 * 30876 * 2
def baseEnd_30876 : Nat := 14092647722956827740453

theorem tailTrace_30876 : CollatzResearch.WordTrace tailWord_30876 prefixEnd_30876 14092647722956827740453 := by
  unfold tailWord_30876
  simp only [CollatzResearch.WordTrace]
  refine ⟨563070118074500023044241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 750760157432666697392321 563070118074500023044241)
  ·
    refine ⟨422302588555875017283181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 563070118074500023044241 422302588555875017283181)
    ·
      refine ⟨158363470708453131481193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 422302588555875017283181 158363470708453131481193)
      ·
        refine ⟨118772603031339848610895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158363470708453131481193 118772603031339848610895)
        ·
          refine ⟨178158904547009772916343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118772603031339848610895 178158904547009772916343)
          ·
            refine ⟨267238356820514659374515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178158904547009772916343 267238356820514659374515)
            ·
              refine ⟨400857535230771989061773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267238356820514659374515 400857535230771989061773)
              ·
                refine ⟨150321575711539495898165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 400857535230771989061773 150321575711539495898165)
                ·
                  refine ⟨14092647722956827740453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150321575711539495898165 14092647722956827740453)
                  ·
                    rfl

theorem cell20_30876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_30876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30876 prefixEnd_30876 := by exact prefixLift 30876
  have htrace : WordTrace (prefixWord ++ tailWord_30876) baseStart_30876 baseEnd_30876 := by
    simpa [prefixWord, tailWord_30876, baseEnd_30876] using wordTrace_append hprefix tailTrace_30876
  have hstable : (prefixWord ++ tailWord_30876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30876).length < 2 ^ (prefixWord ++ tailWord_30876).sum := by decide
  have hdescent : baseEnd_30876 < baseStart_30876 := by decide
  rcases family_descends (prefixWord ++ tailWord_30876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30879 : List Nat := [1, 1, 2, 6, 1, 3, 1, 1, 4]
def baseStart_30879 : Nat := 118140960795 + 30879 * 2 ^ 59
def prefixEnd_30879 : Nat := 4983230072969 + 3 ^ 40 * 30879 * 2
def baseEnd_30879 : Nat := 14094017004702150640441

theorem tailTrace_30879 : CollatzResearch.WordTrace tailWord_30879 prefixEnd_30879 14094017004702150640441 := by
  unfold tailWord_30879
  simp only [CollatzResearch.WordTrace]
  refine ⟨1126249655138131558447691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 750833103425421038965127 1126249655138131558447691)
  ·
    refine ⟨1689374482707197337671537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1126249655138131558447691 1689374482707197337671537)
    ·
      refine ⟨1267030862030398003253653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1689374482707197337671537 1267030862030398003253653)
      ·
        refine ⟨59392071657674906402515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1267030862030398003253653 59392071657674906402515)
        ·
          refine ⟨89088107486512359603773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59392071657674906402515 89088107486512359603773)
          ·
            refine ⟨33408040307442134851415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89088107486512359603773 33408040307442134851415)
            ·
              refine ⟨50112060461163202277123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33408040307442134851415 50112060461163202277123)
              ·
                refine ⟨75168090691744803415685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50112060461163202277123 75168090691744803415685)
                ·
                  refine ⟨14094017004702150640441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75168090691744803415685 14094017004702150640441)
                  ·
                    rfl

theorem cell20_30879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 4].length) (baseStart_30879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30879 prefixEnd_30879 := by exact prefixLift 30879
  have htrace : WordTrace (prefixWord ++ tailWord_30879) baseStart_30879 baseEnd_30879 := by
    simpa [prefixWord, tailWord_30879, baseEnd_30879] using wordTrace_append hprefix tailTrace_30879
  have hstable : (prefixWord ++ tailWord_30879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30879).length < 2 ^ (prefixWord ++ tailWord_30879).sum := by decide
  have hdescent : baseEnd_30879 < baseStart_30879 := by decide
  rcases family_descends (prefixWord ++ tailWord_30879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30924 : List Nat := [2, 2, 1, 6, 2, 7]
def baseStart_30924 : Nat := 118140960795 + 30924 * 2 ^ 59
def prefixEnd_30924 : Nat := 4983230072969 + 3 ^ 40 * 30924 * 2
def baseEnd_30924 : Nat := 522761341884518301491

theorem tailTrace_30924 : CollatzResearch.WordTrace tailWord_30924 prefixEnd_30924 522761341884518301491 := by
  unfold tailWord_30924
  simp only [CollatzResearch.WordTrace]
  refine ⟨563945469987552121917913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 751927293316736162557217 563945469987552121917913)
  ·
    refine ⟨422959102490664091438435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 563945469987552121917913 422959102490664091438435)
    ·
      refine ⟨634438653735996137157653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422959102490664091438435 634438653735996137157653)
      ·
        refine ⟨29739311893874818929265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 634438653735996137157653 29739311893874818929265)
        ·
          refine ⟨22304483920406114196949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29739311893874818929265 22304483920406114196949)
          ·
            refine ⟨522761341884518301491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 22304483920406114196949 522761341884518301491)
            ·
              rfl

theorem cell20_30924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 7].length) (baseStart_30924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30924 prefixEnd_30924 := by exact prefixLift 30924
  have htrace : WordTrace (prefixWord ++ tailWord_30924) baseStart_30924 baseEnd_30924 := by
    simpa [prefixWord, tailWord_30924, baseEnd_30924] using wordTrace_append hprefix tailTrace_30924
  have hstable : (prefixWord ++ tailWord_30924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30924).length < 2 ^ (prefixWord ++ tailWord_30924).sum := by decide
  have hdescent : baseEnd_30924 < baseStart_30924 := by decide
  rcases family_descends (prefixWord ++ tailWord_30924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30959 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 6]
def baseStart_30959 : Nat := 118140960795 + 30959 * 2 ^ 59
def prefixEnd_30959 : Nat := 4983230072969 + 3 ^ 40 * 30959 * 2
def baseEnd_30959 : Nat := 14130531184577427973447

theorem tailTrace_30959 : CollatzResearch.WordTrace tailWord_30959 prefixEnd_30959 14130531184577427973447 := by
  unfold tailWord_30959
  simp only [CollatzResearch.WordTrace]
  refine ⟨1129167494848305221359931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 752778329898870147573287 1129167494848305221359931)
  ·
    refine ⟨1693751242272457832039897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1129167494848305221359931 1693751242272457832039897)
    ·
      refine ⟨1270313431704343374029923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1693751242272457832039897 1270313431704343374029923)
      ·
        refine ⟨1905470147556515061044885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1270313431704343374029923 1905470147556515061044885)
        ·
          refine ⟨89318913166711643486479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1905470147556515061044885 89318913166711643486479)
          ·
            refine ⟨133978369750067465229719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89318913166711643486479 133978369750067465229719)
            ·
              refine ⟨200967554625101197844579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133978369750067465229719 200967554625101197844579)
              ·
                refine ⟨301451331937651796766869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200967554625101197844579 301451331937651796766869)
                ·
                  refine ⟨14130531184577427973447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 301451331937651796766869 14130531184577427973447)
                  ·
                    rfl

theorem cell20_30959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 6].length) (baseStart_30959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30959 prefixEnd_30959 := by exact prefixLift 30959
  have htrace : WordTrace (prefixWord ++ tailWord_30959) baseStart_30959 baseEnd_30959 := by
    simpa [prefixWord, tailWord_30959, baseEnd_30959] using wordTrace_append hprefix tailTrace_30959
  have hstable : (prefixWord ++ tailWord_30959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30959).length < 2 ^ (prefixWord ++ tailWord_30959).sum := by decide
  have hdescent : baseEnd_30959 < baseStart_30959 := by decide
  rcases family_descends (prefixWord ++ tailWord_30959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30962 : List Nat := [3, 2, 1, 3, 2, 2, 3, 4]
def baseStart_30962 : Nat := 118140960795 + 30962 * 2 ^ 59
def prefixEnd_30962 : Nat := 4983230072969 + 3 ^ 40 * 30962 * 2
def baseEnd_30962 : Nat := 4710633488774250291145

theorem tailTrace_30962 : CollatzResearch.WordTrace tailWord_30962 prefixEnd_30962 4710633488774250291145 := by
  unfold tailWord_30962
  simp only [CollatzResearch.WordTrace]
  refine ⟨282319228459359183429785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 752851275891624489146093 282319228459359183429785)
  ·
    refine ⟨211739421344519387572339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282319228459359183429785 211739421344519387572339)
    ·
      refine ⟨317609132016779081358509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211739421344519387572339 317609132016779081358509)
      ·
        refine ⟨119103424506292155509441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317609132016779081358509 119103424506292155509441)
        ·
          refine ⟨89327568379719116632081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119103424506292155509441 89327568379719116632081)
          ·
            refine ⟨66995676284789337474061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89327568379719116632081 66995676284789337474061)
            ·
              refine ⟨25123378606796001552773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66995676284789337474061 25123378606796001552773)
              ·
                refine ⟨4710633488774250291145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25123378606796001552773 4710633488774250291145)
                ·
                  rfl

theorem cell20_30962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_30962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30962 prefixEnd_30962 := by exact prefixLift 30962
  have htrace : WordTrace (prefixWord ++ tailWord_30962) baseStart_30962 baseEnd_30962 := by
    simpa [prefixWord, tailWord_30962, baseEnd_30962] using wordTrace_append hprefix tailTrace_30962
  have hstable : (prefixWord ++ tailWord_30962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30962).length < 2 ^ (prefixWord ++ tailWord_30962).sum := by decide
  have hdescent : baseEnd_30962 < baseStart_30962 := by decide
  rcases family_descends (prefixWord ++ tailWord_30962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30976 : List Nat := [2, 1, 1, 2, 1, 1, 5, 5, 2]
def baseStart_30976 : Nat := 118140960795 + 30976 * 2 ^ 59
def prefixEnd_30976 : Nat := 4983230072969 + 3 ^ 40 * 30976 * 2
def baseEnd_30976 : Nat := 14138290447800924406711

theorem tailTrace_30976 : CollatzResearch.WordTrace tailWord_30976 prefixEnd_30976 14138290447800924406711 := by
  unfold tailWord_30976
  simp only [CollatzResearch.WordTrace]
  refine ⟨564893767893358562364391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 753191690524478083152521 564893767893358562364391)
  ·
    refine ⟨847340651840037843546587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 564893767893358562364391 847340651840037843546587)
    ·
      refine ⟨1271010977760056765319881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 847340651840037843546587 1271010977760056765319881)
      ·
        refine ⟨953258233320042573989911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1271010977760056765319881 953258233320042573989911)
        ·
          refine ⟨1429887349980063860984867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 953258233320042573989911 1429887349980063860984867)
          ·
            refine ⟨2144831024970095791477301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1429887349980063860984867 2144831024970095791477301)
            ·
              refine ⟨201077908590946480450997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2144831024970095791477301 201077908590946480450997)
              ·
                refine ⟨18851053930401232542281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 201077908590946480450997 18851053930401232542281)
                ·
                  refine ⟨14138290447800924406711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18851053930401232542281 14138290447800924406711)
                  ·
                    rfl

theorem cell20_30976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 2].length) (baseStart_30976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30976 prefixEnd_30976 := by exact prefixLift 30976
  have htrace : WordTrace (prefixWord ++ tailWord_30976) baseStart_30976 baseEnd_30976 := by
    simpa [prefixWord, tailWord_30976, baseEnd_30976] using wordTrace_append hprefix tailTrace_30976
  have hstable : (prefixWord ++ tailWord_30976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30976).length < 2 ^ (prefixWord ++ tailWord_30976).sum := by decide
  have hdescent : baseEnd_30976 < baseStart_30976 := by decide
  rcases family_descends (prefixWord ++ tailWord_30976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30990 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_30990 : Nat := 118140960795 + 30990 * 2 ^ 59
def prefixEnd_30990 : Nat := 4983230072969 + 3 ^ 40 * 30990 * 2
def baseEnd_30990 : Nat := 14144680429279097939987

theorem tailTrace_30990 : CollatzResearch.WordTrace tailWord_30990 prefixEnd_30990 14144680429279097939987 := by
  unfold tailWord_30990
  simp only [CollatzResearch.WordTrace]
  refine ⟨141287269716999689467303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 753532105157331677158949 141287269716999689467303)
  ·
    refine ⟨211930904575499534200955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141287269716999689467303 211930904575499534200955)
    ·
      refine ⟨317896356863249301301433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211930904575499534200955 317896356863249301301433)
      ·
        refine ⟨238422267647436975976075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317896356863249301301433 238422267647436975976075)
        ·
          refine ⟨357633401471155463964113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238422267647436975976075 357633401471155463964113)
          ·
            refine ⟨268225051103366597973085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357633401471155463964113 268225051103366597973085)
            ·
              refine ⟨100584394163762474239907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268225051103366597973085 100584394163762474239907)
              ·
                refine ⟨150876591245643711359861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100584394163762474239907 150876591245643711359861)
                ·
                  refine ⟨14144680429279097939987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150876591245643711359861 14144680429279097939987)
                  ·
                    rfl

theorem cell20_30990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_30990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30990 prefixEnd_30990 := by exact prefixLift 30990
  have htrace : WordTrace (prefixWord ++ tailWord_30990) baseStart_30990 baseEnd_30990 := by
    simpa [prefixWord, tailWord_30990, baseEnd_30990] using wordTrace_append hprefix tailTrace_30990
  have hstable : (prefixWord ++ tailWord_30990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30990).length < 2 ^ (prefixWord ++ tailWord_30990).sum := by decide
  have hdescent : baseEnd_30990 < baseStart_30990 := by decide
  rcases family_descends (prefixWord ++ tailWord_30990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30997 : List Nat := [1, 3, 2, 1, 2, 1, 3, 3, 4]
def baseStart_30997 : Nat := 118140960795 + 30997 * 2 ^ 59
def prefixEnd_30997 : Nat := 4983230072969 + 3 ^ 40 * 30997 * 2
def baseEnd_30997 : Nat := 14147875420018184706625

theorem tailTrace_30997 : CollatzResearch.WordTrace tailWord_30997 prefixEnd_30997 14147875420018184706625 := by
  unfold tailWord_30997
  simp only [CollatzResearch.WordTrace]
  refine ⟨1130553468710637711243245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 753702312473758474162163 1130553468710637711243245)
  ·
    refine ⟨423957550766489141716217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1130553468710637711243245 423957550766489141716217)
    ·
      refine ⟨317968163074866856287163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423957550766489141716217 317968163074866856287163)
      ·
        refine ⟨476952244612300284430745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317968163074866856287163 476952244612300284430745)
        ·
          refine ⟨357714183459225213323059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476952244612300284430745 357714183459225213323059)
          ·
            refine ⟨536571275188837819984589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357714183459225213323059 536571275188837819984589)
            ·
              refine ⟨201214228195814182494221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 536571275188837819984589 201214228195814182494221)
              ·
                refine ⟨75455335573430318435333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201214228195814182494221 75455335573430318435333)
                ·
                  refine ⟨14147875420018184706625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75455335573430318435333 14147875420018184706625)
                  ·
                    rfl

theorem cell20_30997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_30997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_30997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_30997 prefixEnd_30997 := by exact prefixLift 30997
  have htrace : WordTrace (prefixWord ++ tailWord_30997) baseStart_30997 baseEnd_30997 := by
    simpa [prefixWord, tailWord_30997, baseEnd_30997] using wordTrace_append hprefix tailTrace_30997
  have hstable : (prefixWord ++ tailWord_30997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30997).length < 2 ^ (prefixWord ++ tailWord_30997).sum := by decide
  have hdescent : baseEnd_30997 < baseStart_30997 := by decide
  rcases family_descends (prefixWord ++ tailWord_30997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31004 : List Nat := [2, 2, 3, 1, 1, 1, 1, 9]
def baseStart_31004 : Nat := 118140960795 + 31004 * 2 ^ 59
def prefixEnd_31004 : Nat := 4983230072969 + 3 ^ 40 * 31004 * 2
def baseEnd_31004 : Nat := 4717023470252423824421

theorem tailTrace_31004 : CollatzResearch.WordTrace tailWord_31004 prefixEnd_31004 4717023470252423824421 := by
  unfold tailWord_31004
  simp only [CollatzResearch.WordTrace]
  refine ⟨565404389842638953374033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 753872519790185271165377 565404389842638953374033)
  ·
    refine ⟨424053292381979215030525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 565404389842638953374033 424053292381979215030525)
    ·
      refine ⟨159019984643242205636447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424053292381979215030525 159019984643242205636447)
      ·
        refine ⟨238529976964863308454671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159019984643242205636447 238529976964863308454671)
        ·
          refine ⟨357794965447294962682007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238529976964863308454671 357794965447294962682007)
          ·
            refine ⟨536692448170942444023011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357794965447294962682007 536692448170942444023011)
            ·
              refine ⟨805038672256413666034517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536692448170942444023011 805038672256413666034517)
              ·
                refine ⟨4717023470252423824421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 805038672256413666034517 4717023470252423824421)
                ·
                  rfl

theorem cell20_31004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_31004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31004 prefixEnd_31004 := by exact prefixLift 31004
  have htrace : WordTrace (prefixWord ++ tailWord_31004) baseStart_31004 baseEnd_31004 := by
    simpa [prefixWord, tailWord_31004, baseEnd_31004] using wordTrace_append hprefix tailTrace_31004
  have hstable : (prefixWord ++ tailWord_31004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31004).length < 2 ^ (prefixWord ++ tailWord_31004).sum := by decide
  have hdescent : baseEnd_31004 < baseStart_31004 := by decide
  rcases family_descends (prefixWord ++ tailWord_31004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31087 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 5]
def baseStart_31087 : Nat := 118140960795 + 31087 * 2 ^ 59
def prefixEnd_31087 : Nat := 4983230072969 + 3 ^ 40 * 31087 * 2
def baseEnd_31087 : Nat := 14188953872377871706257

theorem tailTrace_31087 : CollatzResearch.WordTrace tailWord_31087 prefixEnd_31087 14188953872377871706257 := by
  unfold tailWord_31087
  simp only [CollatzResearch.WordTrace]
  refine ⟨1133836038384583082019515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 755890692256388721346343 1133836038384583082019515)
  ·
    refine ⟨1700754057576874623029273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1133836038384583082019515 1700754057576874623029273)
    ·
      refine ⟨1275565543182655967271955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1700754057576874623029273 1275565543182655967271955)
      ·
        refine ⟨1913348314773983950907933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1275565543182655967271955 1913348314773983950907933)
        ·
          refine ⟨717505618040243981590475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1913348314773983950907933 717505618040243981590475)
          ·
            refine ⟨1076258427060365972385713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717505618040243981590475 1076258427060365972385713)
            ·
              refine ⟨807193820295274479289285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1076258427060365972385713 807193820295274479289285)
              ·
                refine ⟨151348841305363964866741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 807193820295274479289285 151348841305363964866741)
                ·
                  refine ⟨14188953872377871706257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151348841305363964866741 14188953872377871706257)
                  ·
                    rfl

theorem cell20_31087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_31087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31087 prefixEnd_31087 := by exact prefixLift 31087
  have htrace : WordTrace (prefixWord ++ tailWord_31087) baseStart_31087 baseEnd_31087 := by
    simpa [prefixWord, tailWord_31087, baseEnd_31087] using wordTrace_append hprefix tailTrace_31087
  have hstable : (prefixWord ++ tailWord_31087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31087).length < 2 ^ (prefixWord ++ tailWord_31087).sum := by decide
  have hdescent : baseEnd_31087 < baseStart_31087 := by decide
  rcases family_descends (prefixWord ++ tailWord_31087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31107 : List Nat := [1, 1, 1, 3, 6, 1, 1, 4, 2]
def baseStart_31107 : Nat := 118140960795 + 31107 * 2 ^ 59
def prefixEnd_31107 : Nat := 4983230072969 + 3 ^ 40 * 31107 * 2
def baseEnd_31107 : Nat := 14198082417346691039509

theorem tailTrace_31107 : CollatzResearch.WordTrace tailWord_31107 prefixEnd_31107 14198082417346691039509 := by
  unfold tailWord_31107
  simp only [CollatzResearch.WordTrace]
  refine ⟨1134565498312126497747575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 756376998874750998498383 1134565498312126497747575)
  ·
    refine ⟨1701848247468189746621363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1134565498312126497747575 1701848247468189746621363)
    ·
      refine ⟨2552772371202284619932045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1701848247468189746621363 2552772371202284619932045)
      ·
        refine ⟨957289639200856732474517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2552772371202284619932045 957289639200856732474517)
        ·
          refine ⟨44872951837540159334743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 957289639200856732474517 44872951837540159334743)
          ·
            refine ⟨67309427756310239002115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44872951837540159334743 67309427756310239002115)
            ·
              refine ⟨100964141634465358503173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67309427756310239002115 100964141634465358503173)
              ·
                refine ⟨18930776556462254719345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100964141634465358503173 18930776556462254719345)
                ·
                  refine ⟨14198082417346691039509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18930776556462254719345 14198082417346691039509)
                  ·
                    rfl

theorem cell20_31107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 2].length) (baseStart_31107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31107 prefixEnd_31107 := by exact prefixLift 31107
  have htrace : WordTrace (prefixWord ++ tailWord_31107) baseStart_31107 baseEnd_31107 := by
    simpa [prefixWord, tailWord_31107, baseEnd_31107] using wordTrace_append hprefix tailTrace_31107
  have hstable : (prefixWord ++ tailWord_31107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31107).length < 2 ^ (prefixWord ++ tailWord_31107).sum := by decide
  have hdescent : baseEnd_31107 < baseStart_31107 := by decide
  rcases family_descends (prefixWord ++ tailWord_31107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31111 : List Nat := [1, 1, 4, 2, 2, 1, 2, 3, 4]
def baseStart_31111 : Nat := 118140960795 + 31111 * 2 ^ 59
def prefixEnd_31111 : Nat := 4983230072969 + 3 ^ 40 * 31111 * 2
def baseEnd_31111 : Nat := 14199908126340454906159

theorem tailTrace_31111 : CollatzResearch.WordTrace tailWord_31111 prefixEnd_31111 14199908126340454906159 := by
  unfold tailWord_31111
  simp only [CollatzResearch.WordTrace]
  refine ⟨1134711390297635180893187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 756474260198423453928791 1134711390297635180893187)
  ·
    refine ⟨1702067085446452771339781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1134711390297635180893187 1702067085446452771339781)
    ·
      refine ⟨319137578521209894626209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1702067085446452771339781 319137578521209894626209)
      ·
        refine ⟨239353183890907420969657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319137578521209894626209 239353183890907420969657)
        ·
          refine ⟨179514887918180565727243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239353183890907420969657 179514887918180565727243)
          ·
            refine ⟨269272331877270848590865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179514887918180565727243 269272331877270848590865)
            ·
              refine ⟨201954248907953136443149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269272331877270848590865 201954248907953136443149)
              ·
                refine ⟨75732843340482426166181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201954248907953136443149 75732843340482426166181)
                ·
                  refine ⟨14199908126340454906159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75732843340482426166181 14199908126340454906159)
                  ·
                    rfl

theorem cell20_31111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 4].length) (baseStart_31111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31111 prefixEnd_31111 := by exact prefixLift 31111
  have htrace : WordTrace (prefixWord ++ tailWord_31111) baseStart_31111 baseEnd_31111 := by
    simpa [prefixWord, tailWord_31111, baseEnd_31111] using wordTrace_append hprefix tailTrace_31111
  have hstable : (prefixWord ++ tailWord_31111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31111).length < 2 ^ (prefixWord ++ tailWord_31111).sum := by decide
  have hdescent : baseEnd_31111 < baseStart_31111 := by decide
  rcases family_descends (prefixWord ++ tailWord_31111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31125 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 7]
def baseStart_31125 : Nat := 118140960795 + 31125 * 2 ^ 59
def prefixEnd_31125 : Nat := 4983230072969 + 3 ^ 40 * 31125 * 2
def baseEnd_31125 : Nat := 14206298107818628439435

theorem tailTrace_31125 : CollatzResearch.WordTrace tailWord_31125 prefixEnd_31125 14206298107818628439435 := by
  unfold tailWord_31125
  simp only [CollatzResearch.WordTrace]
  refine ⟨1135222012246915571902829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 756814674831277047935219 1135222012246915571902829)
  ·
    refine ⟨425708254592593339463561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1135222012246915571902829 425708254592593339463561)
    ·
      refine ⟨319281190944445004597671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425708254592593339463561 319281190944445004597671)
      ·
        refine ⟨478921786416667506896507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319281190944445004597671 478921786416667506896507)
        ·
          refine ⟨718382679625001260344761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478921786416667506896507 718382679625001260344761)
          ·
            refine ⟨538787009718750945258571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 718382679625001260344761 538787009718750945258571)
            ·
              refine ⟨808180514578126417887857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538787009718750945258571 808180514578126417887857)
              ·
                refine ⟨606135385933594813415893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 808180514578126417887857 606135385933594813415893)
                ·
                  refine ⟨14206298107818628439435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 606135385933594813415893 14206298107818628439435)
                  ·
                    rfl

theorem cell20_31125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_31125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31125 prefixEnd_31125 := by exact prefixLift 31125
  have htrace : WordTrace (prefixWord ++ tailWord_31125) baseStart_31125 baseEnd_31125 := by
    simpa [prefixWord, tailWord_31125, baseEnd_31125] using wordTrace_append hprefix tailTrace_31125
  have hstable : (prefixWord ++ tailWord_31125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31125).length < 2 ^ (prefixWord ++ tailWord_31125).sum := by decide
  have hdescent : baseEnd_31125 < baseStart_31125 := by decide
  rcases family_descends (prefixWord ++ tailWord_31125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31128 : List Nat := [2, 1, 2, 5, 1, 2, 1, 2, 4]
def baseStart_31128 : Nat := 118140960795 + 31128 * 2 ^ 59
def prefixEnd_31128 : Nat := 4983230072969 + 3 ^ 40 * 31128 * 2
def baseEnd_31128 : Nat := 14207667389563951339423

theorem tailTrace_31128 : CollatzResearch.WordTrace tailWord_31128 prefixEnd_31128 14207667389563951339423 := by
  unfold tailWord_31128
  simp only [CollatzResearch.WordTrace]
  refine ⟨567665715618023542131019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 756887620824031389508025 567665715618023542131019)
  ·
    refine ⟨851498573427035313196529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 567665715618023542131019 851498573427035313196529)
    ·
      refine ⟨638623930070276484897397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 851498573427035313196529 638623930070276484897397)
      ·
        refine ⟨59870993444088420459131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 638623930070276484897397 59870993444088420459131)
        ·
          refine ⟨89806490166132630688697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59870993444088420459131 89806490166132630688697)
          ·
            refine ⟨67354867624599473016523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89806490166132630688697 67354867624599473016523)
            ·
              refine ⟨101032301436899209524785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67354867624599473016523 101032301436899209524785)
              ·
                refine ⟨75774226077674407143589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101032301436899209524785 75774226077674407143589)
                ·
                  refine ⟨14207667389563951339423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75774226077674407143589 14207667389563951339423)
                  ·
                    rfl

theorem cell20_31128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_31128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31128 prefixEnd_31128 := by exact prefixLift 31128
  have htrace : WordTrace (prefixWord ++ tailWord_31128) baseStart_31128 baseEnd_31128 := by
    simpa [prefixWord, tailWord_31128, baseEnd_31128] using wordTrace_append hprefix tailTrace_31128
  have hstable : (prefixWord ++ tailWord_31128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31128).length < 2 ^ (prefixWord ++ tailWord_31128).sum := by decide
  have hdescent : baseEnd_31128 < baseStart_31128 := by decide
  rcases family_descends (prefixWord ++ tailWord_31128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31135 : List Nat := [1, 1, 2, 5, 1, 1, 5, 4]
def baseStart_31135 : Nat := 118140960795 + 31135 * 2 ^ 59
def prefixEnd_31135 : Nat := 4983230072969 + 3 ^ 40 * 31135 * 2
def baseEnd_31135 : Nat := 4736954126767679368687

theorem tailTrace_31135 : CollatzResearch.WordTrace tailWord_31135 prefixEnd_31135 4736954126767679368687 := by
  unfold tailWord_31135
  simp only [CollatzResearch.WordTrace]
  refine ⟨1135586742210687279766859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 757057828140458186511239 1135586742210687279766859)
  ·
    refine ⟨1703380113316030919650289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1135586742210687279766859 1703380113316030919650289)
    ·
      refine ⟨1277535084987023189737717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1703380113316030919650289 1277535084987023189737717)
      ·
        refine ⟨119768914217533424037911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1277535084987023189737717 119768914217533424037911)
        ·
          refine ⟨179653371326300136056867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119768914217533424037911 179653371326300136056867)
          ·
            refine ⟨269480056989450204085301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179653371326300136056867 269480056989450204085301)
            ·
              refine ⟨25263755342760956632997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 269480056989450204085301 25263755342760956632997)
              ·
                refine ⟨4736954126767679368687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25263755342760956632997 4736954126767679368687)
                ·
                  rfl

theorem cell20_31135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 4].length) (baseStart_31135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31135 prefixEnd_31135 := by exact prefixLift 31135
  have htrace : WordTrace (prefixWord ++ tailWord_31135) baseStart_31135 baseEnd_31135 := by
    simpa [prefixWord, tailWord_31135, baseEnd_31135] using wordTrace_append hprefix tailTrace_31135
  have hstable : (prefixWord ++ tailWord_31135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31135).length < 2 ^ (prefixWord ++ tailWord_31135).sum := by decide
  have hdescent : baseEnd_31135 < baseStart_31135 := by decide
  rcases family_descends (prefixWord ++ tailWord_31135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31159 : List Nat := [1, 1, 3, 1, 3, 5, 1, 2, 3]
def baseStart_31159 : Nat := 118140960795 + 31159 * 2 ^ 59
def prefixEnd_31159 : Nat := 4983230072969 + 3 ^ 40 * 31159 * 2
def baseEnd_31159 : Nat := 14221816634265621305963

theorem tailTrace_31159 : CollatzResearch.WordTrace tailWord_31159 prefixEnd_31159 14221816634265621305963 := by
  unfold tailWord_31159
  simp only [CollatzResearch.WordTrace]
  refine ⟨1136462094123739378640531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 757641396082492919093687 1136462094123739378640531)
  ·
    refine ⟨1704693141185609067960797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1136462094123739378640531 1704693141185609067960797)
    ·
      refine ⟨639259927944603400485299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1704693141185609067960797 639259927944603400485299)
      ·
        refine ⟨958889891916905100727949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639259927944603400485299 958889891916905100727949)
        ·
          refine ⟨359583709468839412772981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 958889891916905100727949 359583709468839412772981)
          ·
            refine ⟨33710972762703694947467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 359583709468839412772981 33710972762703694947467)
            ·
              refine ⟨50566459144055542421201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33710972762703694947467 50566459144055542421201)
              ·
                refine ⟨37924844358041656815901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50566459144055542421201 37924844358041656815901)
                ·
                  refine ⟨14221816634265621305963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37924844358041656815901 14221816634265621305963)
                  ·
                    rfl

theorem cell20_31159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 3].length) (baseStart_31159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31159 prefixEnd_31159 := by exact prefixLift 31159
  have htrace : WordTrace (prefixWord ++ tailWord_31159) baseStart_31159 baseEnd_31159 := by
    simpa [prefixWord, tailWord_31159, baseEnd_31159] using wordTrace_append hprefix tailTrace_31159
  have hstable : (prefixWord ++ tailWord_31159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31159).length < 2 ^ (prefixWord ++ tailWord_31159).sum := by decide
  have hdescent : baseEnd_31159 < baseStart_31159 := by decide
  rcases family_descends (prefixWord ++ tailWord_31159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31186 : List Nat := [3, 2, 2, 4, 2, 1, 2, 4]
def baseStart_31186 : Nat := 118140960795 + 31186 * 2 ^ 59
def prefixEnd_31186 : Nat := 4983230072969 + 3 ^ 40 * 31186 * 2
def baseEnd_31186 : Nat := 4744713389991175801951

theorem tailTrace_31186 : CollatzResearch.WordTrace tailWord_31186 prefixEnd_31186 4744713389991175801951 := by
  unfold tailWord_31186
  simp only [CollatzResearch.WordTrace]
  refine ⟨284361716256480747468353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 758297910017281993248941 284361716256480747468353)
  ·
    refine ⟨213271287192360560601265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284361716256480747468353 213271287192360560601265)
    ·
      refine ⟨159953465394270420450949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213271287192360560601265 159953465394270420450949)
      ·
        refine ⟨29991274761425703834553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159953465394270420450949 29991274761425703834553)
        ·
          refine ⟨22493456071069277875915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29991274761425703834553 22493456071069277875915)
          ·
            refine ⟨33740184106603916813873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22493456071069277875915 33740184106603916813873)
            ·
              refine ⟨25305138079952937610405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33740184106603916813873 25305138079952937610405)
              ·
                refine ⟨4744713389991175801951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25305138079952937610405 4744713389991175801951)
                ·
                  rfl

theorem cell20_31186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_31186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31186 prefixEnd_31186 := by exact prefixLift 31186
  have htrace : WordTrace (prefixWord ++ tailWord_31186) baseStart_31186 baseEnd_31186 := by
    simpa [prefixWord, tailWord_31186, baseEnd_31186] using wordTrace_append hprefix tailTrace_31186
  have hstable : (prefixWord ++ tailWord_31186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31186).length < 2 ^ (prefixWord ++ tailWord_31186).sum := by decide
  have hdescent : baseEnd_31186 < baseStart_31186 := by decide
  rcases family_descends (prefixWord ++ tailWord_31186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31194 : List Nat := [3, 1, 1, 2, 3, 1, 3, 6]
def baseStart_31194 : Nat := 118140960795 + 31194 * 2 ^ 59
def prefixEnd_31194 : Nat := 4983230072969 + 3 ^ 40 * 31194 * 2
def baseEnd_31194 : Nat := 4745930529320351713051

theorem tailTrace_31194 : CollatzResearch.WordTrace tailWord_31194 prefixEnd_31194 4745930529320351713051 := by
  unfold tailWord_31194
  simp only [CollatzResearch.WordTrace]
  refine ⟨284434662249235089041159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 758492432664626904109757 284434662249235089041159)
  ·
    refine ⟨426651993373852633561739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284434662249235089041159 426651993373852633561739)
    ·
      refine ⟨639977990060778950342609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426651993373852633561739 639977990060778950342609)
      ·
        refine ⟨479983492545584212756957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 639977990060778950342609 479983492545584212756957)
        ·
          refine ⟨179993809704594079783859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 479983492545584212756957 179993809704594079783859)
          ·
            refine ⟨269990714556891119675789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179993809704594079783859 269990714556891119675789)
            ·
              refine ⟨101246517958834169878421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269990714556891119675789 101246517958834169878421)
              ·
                refine ⟨4745930529320351713051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101246517958834169878421 4745930529320351713051)
                ·
                  rfl

theorem cell20_31194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_31194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31194 prefixEnd_31194 := by exact prefixLift 31194
  have htrace : WordTrace (prefixWord ++ tailWord_31194) baseStart_31194 baseEnd_31194 := by
    simpa [prefixWord, tailWord_31194, baseEnd_31194] using wordTrace_append hprefix tailTrace_31194
  have hstable : (prefixWord ++ tailWord_31194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31194).length < 2 ^ (prefixWord ++ tailWord_31194).sum := by decide
  have hdescent : baseEnd_31194 < baseStart_31194 := by decide
  rcases family_descends (prefixWord ++ tailWord_31194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31201 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 7]
def baseStart_31201 : Nat := 118140960795 + 31201 * 2 ^ 59
def prefixEnd_31201 : Nat := 4983230072969 + 3 ^ 40 * 31201 * 2
def baseEnd_31201 : Nat := 14240986578700141905791

theorem tailTrace_31201 : CollatzResearch.WordTrace tailWord_31201 prefixEnd_31201 14240986578700141905791 := by
  unfold tailWord_31201
  simp only [CollatzResearch.WordTrace]
  refine ⟨1137993959971580551669457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 758662639981053701112971 1137993959971580551669457)
  ·
    refine ⟨853495469978685413752093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1137993959971580551669457 853495469978685413752093)
    ·
      refine ⟨320060801242007030157035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 853495469978685413752093 320060801242007030157035)
      ·
        refine ⟨480091201863010545235553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320060801242007030157035 480091201863010545235553)
        ·
          refine ⟨360068401397257908926665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480091201863010545235553 360068401397257908926665)
          ·
            refine ⟨270051301047943431694999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360068401397257908926665 270051301047943431694999)
            ·
              refine ⟨405076951571915147542499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270051301047943431694999 405076951571915147542499)
              ·
                refine ⟨607615427357872721313749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405076951571915147542499 607615427357872721313749)
                ·
                  refine ⟨14240986578700141905791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 607615427357872721313749 14240986578700141905791)
                  ·
                    rfl

theorem cell20_31201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_31201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31201 prefixEnd_31201 := by exact prefixLift 31201
  have htrace : WordTrace (prefixWord ++ tailWord_31201) baseStart_31201 baseEnd_31201 := by
    simpa [prefixWord, tailWord_31201, baseEnd_31201] using wordTrace_append hprefix tailTrace_31201
  have hstable : (prefixWord ++ tailWord_31201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31201).length < 2 ^ (prefixWord ++ tailWord_31201).sum := by decide
  have hdescent : baseEnd_31201 < baseStart_31201 := by decide
  rcases family_descends (prefixWord ++ tailWord_31201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31225 : List Nat := [1, 2, 1, 3, 1, 2, 5, 1, 4]
def baseStart_31225 : Nat := 118140960795 + 31225 * 2 ^ 59
def prefixEnd_31225 : Nat := 4983230072969 + 3 ^ 40 * 31225 * 2
def baseEnd_31225 : Nat := 14251940832662725105693

theorem tailTrace_31225 : CollatzResearch.WordTrace tailWord_31225 prefixEnd_31225 14251940832662725105693 := by
  unfold tailWord_31225
  simp only [CollatzResearch.WordTrace]
  refine ⟨1138869311884632650543129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 759246207923088433695419 1138869311884632650543129)
  ·
    refine ⟨854151983913474487907347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1138869311884632650543129 854151983913474487907347)
    ·
      refine ⟨1281227975870211731861021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 854151983913474487907347 1281227975870211731861021)
      ·
        refine ⟨480460490951329399447883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1281227975870211731861021 480460490951329399447883)
        ·
          refine ⟨720690736426994099171825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480460490951329399447883 720690736426994099171825)
          ·
            refine ⟨540518052320245574378869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 720690736426994099171825 540518052320245574378869)
            ·
              refine ⟨50673567405023022598019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 540518052320245574378869 50673567405023022598019)
              ·
                refine ⟨76010351107534533897029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50673567405023022598019 76010351107534533897029)
                ·
                  refine ⟨14251940832662725105693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76010351107534533897029 14251940832662725105693)
                  ·
                    rfl

theorem cell20_31225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_31225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31225 prefixEnd_31225 := by exact prefixLift 31225
  have htrace : WordTrace (prefixWord ++ tailWord_31225) baseStart_31225 baseEnd_31225 := by
    simpa [prefixWord, tailWord_31225, baseEnd_31225] using wordTrace_append hprefix tailTrace_31225
  have hstable : (prefixWord ++ tailWord_31225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31225).length < 2 ^ (prefixWord ++ tailWord_31225).sum := by decide
  have hdescent : baseEnd_31225 < baseStart_31225 := by decide
  rcases family_descends (prefixWord ++ tailWord_31225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31300 : List Nat := [2, 3, 5, 1, 1, 1, 3, 4]
def baseStart_31300 : Nat := 118140960795 + 31300 * 2 ^ 59
def prefixEnd_31300 : Nat := 4983230072969 + 3 ^ 40 * 31300 * 2
def baseEnd_31300 : Nat := 4762057625431932535129

theorem tailTrace_31300 : CollatzResearch.WordTrace tailWord_31300 prefixEnd_31300 4762057625431932535129 := by
  unfold tailWord_31300
  simp only [CollatzResearch.WordTrace]
  refine ⟨570802393306460229761677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 761069857741946973015569 570802393306460229761677)
  ·
    refine ⟨214050897489922586160629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 570802393306460229761677 214050897489922586160629)
    ·
      refine ⟨20067271639680242452559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214050897489922586160629 20067271639680242452559)
      ·
        refine ⟨30100907459520363678839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20067271639680242452559 30100907459520363678839)
        ·
          refine ⟨45151361189280545518259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30100907459520363678839 45151361189280545518259)
          ·
            refine ⟨67727041783920818277389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45151361189280545518259 67727041783920818277389)
            ·
              refine ⟨25397640668970306854021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67727041783920818277389 25397640668970306854021)
              ·
                refine ⟨4762057625431932535129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25397640668970306854021 4762057625431932535129)
                ·
                  rfl

theorem cell20_31300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 4].length) (baseStart_31300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31300 prefixEnd_31300 := by exact prefixLift 31300
  have htrace : WordTrace (prefixWord ++ tailWord_31300) baseStart_31300 baseEnd_31300 := by
    simpa [prefixWord, tailWord_31300, baseEnd_31300] using wordTrace_append hprefix tailTrace_31300
  have hstable : (prefixWord ++ tailWord_31300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31300).length < 2 ^ (prefixWord ++ tailWord_31300).sum := by decide
  have hdescent : baseEnd_31300 < baseStart_31300 := by decide
  rcases family_descends (prefixWord ++ tailWord_31300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31301 : List Nat := [1, 3, 1, 1, 1, 6, 1, 2, 4]
def baseStart_31301 : Nat := 118140960795 + 31301 * 2 ^ 59
def prefixEnd_31301 : Nat := 4983230072969 + 3 ^ 40 * 31301 * 2
def baseEnd_31301 : Nat := 14286629303544238572049

theorem tailTrace_31301 : CollatzResearch.WordTrace tailWord_31301 prefixEnd_31301 14286629303544238572049 := by
  unfold tailWord_31301
  simp only [CollatzResearch.WordTrace]
  refine ⟨1141641259609297630309757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 761094173072865086873171 1141641259609297630309757)
  ·
    refine ⟨428115472353486611366159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1141641259609297630309757 428115472353486611366159)
    ·
      refine ⟨642173208530229917049239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428115472353486611366159 642173208530229917049239)
      ·
        refine ⟨963259812795344875573859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642173208530229917049239 963259812795344875573859)
        ·
          refine ⟨1444889719193017313360789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 963259812795344875573859 1444889719193017313360789)
          ·
            refine ⟨67729205587172686563787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1444889719193017313360789 67729205587172686563787)
            ·
              refine ⟨101593808380759029845681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67729205587172686563787 101593808380759029845681)
              ·
                refine ⟨76195356285569272384261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101593808380759029845681 76195356285569272384261)
                ·
                  refine ⟨14286629303544238572049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76195356285569272384261 14286629303544238572049)
                  ·
                    rfl

theorem cell20_31301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_31301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31301 prefixEnd_31301 := by exact prefixLift 31301
  have htrace : WordTrace (prefixWord ++ tailWord_31301) baseStart_31301 baseEnd_31301 := by
    simpa [prefixWord, tailWord_31301, baseEnd_31301] using wordTrace_append hprefix tailTrace_31301
  have hstable : (prefixWord ++ tailWord_31301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31301).length < 2 ^ (prefixWord ++ tailWord_31301).sum := by decide
  have hdescent : baseEnd_31301 < baseStart_31301 := by decide
  rcases family_descends (prefixWord ++ tailWord_31301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31390 : List Nat := [4, 3, 1, 1, 1, 1, 5, 2, 2]
def baseStart_31390 : Nat := 118140960795 + 31390 * 2 ^ 59
def prefixEnd_31390 : Nat := 4983230072969 + 3 ^ 40 * 31390 * 2
def baseEnd_31390 : Nat := 14327251328655484605019

theorem tailTrace_31390 : CollatzResearch.WordTrace tailWord_31390 prefixEnd_31390 14327251328655484605019 := by
  unfold tailWord_31390
  simp only [CollatzResearch.WordTrace]
  refine ⟨143110919535858228787453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 763258237524577220199749 143110919535858228787453)
  ·
    refine ⟨53666594825946835795295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143110919535858228787453 53666594825946835795295)
    ·
      refine ⟨80499892238920253692943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53666594825946835795295 80499892238920253692943)
      ·
        refine ⟨120749838358380380539415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80499892238920253692943 120749838358380380539415)
        ·
          refine ⟨181124757537570570809123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120749838358380380539415 181124757537570570809123)
          ·
            refine ⟨271687136306355856213685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181124757537570570809123 271687136306355856213685)
            ·
              refine ⟨25470669028720861520033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 271687136306355856213685 25470669028720861520033)
              ·
                refine ⟨19103001771540646140025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25470669028720861520033 19103001771540646140025)
                ·
                  refine ⟨14327251328655484605019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19103001771540646140025 14327251328655484605019)
                  ·
                    rfl

theorem cell20_31390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_31390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31390 prefixEnd_31390 := by exact prefixLift 31390
  have htrace : WordTrace (prefixWord ++ tailWord_31390) baseStart_31390 baseEnd_31390 := by
    simpa [prefixWord, tailWord_31390, baseEnd_31390] using wordTrace_append hprefix tailTrace_31390
  have hstable : (prefixWord ++ tailWord_31390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31390).length < 2 ^ (prefixWord ++ tailWord_31390).sum := by decide
  have hdescent : baseEnd_31390 < baseStart_31390 := by decide
  rcases family_descends (prefixWord ++ tailWord_31390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31422 : List Nat := [4, 2, 1, 1, 2, 1, 1, 8]
def baseStart_31422 : Nat := 118140960795 + 31422 * 2 ^ 59
def prefixEnd_31422 : Nat := 4983230072969 + 3 ^ 40 * 31422 * 2
def baseEnd_31422 : Nat := 4780619000201865179407

theorem tailTrace_31422 : CollatzResearch.WordTrace tailWord_31422 prefixEnd_31422 4780619000201865179407 := by
  unfold tailWord_31422
  simp only [CollatzResearch.WordTrace]
  refine ⟨143256811521366911933065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 764036328113956863643013 143256811521366911933065)
  ·
    refine ⟨107442608641025183949799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143256811521366911933065 107442608641025183949799)
    ·
      refine ⟨161163912961537775924699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107442608641025183949799 161163912961537775924699)
      ·
        refine ⟨241745869442306663887049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161163912961537775924699 241745869442306663887049)
        ·
          refine ⟨181309402081729997915287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241745869442306663887049 181309402081729997915287)
          ·
            refine ⟨271964103122594996872931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181309402081729997915287 271964103122594996872931)
            ·
              refine ⟨407946154683892495309397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271964103122594996872931 407946154683892495309397)
              ·
                refine ⟨4780619000201865179407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 407946154683892495309397 4780619000201865179407)
                ·
                  rfl

theorem cell20_31422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_31422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31422 prefixEnd_31422 := by exact prefixLift 31422
  have htrace : WordTrace (prefixWord ++ tailWord_31422) baseStart_31422 baseEnd_31422 := by
    simpa [prefixWord, tailWord_31422, baseEnd_31422] using wordTrace_append hprefix tailTrace_31422
  have hstable : (prefixWord ++ tailWord_31422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31422).length < 2 ^ (prefixWord ++ tailWord_31422).sum := by decide
  have hdescent : baseEnd_31422 < baseStart_31422 := by decide
  rcases family_descends (prefixWord ++ tailWord_31422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31445 : List Nat := [1, 3, 2, 5, 1, 2, 2, 2, 2]
def baseStart_31445 : Nat := 118140960795 + 31445 * 2 ^ 59
def prefixEnd_31445 : Nat := 4983230072969 + 3 ^ 40 * 31445 * 2
def baseEnd_31445 : Nat := 14352354827319737771461

theorem tailTrace_31445 : CollatzResearch.WordTrace tailWord_31445 prefixEnd_31445 14352354827319737771461 := by
  unfold tailWord_31445
  simp only [CollatzResearch.WordTrace]
  refine ⟨1146893371087610223551789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 764595580725073482367859 1146893371087610223551789)
  ·
    refine ⟨430085014157853833831921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1146893371087610223551789 430085014157853833831921)
    ·
      refine ⟨322563760618390375373941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430085014157853833831921 322563760618390375373941)
      ·
        refine ⟨30240352557974097691307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 322563760618390375373941 30240352557974097691307)
        ·
          refine ⟨45360528836961146536961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30240352557974097691307 45360528836961146536961)
          ·
            refine ⟨34020396627720859902721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45360528836961146536961 34020396627720859902721)
            ·
              refine ⟨25515297470790644927041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34020396627720859902721 25515297470790644927041)
              ·
                refine ⟨19136473103092983695281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25515297470790644927041 19136473103092983695281)
                ·
                  refine ⟨14352354827319737771461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19136473103092983695281 14352354827319737771461)
                  ·
                    rfl

theorem cell20_31445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 2].length) (baseStart_31445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31445 prefixEnd_31445 := by exact prefixLift 31445
  have htrace : WordTrace (prefixWord ++ tailWord_31445) baseStart_31445 baseEnd_31445 := by
    simpa [prefixWord, tailWord_31445, baseEnd_31445] using wordTrace_append hprefix tailTrace_31445
  have hstable : (prefixWord ++ tailWord_31445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31445).length < 2 ^ (prefixWord ++ tailWord_31445).sum := by decide
  have hdescent : baseEnd_31445 < baseStart_31445 := by decide
  rcases family_descends (prefixWord ++ tailWord_31445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31460 : List Nat := [2, 3, 1, 1, 1, 4, 3, 5]
def baseStart_31460 : Nat := 118140960795 + 31460 * 2 ^ 59
def prefixEnd_31460 : Nat := 4983230072969 + 3 ^ 40 * 31460 * 2
def baseEnd_31460 : Nat := 4786400412015450757133

theorem tailTrace_31460 : CollatzResearch.WordTrace tailWord_31460 prefixEnd_31460 4786400412015450757133 := by
  unfold tailWord_31460
  simp only [CollatzResearch.WordTrace]
  refine ⟨573720233016633892673917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 764960310688845190231889 573720233016633892673917)
  ·
    refine ⟨215145087381237709752719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 573720233016633892673917 215145087381237709752719)
    ·
      refine ⟨322717631071856564629079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215145087381237709752719 322717631071856564629079)
      ·
        refine ⟨484076446607784846943619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322717631071856564629079 484076446607784846943619)
        ·
          refine ⟨726114669911677270415429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484076446607784846943619 726114669911677270415429)
          ·
            refine ⟨136146500608439488202893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 726114669911677270415429 136146500608439488202893)
            ·
              refine ⟨51054937728164808076085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136146500608439488202893 51054937728164808076085)
              ·
                refine ⟨4786400412015450757133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51054937728164808076085 4786400412015450757133)
                ·
                  rfl

theorem cell20_31460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_31460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31460 prefixEnd_31460 := by exact prefixLift 31460
  have htrace : WordTrace (prefixWord ++ tailWord_31460) baseStart_31460 baseEnd_31460 := by
    simpa [prefixWord, tailWord_31460, baseEnd_31460] using wordTrace_append hprefix tailTrace_31460
  have hstable : (prefixWord ++ tailWord_31460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31460).length < 2 ^ (prefixWord ++ tailWord_31460).sum := by decide
  have hdescent : baseEnd_31460 < baseStart_31460 := by decide
  rcases family_descends (prefixWord ++ tailWord_31460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31481 : List Nat := [1, 2, 1, 3, 1, 1, 1, 10]
def baseStart_31481 : Nat := 118140960795 + 31481 * 2 ^ 59
def prefixEnd_31481 : Nat := 4983230072969 + 3 ^ 40 * 31481 * 2
def baseEnd_31481 : Nat := 4789595402754537523771

theorem tailTrace_31481 : CollatzResearch.WordTrace tailWord_31481 prefixEnd_31481 4789595402754537523771 := by
  unfold tailWord_31481
  simp only [CollatzResearch.WordTrace]
  refine ⟨1148206398957188371862297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 765470932638125581241531 1148206398957188371862297)
  ·
    refine ⟨861154799217891278896723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1148206398957188371862297 861154799217891278896723)
    ·
      refine ⟨1291732198826836918345085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 861154799217891278896723 1291732198826836918345085)
      ·
        refine ⟨484399574560063844379407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1291732198826836918345085 484399574560063844379407)
        ·
          refine ⟨726599361840095766569111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484399574560063844379407 726599361840095766569111)
          ·
            refine ⟨1089899042760143649853667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726599361840095766569111 1089899042760143649853667)
            ·
              refine ⟨1634848564140215474780501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1089899042760143649853667 1634848564140215474780501)
              ·
                refine ⟨4789595402754537523771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1634848564140215474780501 4789595402754537523771)
                ·
                  rfl

theorem cell20_31481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 10].length) (baseStart_31481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31481 prefixEnd_31481 := by exact prefixLift 31481
  have htrace : WordTrace (prefixWord ++ tailWord_31481) baseStart_31481 baseEnd_31481 := by
    simpa [prefixWord, tailWord_31481, baseEnd_31481] using wordTrace_append hprefix tailTrace_31481
  have hstable : (prefixWord ++ tailWord_31481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31481).length < 2 ^ (prefixWord ++ tailWord_31481).sum := by decide
  have hdescent : baseEnd_31481 < baseStart_31481 := by decide
  rcases family_descends (prefixWord ++ tailWord_31481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31577 : List Nat := [1, 2, 1, 2, 2, 6, 2, 1, 3]
def baseStart_31577 : Nat := 118140960795 + 31577 * 2 ^ 59
def prefixEnd_31577 : Nat := 4983230072969 + 3 ^ 40 * 31577 * 2
def baseEnd_31577 : Nat := 14412603224113945370921

theorem tailTrace_31577 : CollatzResearch.WordTrace tailWord_31577 prefixEnd_31577 14412603224113945370921 := by
  unfold tailWord_31577
  simp only [CollatzResearch.WordTrace]
  refine ⟨1151707806609396767356985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 767805204406264511571323 1151707806609396767356985)
  ·
    refine ⟨863780854957047575517739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1151707806609396767356985 863780854957047575517739)
    ·
      refine ⟨1295671282435571363276609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 863780854957047575517739 1295671282435571363276609)
      ·
        refine ⟨971753461826678522457457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1295671282435571363276609 971753461826678522457457)
        ·
          refine ⟨728815096370008891843093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 971753461826678522457457 728815096370008891843093)
          ·
            refine ⟨34163207642344166805145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 728815096370008891843093 34163207642344166805145)
            ·
              refine ⟨25622405731758125103859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34163207642344166805145 25622405731758125103859)
              ·
                refine ⟨38433608597637187655789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25622405731758125103859 38433608597637187655789)
                ·
                  refine ⟨14412603224113945370921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38433608597637187655789 14412603224113945370921)
                  ·
                    rfl

theorem cell20_31577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 3].length) (baseStart_31577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31577 prefixEnd_31577 := by exact prefixLift 31577
  have htrace : WordTrace (prefixWord ++ tailWord_31577) baseStart_31577 baseEnd_31577 := by
    simpa [prefixWord, tailWord_31577, baseEnd_31577] using wordTrace_append hprefix tailTrace_31577
  have hstable : (prefixWord ++ tailWord_31577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31577).length < 2 ^ (prefixWord ++ tailWord_31577).sum := by decide
  have hdescent : baseEnd_31577 < baseStart_31577 := by decide
  rcases family_descends (prefixWord ++ tailWord_31577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31595 : List Nat := [1, 1, 1, 1, 2, 2, 6, 6]
def baseStart_31595 : Nat := 118140960795 + 31595 * 2 ^ 59
def prefixEnd_31595 : Nat := 4983230072969 + 3 ^ 40 * 31595 * 2
def baseEnd_31595 : Nat := 4806939638195294256949

theorem tailTrace_31595 : CollatzResearch.WordTrace tailWord_31595 prefixEnd_31595 4806939638195294256949 := by
  unfold tailWord_31595
  simp only [CollatzResearch.WordTrace]
  refine ⟨1152364320544185841512239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 768242880362790561008159 1152364320544185841512239)
  ·
    refine ⟨1728546480816278762268359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1152364320544185841512239 1728546480816278762268359)
    ·
      refine ⟨2592819721224418143402539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1728546480816278762268359 2592819721224418143402539)
      ·
        refine ⟨3889229581836627215103809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2592819721224418143402539 3889229581836627215103809)
        ·
          refine ⟨2916922186377470411327857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3889229581836627215103809 2916922186377470411327857)
          ·
            refine ⟨2187691639783102808495893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2916922186377470411327857 2187691639783102808495893)
            ·
              refine ⟨102548045614832944148245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2187691639783102808495893 102548045614832944148245)
              ·
                refine ⟨4806939638195294256949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102548045614832944148245 4806939638195294256949)
                ·
                  rfl

theorem cell20_31595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 6].length) (baseStart_31595 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31595 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31595 prefixEnd_31595 := by exact prefixLift 31595
  have htrace : WordTrace (prefixWord ++ tailWord_31595) baseStart_31595 baseEnd_31595 := by
    simpa [prefixWord, tailWord_31595, baseEnd_31595] using wordTrace_append hprefix tailTrace_31595
  have hstable : (prefixWord ++ tailWord_31595).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31595).length < 2 ^ (prefixWord ++ tailWord_31595).sum := by decide
  have hdescent : baseEnd_31595 < baseStart_31595 := by decide
  rcases family_descends (prefixWord ++ tailWord_31595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31614 : List Nat := [4, 2, 3, 1, 3, 1, 2, 2, 2]
def baseStart_31614 : Nat := 118140960795 + 31614 * 2 ^ 59
def prefixEnd_31614 : Nat := 4983230072969 + 3 ^ 40 * 31614 * 2
def baseEnd_31614 : Nat := 14429491032306261137437

theorem tailTrace_31614 : CollatzResearch.WordTrace tailWord_31614 prefixEnd_31614 14429491032306261137437 := by
  unfold tailWord_31614
  simp only [CollatzResearch.WordTrace]
  refine ⟨144132163434419010806737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 768704871650234724302597 144132163434419010806737)
  ·
    refine ⟨108099122575814258105053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144132163434419010806737 108099122575814258105053)
    ·
      refine ⟨40537170965930346789395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108099122575814258105053 40537170965930346789395)
      ·
        refine ⟨60805756448895520184093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40537170965930346789395 60805756448895520184093)
        ·
          refine ⟨22802158668335820069035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60805756448895520184093 22802158668335820069035)
          ·
            refine ⟨34203238002503730103553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22802158668335820069035 34203238002503730103553)
            ·
              refine ⟨25652428501877797577665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34203238002503730103553 25652428501877797577665)
              ·
                refine ⟨19239321376408348183249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25652428501877797577665 19239321376408348183249)
                ·
                  refine ⟨14429491032306261137437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19239321376408348183249 14429491032306261137437)
                  ·
                    rfl

theorem cell20_31614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_31614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31614 prefixEnd_31614 := by exact prefixLift 31614
  have htrace : WordTrace (prefixWord ++ tailWord_31614) baseStart_31614 baseEnd_31614 := by
    simpa [prefixWord, tailWord_31614, baseEnd_31614] using wordTrace_append hprefix tailTrace_31614
  have hstable : (prefixWord ++ tailWord_31614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31614).length < 2 ^ (prefixWord ++ tailWord_31614).sum := by decide
  have hdescent : baseEnd_31614 < baseStart_31614 := by decide
  rcases family_descends (prefixWord ++ tailWord_31614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31636 : List Nat := [2, 4, 2, 1, 1, 1, 1, 5, 3]
def baseStart_31636 : Nat := 118140960795 + 31636 * 2 ^ 59
def prefixEnd_31636 : Nat := 4983230072969 + 3 ^ 40 * 31636 * 2
def baseEnd_31636 : Nat := 14439532431771962404013

theorem tailTrace_31636 : CollatzResearch.WordTrace tailWord_31636 prefixEnd_31636 14439532431771962404013 := by
  unfold tailWord_31636
  simp only [CollatzResearch.WordTrace]
  refine ⟨576929856697824921877381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 769239808930433229169841 576929856697824921877381)
  ·
    refine ⟨108174348130842172852009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 576929856697824921877381 108174348130842172852009)
    ·
      refine ⟨81130761098131629639007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108174348130842172852009 81130761098131629639007)
      ·
        refine ⟨121696141647197444458511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81130761098131629639007 121696141647197444458511)
        ·
          refine ⟨182544212470796166687767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121696141647197444458511 182544212470796166687767)
          ·
            refine ⟨273816318706194250031651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182544212470796166687767 273816318706194250031651)
            ·
              refine ⟨410724478059291375047477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273816318706194250031651 410724478059291375047477)
              ·
                refine ⟨38505419818058566410701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 410724478059291375047477 38505419818058566410701)
                ·
                  refine ⟨14439532431771962404013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38505419818058566410701 14439532431771962404013)
                  ·
                    rfl

theorem cell20_31636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_31636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31636 prefixEnd_31636 := by exact prefixLift 31636
  have htrace : WordTrace (prefixWord ++ tailWord_31636) baseStart_31636 baseEnd_31636 := by
    simpa [prefixWord, tailWord_31636, baseEnd_31636] using wordTrace_append hprefix tailTrace_31636
  have hstable : (prefixWord ++ tailWord_31636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31636).length < 2 ^ (prefixWord ++ tailWord_31636).sum := by decide
  have hdescent : baseEnd_31636 < baseStart_31636 := by decide
  rcases family_descends (prefixWord ++ tailWord_31636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31705 : List Nat := [1, 2, 1, 2, 5, 3, 2, 4]
def baseStart_31705 : Nat := 118140960795 + 31705 * 2 ^ 59
def prefixEnd_31705 : Nat := 4983230072969 + 3 ^ 40 * 31705 * 2
def baseEnd_31705 : Nat := 4823675303971463034577

theorem tailTrace_31705 : CollatzResearch.WordTrace tailWord_31705 prefixEnd_31705 4823675303971463034577 := by
  unfold tailWord_31705
  simp only [CollatzResearch.WordTrace]
  refine ⟨1156376350145674628016569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 770917566763783085344379 1156376350145674628016569)
  ·
    refine ⟨867282262609255971012427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1156376350145674628016569 867282262609255971012427)
    ·
      refine ⟨1300923393913883956518641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 867282262609255971012427 1300923393913883956518641)
      ·
        refine ⟨975692545435412967388981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1300923393913883956518641 975692545435412967388981)
        ·
          refine ⟨91471176134569965692717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 975692545435412967388981 91471176134569965692717)
          ·
            refine ⟨34301691050463737134769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91471176134569965692717 34301691050463737134769)
            ·
              refine ⟨25726268287847802851077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34301691050463737134769 25726268287847802851077)
              ·
                refine ⟨4823675303971463034577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25726268287847802851077 4823675303971463034577)
                ·
                  rfl

theorem cell20_31705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 4].length) (baseStart_31705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31705 prefixEnd_31705 := by exact prefixLift 31705
  have htrace : WordTrace (prefixWord ++ tailWord_31705) baseStart_31705 baseEnd_31705 := by
    simpa [prefixWord, tailWord_31705, baseEnd_31705] using wordTrace_append hprefix tailTrace_31705
  have hstable : (prefixWord ++ tailWord_31705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31705).length < 2 ^ (prefixWord ++ tailWord_31705).sum := by decide
  have hdescent : baseEnd_31705 < baseStart_31705 := by decide
  rcases family_descends (prefixWord ++ tailWord_31705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31746 : List Nat := [3, 4, 1, 3, 1, 1, 1, 3, 3]
def baseStart_31746 : Nat := 118140960795 + 31746 * 2 ^ 59
def prefixEnd_31746 : Nat := 4983230072969 + 3 ^ 40 * 31746 * 2
def baseEnd_31746 : Nat := 14489739429100468736897

theorem tailTrace_31746 : CollatzResearch.WordTrace tailWord_31746 prefixEnd_31746 14489739429100468736897 := by
  unfold tailWord_31746
  simp only [CollatzResearch.WordTrace]
  refine ⟨289467935749284657564773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 771914495331425753506061 289467935749284657564773)
  ·
    refine ⟨54275237952990873293395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289467935749284657564773 54275237952990873293395)
    ·
      refine ⟨81412856929486309940093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54275237952990873293395 81412856929486309940093)
      ·
        refine ⟨30529821348557366227535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81412856929486309940093 30529821348557366227535)
        ·
          refine ⟨45794732022836049341303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30529821348557366227535 45794732022836049341303)
          ·
            refine ⟨68692098034254074011955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45794732022836049341303 68692098034254074011955)
            ·
              refine ⟨103038147051381111017933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68692098034254074011955 103038147051381111017933)
              ·
                refine ⟨38639305144267916631725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103038147051381111017933 38639305144267916631725)
                ·
                  refine ⟨14489739429100468736897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38639305144267916631725 14489739429100468736897)
                  ·
                    rfl

theorem cell20_31746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_31746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31746 prefixEnd_31746 := by exact prefixLift 31746
  have htrace : WordTrace (prefixWord ++ tailWord_31746) baseStart_31746 baseEnd_31746 := by
    simpa [prefixWord, tailWord_31746, baseEnd_31746] using wordTrace_append hprefix tailTrace_31746
  have hstable : (prefixWord ++ tailWord_31746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31746).length < 2 ^ (prefixWord ++ tailWord_31746).sum := by decide
  have hdescent : baseEnd_31746 < baseStart_31746 := by decide
  rcases family_descends (prefixWord ++ tailWord_31746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31816 : List Nat := [2, 1, 3, 1, 1, 1, 5, 2, 4]
def baseStart_31816 : Nat := 118140960795 + 31816 * 2 ^ 59
def prefixEnd_31816 : Nat := 4983230072969 + 3 ^ 40 * 31816 * 2
def baseEnd_31816 : Nat := 14521689336491336403277

theorem tailTrace_31816 : CollatzResearch.WordTrace tailWord_31816 prefixEnd_31816 14521689336491336403277 := by
  unfold tailWord_31816
  simp only [CollatzResearch.WordTrace]
  refine ⟨580212426371770292653651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 773616568495693723538201 580212426371770292653651)
  ·
    refine ⟨870318639557655438980477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 580212426371770292653651 870318639557655438980477)
    ·
      refine ⟨326369489834120789617679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 870318639557655438980477 326369489834120789617679)
      ·
        refine ⟨489554234751181184426519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326369489834120789617679 489554234751181184426519)
        ·
          refine ⟨734331352126771776639779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489554234751181184426519 734331352126771776639779)
          ·
            refine ⟨1101497028190157664959669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734331352126771776639779 1101497028190157664959669)
            ·
              refine ⟨103265346392827281089969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1101497028190157664959669 103265346392827281089969)
              ·
                refine ⟨77449009794620460817477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103265346392827281089969 77449009794620460817477)
                ·
                  refine ⟨14521689336491336403277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77449009794620460817477 14521689336491336403277)
                  ·
                    rfl

theorem cell20_31816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_31816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31816 prefixEnd_31816 := by exact prefixLift 31816
  have htrace : WordTrace (prefixWord ++ tailWord_31816) baseStart_31816 baseEnd_31816 := by
    simpa [prefixWord, tailWord_31816, baseEnd_31816] using wordTrace_append hprefix tailTrace_31816
  have hstable : (prefixWord ++ tailWord_31816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31816).length < 2 ^ (prefixWord ++ tailWord_31816).sum := by decide
  have hdescent : baseEnd_31816 < baseStart_31816 := by decide
  rcases family_descends (prefixWord ++ tailWord_31816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31847 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 5]
def baseStart_31847 : Nat := 118140960795 + 31847 * 2 ^ 59
def prefixEnd_31847 : Nat := 4983230072969 + 3 ^ 40 * 31847 * 2
def baseEnd_31847 : Nat := 14535838581193006369817

theorem tailTrace_31847 : CollatzResearch.WordTrace tailWord_31847 prefixEnd_31847 14535838581193006369817 := by
  unfold tailWord_31847
  simp only [CollatzResearch.WordTrace]
  refine ⟨1161555515631232879685795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 774370343754155253123863 1161555515631232879685795)
  ·
    refine ⟨1742333273446849319528693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1161555515631232879685795 1742333273446849319528693)
    ·
      refine ⟨163343744385642123705815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1742333273446849319528693 163343744385642123705815)
      ·
        refine ⟨245015616578463185558723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163343744385642123705815 245015616578463185558723)
        ·
          refine ⟨367523424867694778338085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245015616578463185558723 367523424867694778338085)
          ·
            refine ⟨68910642162692770938391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 367523424867694778338085 68910642162692770938391)
            ·
              refine ⟨103365963244039156407587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68910642162692770938391 103365963244039156407587)
              ·
                refine ⟨155048944866058734611381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103365963244039156407587 155048944866058734611381)
                ·
                  refine ⟨14535838581193006369817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155048944866058734611381 14535838581193006369817)
                  ·
                    rfl

theorem cell20_31847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 5].length) (baseStart_31847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31847 prefixEnd_31847 := by exact prefixLift 31847
  have htrace : WordTrace (prefixWord ++ tailWord_31847) baseStart_31847 baseEnd_31847 := by
    simpa [prefixWord, tailWord_31847, baseEnd_31847] using wordTrace_append hprefix tailTrace_31847
  have hstable : (prefixWord ++ tailWord_31847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31847).length < 2 ^ (prefixWord ++ tailWord_31847).sum := by decide
  have hdescent : baseEnd_31847 < baseStart_31847 := by decide
  rcases family_descends (prefixWord ++ tailWord_31847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31850 : List Nat := [3, 1, 3, 2, 2, 1, 2, 4, 2]
def baseStart_31850 : Nat := 118140960795 + 31850 * 2 ^ 59
def prefixEnd_31850 : Nat := 4983230072969 + 3 ^ 40 * 31850 * 2
def baseEnd_31850 : Nat := 14537207862938329269805

theorem tailTrace_31850 : CollatzResearch.WordTrace tailWord_31850 prefixEnd_31850 14537207862938329269805 := by
  unfold tailWord_31850
  simp only [CollatzResearch.WordTrace]
  refine ⟨290416233655091098011251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 774443289746909594696669 290416233655091098011251)
  ·
    refine ⟨435624350482636647016877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290416233655091098011251 435624350482636647016877)
    ·
      refine ⟨163359131430988742631329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435624350482636647016877 163359131430988742631329)
      ·
        refine ⟨122519348573241556973497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163359131430988742631329 122519348573241556973497)
        ·
          refine ⟨91889511429931167730123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122519348573241556973497 91889511429931167730123)
          ·
            refine ⟨137834267144896751595185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91889511429931167730123 137834267144896751595185)
            ·
              refine ⟨103375700358672563696389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137834267144896751595185 103375700358672563696389)
              ·
                refine ⟨19382943817251105693073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103375700358672563696389 19382943817251105693073)
                ·
                  refine ⟨14537207862938329269805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19382943817251105693073 14537207862938329269805)
                  ·
                    rfl

theorem cell20_31850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 2].length) (baseStart_31850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31850 prefixEnd_31850 := by exact prefixLift 31850
  have htrace : WordTrace (prefixWord ++ tailWord_31850) baseStart_31850 baseEnd_31850 := by
    simpa [prefixWord, tailWord_31850, baseEnd_31850] using wordTrace_append hprefix tailTrace_31850
  have hstable : (prefixWord ++ tailWord_31850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31850).length < 2 ^ (prefixWord ++ tailWord_31850).sum := by decide
  have hdescent : baseEnd_31850 < baseStart_31850 := by decide
  rcases family_descends (prefixWord ++ tailWord_31850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31870 : List Nat := [4, 2, 4, 1, 1, 2, 2, 4]
def baseStart_31870 : Nat := 118140960795 + 31870 * 2 ^ 59
def prefixEnd_31870 : Nat := 4983230072969 + 3 ^ 40 * 31870 * 2
def baseEnd_31870 : Nat := 4848778802635716201019

theorem tailTrace_31870 : CollatzResearch.WordTrace tailWord_31870 prefixEnd_31870 4848778802635716201019 := by
  unfold tailWord_31870
  simp only [CollatzResearch.WordTrace]
  refine ⟨145299299318488475971633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 774929596365271871848709 145299299318488475971633)
  ·
    refine ⟨108974474488866356978725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145299299318488475971633 108974474488866356978725)
    ·
      refine ⟨20432713966662441933511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108974474488866356978725 20432713966662441933511)
      ·
        refine ⟨30649070949993662900267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20432713966662441933511 30649070949993662900267)
        ·
          refine ⟨45973606424990494350401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30649070949993662900267 45973606424990494350401)
          ·
            refine ⟨34480204818742870762801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45973606424990494350401 34480204818742870762801)
            ·
              refine ⟨25860153614057153072101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34480204818742870762801 25860153614057153072101)
              ·
                refine ⟨4848778802635716201019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25860153614057153072101 4848778802635716201019)
                ·
                  rfl

theorem cell20_31870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_31870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31870 prefixEnd_31870 := by exact prefixLift 31870
  have htrace : WordTrace (prefixWord ++ tailWord_31870) baseStart_31870 baseEnd_31870 := by
    simpa [prefixWord, tailWord_31870, baseEnd_31870] using wordTrace_append hprefix tailTrace_31870
  have hstable : (prefixWord ++ tailWord_31870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31870).length < 2 ^ (prefixWord ++ tailWord_31870).sum := by decide
  have hdescent : baseEnd_31870 < baseStart_31870 := by decide
  rcases family_descends (prefixWord ++ tailWord_31870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31902 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_31902 : Nat := 118140960795 + 31902 * 2 ^ 59
def prefixEnd_31902 : Nat := 4983230072969 + 3 ^ 40 * 31902 * 2
def baseEnd_31902 : Nat := 14560942079857259536259

theorem tailTrace_31902 : CollatzResearch.WordTrace tailWord_31902 prefixEnd_31902 14560942079857259536259 := by
  unfold tailWord_31902
  simp only [CollatzResearch.WordTrace]
  refine ⟨145445191303997159117245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 775707686954651515291973 145445191303997159117245)
  ·
    refine ⟨54541946738998934668967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145445191303997159117245 54541946738998934668967)
    ·
      refine ⟨81812920108498402003451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54541946738998934668967 81812920108498402003451)
      ·
        refine ⟨122719380162747603005177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81812920108498402003451 122719380162747603005177)
        ·
          refine ⟨92039535122060702253883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122719380162747603005177 92039535122060702253883)
          ·
            refine ⟨138059302683091053380825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92039535122060702253883 138059302683091053380825)
            ·
              refine ⟨103544477012318290035619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138059302683091053380825 103544477012318290035619)
              ·
                refine ⟨155316715518477435053429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103544477012318290035619 155316715518477435053429)
                ·
                  refine ⟨14560942079857259536259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155316715518477435053429 14560942079857259536259)
                  ·
                    rfl

theorem cell20_31902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_31902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31902 prefixEnd_31902 := by exact prefixLift 31902
  have htrace : WordTrace (prefixWord ++ tailWord_31902) baseStart_31902 baseEnd_31902 := by
    simpa [prefixWord, tailWord_31902, baseEnd_31902] using wordTrace_append hprefix tailTrace_31902
  have hstable : (prefixWord ++ tailWord_31902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31902).length < 2 ^ (prefixWord ++ tailWord_31902).sum := by decide
  have hdescent : baseEnd_31902 < baseStart_31902 := by decide
  rcases family_descends (prefixWord ++ tailWord_31902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31909 : List Nat := [1, 3, 1, 2, 1, 6, 1, 1, 4]
def baseStart_31909 : Nat := 118140960795 + 31909 * 2 ^ 59
def prefixEnd_31909 : Nat := 4983230072969 + 3 ^ 40 * 31909 * 2
def baseEnd_31909 : Nat := 14564137070596346302897

theorem tailTrace_31909 : CollatzResearch.WordTrace tailWord_31909 prefixEnd_31909 14564137070596346302897 := by
  unfold tailWord_31909
  simp only [CollatzResearch.WordTrace]
  refine ⟨1163816841406617468442781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 775877894271078312295187 1163816841406617468442781)
  ·
    refine ⟨436431315527481550666043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1163816841406617468442781 436431315527481550666043)
    ·
      refine ⟨654646973291222325999065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436431315527481550666043 654646973291222325999065)
      ·
        refine ⟨490985229968416744499299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654646973291222325999065 490985229968416744499299)
        ·
          refine ⟨736477844952625116748949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490985229968416744499299 736477844952625116748949)
          ·
            refine ⟨34522398982154302347607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 736477844952625116748949 34522398982154302347607)
            ·
              refine ⟨51783598473231453521411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34522398982154302347607 51783598473231453521411)
              ·
                refine ⟨77675397709847180282117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51783598473231453521411 77675397709847180282117)
                ·
                  refine ⟨14564137070596346302897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77675397709847180282117 14564137070596346302897)
                  ·
                    rfl

theorem cell20_31909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_31909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31909 prefixEnd_31909 := by exact prefixLift 31909
  have htrace : WordTrace (prefixWord ++ tailWord_31909) baseStart_31909 baseEnd_31909 := by
    simpa [prefixWord, tailWord_31909, baseEnd_31909] using wordTrace_append hprefix tailTrace_31909
  have hstable : (prefixWord ++ tailWord_31909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31909).length < 2 ^ (prefixWord ++ tailWord_31909).sum := by decide
  have hdescent : baseEnd_31909 < baseStart_31909 := by decide
  rcases family_descends (prefixWord ++ tailWord_31909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31913 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 10]
def baseStart_31913 : Nat := 118140960795 + 31913 * 2 ^ 59
def prefixEnd_31913 : Nat := 4983230072969 + 3 ^ 40 * 31913 * 2
def baseEnd_31913 : Nat := 14565962779590110169547

theorem tailTrace_31913 : CollatzResearch.WordTrace tailWord_31913 prefixEnd_31913 14565962779590110169547 := by
  unfold tailWord_31913
  simp only [CollatzResearch.WordTrace]
  refine ⟨1163962733392126151588393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 775975155594750767725595 1163962733392126151588393)
  ·
    refine ⟨872972050044094613691295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1163962733392126151588393 872972050044094613691295)
    ·
      refine ⟨1309458075066141920536943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 872972050044094613691295 1309458075066141920536943)
      ·
        refine ⟨1964187112599212880805415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1309458075066141920536943 1964187112599212880805415)
        ·
          refine ⟨2946280668898819321208123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1964187112599212880805415 2946280668898819321208123)
          ·
            refine ⟨4419421003348228981812185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2946280668898819321208123 4419421003348228981812185)
            ·
              refine ⟨3314565752511171736359139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4419421003348228981812185 3314565752511171736359139)
              ·
                refine ⟨4971848628766757604538709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3314565752511171736359139 4971848628766757604538709)
                ·
                  refine ⟨14565962779590110169547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 4971848628766757604538709 14565962779590110169547)
                  ·
                    rfl

theorem cell20_31913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_31913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31913 prefixEnd_31913 := by exact prefixLift 31913
  have htrace : WordTrace (prefixWord ++ tailWord_31913) baseStart_31913 baseEnd_31913 := by
    simpa [prefixWord, tailWord_31913, baseEnd_31913] using wordTrace_append hprefix tailTrace_31913
  have hstable : (prefixWord ++ tailWord_31913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31913).length < 2 ^ (prefixWord ++ tailWord_31913).sum := by decide
  have hdescent : baseEnd_31913 < baseStart_31913 := by decide
  rcases family_descends (prefixWord ++ tailWord_31913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31944 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 7]
def baseStart_31944 : Nat := 118140960795 + 31944 * 2 ^ 59
def prefixEnd_31944 : Nat := 4983230072969 + 3 ^ 40 * 31944 * 2
def baseEnd_31944 : Nat := 14580112024291780136087

theorem tailTrace_31944 : CollatzResearch.WordTrace tailWord_31944 prefixEnd_31944 14580112024291780136087 := by
  unfold tailWord_31944
  simp only [CollatzResearch.WordTrace]
  refine ⟨582546698139909222983443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 776728930853212297311257 582546698139909222983443)
  ·
    refine ⟨873820047209863834475165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 582546698139909222983443 873820047209863834475165)
    ·
      refine ⟨327682517703698937928187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 873820047209863834475165 327682517703698937928187)
      ·
        refine ⟨491523776555548406892281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327682517703698937928187 491523776555548406892281)
        ·
          refine ⟨368642832416661305169211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491523776555548406892281 368642832416661305169211)
          ·
            refine ⟨552964248624991957753817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368642832416661305169211 552964248624991957753817)
            ·
              refine ⟨414723186468743968315363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 552964248624991957753817 414723186468743968315363)
              ·
                refine ⟨622084779703115952473045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414723186468743968315363 622084779703115952473045)
                ·
                  refine ⟨14580112024291780136087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 622084779703115952473045 14580112024291780136087)
                  ·
                    rfl

theorem cell20_31944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_31944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31944 prefixEnd_31944 := by exact prefixLift 31944
  have htrace : WordTrace (prefixWord ++ tailWord_31944) baseStart_31944 baseEnd_31944 := by
    simpa [prefixWord, tailWord_31944, baseEnd_31944] using wordTrace_append hprefix tailTrace_31944
  have hstable : (prefixWord ++ tailWord_31944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31944).length < 2 ^ (prefixWord ++ tailWord_31944).sum := by decide
  have hdescent : baseEnd_31944 < baseStart_31944 := by decide
  rcases family_descends (prefixWord ++ tailWord_31944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31951 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 8]
def baseStart_31951 : Nat := 118140960795 + 31951 * 2 ^ 59
def prefixEnd_31951 : Nat := 4983230072969 + 3 ^ 40 * 31951 * 2
def baseEnd_31951 : Nat := 14583307015030866902725

theorem tailTrace_31951 : CollatzResearch.WordTrace tailWord_31951 prefixEnd_31951 14583307015030866902725 := by
  unfold tailWord_31951
  simp only [CollatzResearch.WordTrace]
  refine ⟨1165348707254458641471707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 776899138169639094314471 1165348707254458641471707)
  ·
    refine ⟨1748023060881687962207561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1165348707254458641471707 1748023060881687962207561)
    ·
      refine ⟨1311017295661265971655671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1748023060881687962207561 1311017295661265971655671)
      ·
        refine ⟨1966525943491898957483507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1311017295661265971655671 1966525943491898957483507)
        ·
          refine ⟨2949788915237848436225261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1966525943491898957483507 2949788915237848436225261)
          ·
            refine ⟨1106170843214193163584473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2949788915237848436225261 1106170843214193163584473)
            ·
              refine ⟨829628132410644872688355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1106170843214193163584473 829628132410644872688355)
              ·
                refine ⟨1244442198615967309032533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 829628132410644872688355 1244442198615967309032533)
                ·
                  refine ⟨14583307015030866902725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1244442198615967309032533 14583307015030866902725)
                  ·
                    rfl

theorem cell20_31951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_31951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31951 prefixEnd_31951 := by exact prefixLift 31951
  have htrace : WordTrace (prefixWord ++ tailWord_31951) baseStart_31951 baseEnd_31951 := by
    simpa [prefixWord, tailWord_31951, baseEnd_31951] using wordTrace_append hprefix tailTrace_31951
  have hstable : (prefixWord ++ tailWord_31951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31951).length < 2 ^ (prefixWord ++ tailWord_31951).sum := by decide
  have hdescent : baseEnd_31951 < baseStart_31951 := by decide
  rcases family_descends (prefixWord ++ tailWord_31951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31960 : List Nat := [2, 1, 2, 2, 6, 1, 2, 2, 2]
def baseStart_31960 : Nat := 118140960795 + 31960 * 2 ^ 59
def prefixEnd_31960 : Nat := 4983230072969 + 3 ^ 40 * 31960 * 2
def baseEnd_31960 : Nat := 14587414860266835602689

theorem tailTrace_31960 : CollatzResearch.WordTrace tailWord_31960 prefixEnd_31960 14587414860266835602689 := by
  unfold tailWord_31960
  simp only [CollatzResearch.WordTrace]
  refine ⟨582838482110926589274667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 777117976147902119032889 582838482110926589274667)
  ·
    refine ⟨874257723166389883912001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 582838482110926589274667 874257723166389883912001)
    ·
      refine ⟨655693292374792412934001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 874257723166389883912001 655693292374792412934001)
      ·
        refine ⟨491769969281094309700501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 655693292374792412934001 491769969281094309700501)
        ·
          refine ⟨23051717310051295767211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 491769969281094309700501 23051717310051295767211)
          ·
            refine ⟨34577575965076943650817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23051717310051295767211 34577575965076943650817)
            ·
              refine ⟨25933181973807707738113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34577575965076943650817 25933181973807707738113)
              ·
                refine ⟨19449886480355780803585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25933181973807707738113 19449886480355780803585)
                ·
                  refine ⟨14587414860266835602689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19449886480355780803585 14587414860266835602689)
                  ·
                    rfl

theorem cell20_31960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 2].length) (baseStart_31960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_31960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_31960 prefixEnd_31960 := by exact prefixLift 31960
  have htrace : WordTrace (prefixWord ++ tailWord_31960) baseStart_31960 baseEnd_31960 := by
    simpa [prefixWord, tailWord_31960, baseEnd_31960] using wordTrace_append hprefix tailTrace_31960
  have hstable : (prefixWord ++ tailWord_31960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31960).length < 2 ^ (prefixWord ++ tailWord_31960).sum := by decide
  have hdescent : baseEnd_31960 < baseStart_31960 := by decide
  rcases family_descends (prefixWord ++ tailWord_31960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32023 : List Nat := [1, 1, 3, 4, 1, 1, 1, 6, 2]
def baseStart_32023 : Nat := 118140960795 + 32023 * 2 ^ 59
def prefixEnd_32023 : Nat := 4983230072969 + 3 ^ 40 * 32023 * 2
def baseEnd_32023 : Nat := 14616169776918616502431

theorem tailTrace_32023 : CollatzResearch.WordTrace tailWord_32023 prefixEnd_32023 14616169776918616502431 := by
  unfold tailWord_32023
  simp only [CollatzResearch.WordTrace]
  refine ⟨1167974762993614938092723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 778649841995743292061815 1167974762993614938092723)
  ·
    refine ⟨1751962144490422407139085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1167974762993614938092723 1751962144490422407139085)
    ·
      refine ⟨656985804183908402677157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1751962144490422407139085 656985804183908402677157)
      ·
        refine ⟨123184838284482825501967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 656985804183908402677157 123184838284482825501967)
        ·
          refine ⟨184777257426724238252951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123184838284482825501967 184777257426724238252951)
          ·
            refine ⟨277165886140086357379427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184777257426724238252951 277165886140086357379427)
            ·
              refine ⟨415748829210129536069141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277165886140086357379427 415748829210129536069141)
              ·
                refine ⟨19488226369224822003241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 415748829210129536069141 19488226369224822003241)
                ·
                  refine ⟨14616169776918616502431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19488226369224822003241 14616169776918616502431)
                  ·
                    rfl

theorem cell20_32023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 2].length) (baseStart_32023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32023 prefixEnd_32023 := by exact prefixLift 32023
  have htrace : WordTrace (prefixWord ++ tailWord_32023) baseStart_32023 baseEnd_32023 := by
    simpa [prefixWord, tailWord_32023, baseEnd_32023] using wordTrace_append hprefix tailTrace_32023
  have hstable : (prefixWord ++ tailWord_32023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32023).length < 2 ^ (prefixWord ++ tailWord_32023).sum := by decide
  have hdescent : baseEnd_32023 < baseStart_32023 := by decide
  rcases family_descends (prefixWord ++ tailWord_32023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32051 : List Nat := [1, 1, 1, 2, 5, 3, 1, 6]
def baseStart_32051 : Nat := 118140960795 + 32051 * 2 ^ 59
def prefixEnd_32051 : Nat := 4983230072969 + 3 ^ 40 * 32051 * 2
def baseEnd_32051 : Nat := 4876316579958321189661

theorem tailTrace_32051 : CollatzResearch.WordTrace tailWord_32051 prefixEnd_32051 4876316579958321189661 := by
  unfold tailWord_32051
  simp only [CollatzResearch.WordTrace]
  refine ⟨1168996006892175720112007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 779330671261450480074671 1168996006892175720112007)
  ·
    refine ⟨1753494010338263580168011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1168996006892175720112007 1753494010338263580168011)
    ·
      refine ⟨2630241015507395370252017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1753494010338263580168011 2630241015507395370252017)
      ·
        refine ⟨1972680761630546527689013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2630241015507395370252017 1972680761630546527689013)
        ·
          refine ⟨184938821402863736970845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1972680761630546527689013 184938821402863736970845)
          ·
            refine ⟨69352058026073901364067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184938821402863736970845 69352058026073901364067)
            ·
              refine ⟨104028087039110852046101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69352058026073901364067 104028087039110852046101)
              ·
                refine ⟨4876316579958321189661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104028087039110852046101 4876316579958321189661)
                ·
                  rfl

theorem cell20_32051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 6].length) (baseStart_32051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32051 prefixEnd_32051 := by exact prefixLift 32051
  have htrace : WordTrace (prefixWord ++ tailWord_32051) baseStart_32051 baseEnd_32051 := by
    simpa [prefixWord, tailWord_32051, baseEnd_32051] using wordTrace_append hprefix tailTrace_32051
  have hstable : (prefixWord ++ tailWord_32051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32051).length < 2 ^ (prefixWord ++ tailWord_32051).sum := by decide
  have hdescent : baseEnd_32051 < baseStart_32051 := by decide
  rcases family_descends (prefixWord ++ tailWord_32051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32057 : List Nat := [1, 2, 1, 6, 2, 2, 1, 3, 2]
def baseStart_32057 : Nat := 118140960795 + 32057 * 2 ^ 59
def prefixEnd_32057 : Nat := 4983230072969 + 3 ^ 40 * 32057 * 2
def baseEnd_32057 : Nat := 14631688303365609368959

theorem tailTrace_32057 : CollatzResearch.WordTrace tailWord_32057 prefixEnd_32057 14631688303365609368959 := by
  unfold tailWord_32057
  simp only [CollatzResearch.WordTrace]
  refine ⟨1169214844870438744830425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 779476563246959163220283 1169214844870438744830425)
  ·
    refine ⟨876911133652829058622819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1169214844870438744830425 876911133652829058622819)
    ·
      refine ⟨1315366700479243587934229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 876911133652829058622819 1315366700479243587934229)
      ·
        refine ⟨61657814084964543184417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1315366700479243587934229 61657814084964543184417)
        ·
          refine ⟨46243360563723407388313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61657814084964543184417 46243360563723407388313)
          ·
            refine ⟨34682520422792555541235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46243360563723407388313 34682520422792555541235)
            ·
              refine ⟨52023780634188833311853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34682520422792555541235 52023780634188833311853)
              ·
                refine ⟨19508917737820812491945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52023780634188833311853 19508917737820812491945)
                ·
                  refine ⟨14631688303365609368959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19508917737820812491945 14631688303365609368959)
                  ·
                    rfl

theorem cell20_32057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 2].length) (baseStart_32057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32057 prefixEnd_32057 := by exact prefixLift 32057
  have htrace : WordTrace (prefixWord ++ tailWord_32057) baseStart_32057 baseEnd_32057 := by
    simpa [prefixWord, tailWord_32057, baseEnd_32057] using wordTrace_append hprefix tailTrace_32057
  have hstable : (prefixWord ++ tailWord_32057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32057).length < 2 ^ (prefixWord ++ tailWord_32057).sum := by decide
  have hdescent : baseEnd_32057 < baseStart_32057 := by decide
  rcases family_descends (prefixWord ++ tailWord_32057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32058 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 7]
def baseStart_32058 : Nat := 118140960795 + 32058 * 2 ^ 59
def prefixEnd_32058 : Nat := 4983230072969 + 3 ^ 40 * 32058 * 2
def baseEnd_32058 : Nat := 14632144730614050335621

theorem tailTrace_32058 : CollatzResearch.WordTrace tailWord_32058 prefixEnd_32058 14632144730614050335621 := by
  unfold tailWord_32058
  simp only [CollatzResearch.WordTrace]
  refine ⟨292312829466703978904207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 779500878577877277077885 292312829466703978904207)
  ·
    refine ⟨438469244200055968356311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292312829466703978904207 438469244200055968356311)
    ·
      refine ⟨657703866300083952534467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438469244200055968356311 657703866300083952534467)
      ·
        refine ⟨986555799450125928801701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657703866300083952534467 986555799450125928801701)
        ·
          refine ⟨184979212396898611650319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 986555799450125928801701 184979212396898611650319)
          ·
            refine ⟨277468818595347917475479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184979212396898611650319 277468818595347917475479)
            ·
              refine ⟨416203227893021876213219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277468818595347917475479 416203227893021876213219)
              ·
                refine ⟨624304841839532814319829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416203227893021876213219 624304841839532814319829)
                ·
                  refine ⟨14632144730614050335621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 624304841839532814319829 14632144730614050335621)
                  ·
                    rfl

theorem cell20_32058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_32058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32058 prefixEnd_32058 := by exact prefixLift 32058
  have htrace : WordTrace (prefixWord ++ tailWord_32058) baseStart_32058 baseEnd_32058 := by
    simpa [prefixWord, tailWord_32058, baseEnd_32058] using wordTrace_append hprefix tailTrace_32058
  have hstable : (prefixWord ++ tailWord_32058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32058).length < 2 ^ (prefixWord ++ tailWord_32058).sum := by decide
  have hdescent : baseEnd_32058 < baseStart_32058 := by decide
  rcases family_descends (prefixWord ++ tailWord_32058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32068 : List Nat := [2, 3, 4, 1, 1, 1, 8]
def baseStart_32068 : Nat := 118140960795 + 32068 * 2 ^ 59
def prefixEnd_32068 : Nat := 4983230072969 + 3 ^ 40 * 32068 * 2
def baseEnd_32068 : Nat := 1626301000344273333583

theorem tailTrace_32068 : CollatzResearch.WordTrace tailWord_32068 prefixEnd_32068 1626301000344273333583 := by
  unfold tailWord_32068
  simp only [CollatzResearch.WordTrace]
  refine ⟨584808023915293811740429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 779744031887058415653905 584808023915293811740429)
  ·
    refine ⟨219303008968235179402661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 584808023915293811740429 219303008968235179402661)
    ·
      refine ⟨41119314181544096137999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219303008968235179402661 41119314181544096137999)
      ·
        refine ⟨61678971272316144206999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41119314181544096137999 61678971272316144206999)
        ·
          refine ⟨92518456908474216310499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61678971272316144206999 92518456908474216310499)
          ·
            refine ⟨138777685362711324465749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92518456908474216310499 138777685362711324465749)
            ·
              refine ⟨1626301000344273333583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 138777685362711324465749 1626301000344273333583)
              ·
                rfl

theorem cell20_32068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 8].length) (baseStart_32068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32068 prefixEnd_32068 := by exact prefixLift 32068
  have htrace : WordTrace (prefixWord ++ tailWord_32068) baseStart_32068 baseEnd_32068 := by
    simpa [prefixWord, tailWord_32068, baseEnd_32068] using wordTrace_append hprefix tailTrace_32068
  have hstable : (prefixWord ++ tailWord_32068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32068).length < 2 ^ (prefixWord ++ tailWord_32068).sum := by decide
  have hdescent : baseEnd_32068 < baseStart_32068 := by decide
  rcases family_descends (prefixWord ++ tailWord_32068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32078 : List Nat := [4, 1, 1, 1, 1, 1, 7, 2, 2]
def baseStart_32078 : Nat := 118140960795 + 32078 * 2 ^ 59
def prefixEnd_32078 : Nat := 4983230072969 + 3 ^ 40 * 32078 * 2
def baseEnd_32078 : Nat := 14641273275582869668873

theorem tailTrace_32078 : CollatzResearch.WordTrace tailWord_32078 prefixEnd_32078 14641273275582869668873 := by
  unfold tailWord_32078
  simp only [CollatzResearch.WordTrace]
  refine ⟨146247597224294916418111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 779987185196239554229925 146247597224294916418111)
  ·
    refine ⟨219371395836442374627167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146247597224294916418111 219371395836442374627167)
    ·
      refine ⟨329057093754663561940751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219371395836442374627167 329057093754663561940751)
      ·
        refine ⟨493585640631995342911127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329057093754663561940751 493585640631995342911127)
        ·
          refine ⟨740378460947993014366691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493585640631995342911127 740378460947993014366691)
          ·
            refine ⟨1110567691421989521550037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740378460947993014366691 1110567691421989521550037)
            ·
              refine ⟨26028930267702879411329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1110567691421989521550037 26028930267702879411329)
              ·
                refine ⟨19521697700777159558497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26028930267702879411329 19521697700777159558497)
                ·
                  refine ⟨14641273275582869668873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19521697700777159558497 14641273275582869668873)
                  ·
                    rfl

theorem cell20_32078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_32078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32078 prefixEnd_32078 := by exact prefixLift 32078
  have htrace : WordTrace (prefixWord ++ tailWord_32078) baseStart_32078 baseEnd_32078 := by
    simpa [prefixWord, tailWord_32078, baseEnd_32078] using wordTrace_append hprefix tailTrace_32078
  have hstable : (prefixWord ++ tailWord_32078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32078).length < 2 ^ (prefixWord ++ tailWord_32078).sum := by decide
  have hdescent : baseEnd_32078 < baseStart_32078 := by decide
  rcases family_descends (prefixWord ++ tailWord_32078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32126 : List Nat := [4, 2, 3, 2, 1, 1, 2, 2, 3]
def baseStart_32126 : Nat := 118140960795 + 32126 * 2 ^ 59
def prefixEnd_32126 : Nat := 4983230072969 + 3 ^ 40 * 32126 * 2
def baseEnd_32126 : Nat := 14663181783508036068677

theorem tailTrace_32126 : CollatzResearch.WordTrace tailWord_32126 prefixEnd_32126 14663181783508036068677 := by
  unfold tailWord_32126
  simp only [CollatzResearch.WordTrace]
  refine ⟨146466435202557941136529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 781154321080309019394821 146466435202557941136529)
  ·
    refine ⟨109849826401918455852397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146466435202557941136529 109849826401918455852397)
    ·
      refine ⟨41193684900719420944649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109849826401918455852397 41193684900719420944649)
      ·
        refine ⟨30895263675539565708487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41193684900719420944649 30895263675539565708487)
        ·
          refine ⟨46342895513309348562731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30895263675539565708487 46342895513309348562731)
          ·
            refine ⟨69514343269964022844097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46342895513309348562731 69514343269964022844097)
            ·
              refine ⟨52135757452473017133073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69514343269964022844097 52135757452473017133073)
              ·
                refine ⟨39101818089354762849805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52135757452473017133073 39101818089354762849805)
                ·
                  refine ⟨14663181783508036068677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39101818089354762849805 14663181783508036068677)
                  ·
                    rfl

theorem cell20_32126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_32126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32126 prefixEnd_32126 := by exact prefixLift 32126
  have htrace : WordTrace (prefixWord ++ tailWord_32126) baseStart_32126 baseEnd_32126 := by
    simpa [prefixWord, tailWord_32126, baseEnd_32126] using wordTrace_append hprefix tailTrace_32126
  have hstable : (prefixWord ++ tailWord_32126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32126).length < 2 ^ (prefixWord ++ tailWord_32126).sum := by decide
  have hdescent : baseEnd_32126 < baseStart_32126 := by decide
  rcases family_descends (prefixWord ++ tailWord_32126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32185 : List Nat := [1, 2, 1, 4, 5, 1, 1, 2, 3]
def baseStart_32185 : Nat := 118140960795 + 32185 * 2 ^ 59
def prefixEnd_32185 : Nat := 4983230072969 + 3 ^ 40 * 32185 * 2
def baseEnd_32185 : Nat := 14690110991166053101769

theorem tailTrace_32185 : CollatzResearch.WordTrace tailWord_32185 prefixEnd_32185 14690110991166053101769 := by
  unfold tailWord_32185
  simp only [CollatzResearch.WordTrace]
  refine ⟨1173883388406716605490009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 782588925604477736993339 1173883388406716605490009)
  ·
    refine ⟨880412541305037454117507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1173883388406716605490009 880412541305037454117507)
    ·
      refine ⟨1320618811957556181176261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 880412541305037454117507 1320618811957556181176261)
      ·
        refine ⟨247616027242041783970549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1320618811957556181176261 247616027242041783970549)
        ·
          refine ⟨23214002553941417247239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 247616027242041783970549 23214002553941417247239)
          ·
            refine ⟨34821003830912125870859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23214002553941417247239 34821003830912125870859)
            ·
              refine ⟨52231505746368188806289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34821003830912125870859 52231505746368188806289)
              ·
                refine ⟨39173629309776141604717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52231505746368188806289 39173629309776141604717)
                ·
                  refine ⟨14690110991166053101769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39173629309776141604717 14690110991166053101769)
                  ·
                    rfl

theorem cell20_32185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 3].length) (baseStart_32185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32185 prefixEnd_32185 := by exact prefixLift 32185
  have htrace : WordTrace (prefixWord ++ tailWord_32185) baseStart_32185 baseEnd_32185 := by
    simpa [prefixWord, tailWord_32185, baseEnd_32185] using wordTrace_append hprefix tailTrace_32185
  have hstable : (prefixWord ++ tailWord_32185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32185).length < 2 ^ (prefixWord ++ tailWord_32185).sum := by decide
  have hdescent : baseEnd_32185 < baseStart_32185 := by decide
  rcases family_descends (prefixWord ++ tailWord_32185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32237 : List Nat := [1, 5, 1, 3, 3, 1, 6]
def baseStart_32237 : Nat := 118140960795 + 32237 * 2 ^ 59
def prefixEnd_32237 : Nat := 4983230072969 + 3 ^ 40 * 32237 * 2
def baseEnd_32237 : Nat := 1634871689787220374247

theorem tailTrace_32237 : CollatzResearch.WordTrace tailWord_32237 prefixEnd_32237 1634871689787220374247 := by
  unfold tailWord_32237
  simp only [CollatzResearch.WordTrace]
  refine ⟨1175779984218329486382965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 783853322812219657588643 1175779984218329486382965)
  ·
    refine ⟨110229373520468389348403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1175779984218329486382965 110229373520468389348403)
    ·
      refine ⟨165344060280702584022605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110229373520468389348403 165344060280702584022605)
      ·
        refine ⟨62004022605263469008477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165344060280702584022605 62004022605263469008477)
        ·
          refine ⟨23251508476973800878179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62004022605263469008477 23251508476973800878179)
          ·
            refine ⟨34877262715460701317269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23251508476973800878179 34877262715460701317269)
            ·
              refine ⟨1634871689787220374247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34877262715460701317269 1634871689787220374247)
              ·
                rfl

theorem cell20_32237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 6].length) (baseStart_32237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32237 prefixEnd_32237 := by exact prefixLift 32237
  have htrace : WordTrace (prefixWord ++ tailWord_32237) baseStart_32237 baseEnd_32237 := by
    simpa [prefixWord, tailWord_32237, baseEnd_32237] using wordTrace_append hprefix tailTrace_32237
  have hstable : (prefixWord ++ tailWord_32237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32237).length < 2 ^ (prefixWord ++ tailWord_32237).sum := by decide
  have hdescent : baseEnd_32237 < baseStart_32237 := by decide
  rcases family_descends (prefixWord ++ tailWord_32237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32241 : List Nat := [1, 2, 2, 2, 3, 4, 6]
def baseStart_32241 : Nat := 118140960795 + 32241 * 2 ^ 59
def prefixEnd_32241 : Nat := 4983230072969 + 3 ^ 40 * 32241 * 2
def baseEnd_32241 : Nat := 1635074546342083026097

theorem tailTrace_32241 : CollatzResearch.WordTrace tailWord_32241 prefixEnd_32241 1635074546342083026097 := by
  unfold tailWord_32241
  simp only [CollatzResearch.WordTrace]
  refine ⟨1175925876203838169528577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 783950584135892113019051 1175925876203838169528577)
  ·
    refine ⟨881944407152878627146433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1175925876203838169528577 881944407152878627146433)
    ·
      refine ⟨661458305364658970359825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 881944407152878627146433 661458305364658970359825)
      ·
        refine ⟨496093729023494227769869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 661458305364658970359825 496093729023494227769869)
        ·
          refine ⟨186035148383810335413701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 496093729023494227769869 186035148383810335413701)
          ·
            refine ⟨34881590321964437890069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186035148383810335413701 34881590321964437890069)
            ·
              refine ⟨1635074546342083026097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34881590321964437890069 1635074546342083026097)
              ·
                rfl

theorem cell20_32241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 6].length) (baseStart_32241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32241 prefixEnd_32241 := by exact prefixLift 32241
  have htrace : WordTrace (prefixWord ++ tailWord_32241) baseStart_32241 baseEnd_32241 := by
    simpa [prefixWord, tailWord_32241, baseEnd_32241] using wordTrace_append hprefix tailTrace_32241
  have hstable : (prefixWord ++ tailWord_32241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32241).length < 2 ^ (prefixWord ++ tailWord_32241).sum := by decide
  have hdescent : baseEnd_32241 < baseStart_32241 := by decide
  rcases family_descends (prefixWord ++ tailWord_32241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32248 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 5]
def baseStart_32248 : Nat := 118140960795 + 32248 * 2 ^ 59
def prefixEnd_32248 : Nat := 4983230072969 + 3 ^ 40 * 32248 * 2
def baseEnd_32248 : Nat := 14718865907817834001511

theorem tailTrace_32248 : CollatzResearch.WordTrace tailWord_32248 prefixEnd_32248 14718865907817834001511 := by
  unfold tailWord_32248
  simp only [CollatzResearch.WordTrace]
  refine ⟨588090593589239182516699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 784120791452318910022265 588090593589239182516699)
  ·
    refine ⟨882135890383858773775049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 588090593589239182516699 882135890383858773775049)
    ·
      refine ⟨661601917787894080331287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 882135890383858773775049 661601917787894080331287)
      ·
        refine ⟨992402876681841120496931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661601917787894080331287 992402876681841120496931)
        ·
          refine ⟨1488604315022761680745397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992402876681841120496931 1488604315022761680745397)
          ·
            refine ⟨139556654533383907569881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1488604315022761680745397 139556654533383907569881)
            ·
              refine ⟨104667490900037930677411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139556654533383907569881 104667490900037930677411)
              ·
                refine ⟨157001236350056896016117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104667490900037930677411 157001236350056896016117)
                ·
                  refine ⟨14718865907817834001511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157001236350056896016117 14718865907817834001511)
                  ·
                    rfl

theorem cell20_32248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_32248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32248 prefixEnd_32248 := by exact prefixLift 32248
  have htrace : WordTrace (prefixWord ++ tailWord_32248) baseStart_32248 baseEnd_32248 := by
    simpa [prefixWord, tailWord_32248, baseEnd_32248] using wordTrace_append hprefix tailTrace_32248
  have hstable : (prefixWord ++ tailWord_32248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32248).length < 2 ^ (prefixWord ++ tailWord_32248).sum := by decide
  have hdescent : baseEnd_32248 < baseStart_32248 := by decide
  rcases family_descends (prefixWord ++ tailWord_32248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32255 : List Nat := [1, 1, 2, 2, 1, 2, 2, 5, 4]
def baseStart_32255 : Nat := 118140960795 + 32255 * 2 ^ 59
def prefixEnd_32255 : Nat := 4983230072969 + 3 ^ 40 * 32255 * 2
def baseEnd_32255 : Nat := 14722060898556920768149

theorem tailTrace_32255 : CollatzResearch.WordTrace tailWord_32255 prefixEnd_32255 14722060898556920768149 := by
  unfold tailWord_32255
  simp only [CollatzResearch.WordTrace]
  refine ⟨1176436498153118560538219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 784290998768745707025479 1176436498153118560538219)
  ·
    refine ⟨1764654747229677840807329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1176436498153118560538219 1764654747229677840807329)
    ·
      refine ⟨1323491060422258380605497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1764654747229677840807329 1323491060422258380605497)
      ·
        refine ⟨992618295316693785454123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1323491060422258380605497 992618295316693785454123)
        ·
          refine ⟨1488927442975040678181185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992618295316693785454123 1488927442975040678181185)
          ·
            refine ⟨1116695582231280508635889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1488927442975040678181185 1116695582231280508635889)
            ·
              refine ⟨837521686673460381476917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1116695582231280508635889 837521686673460381476917)
              ·
                refine ⟨78517658125636910763461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 837521686673460381476917 78517658125636910763461)
                ·
                  refine ⟨14722060898556920768149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78517658125636910763461 14722060898556920768149)
                  ·
                    rfl

theorem cell20_32255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 4].length) (baseStart_32255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32255 prefixEnd_32255 := by exact prefixLift 32255
  have htrace : WordTrace (prefixWord ++ tailWord_32255) baseStart_32255 baseEnd_32255 := by
    simpa [prefixWord, tailWord_32255, baseEnd_32255] using wordTrace_append hprefix tailTrace_32255
  have hstable : (prefixWord ++ tailWord_32255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32255).length < 2 ^ (prefixWord ++ tailWord_32255).sum := by decide
  have hdescent : baseEnd_32255 < baseStart_32255 := by decide
  rcases family_descends (prefixWord ++ tailWord_32255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32258 : List Nat := [3, 4, 1, 2, 1, 1, 1, 7]
def baseStart_32258 : Nat := 118140960795 + 32258 * 2 ^ 59
def prefixEnd_32258 : Nat := 4983230072969 + 3 ^ 40 * 32258 * 2
def baseEnd_32258 : Nat := 4907810060100747889379

theorem tailTrace_32258 : CollatzResearch.WordTrace tailWord_32258 prefixEnd_32258 4907810060100747889379 := by
  unfold tailWord_32258
  simp only [CollatzResearch.WordTrace]
  refine ⟨294136479285562518224357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 784363944761500048598285 294136479285562518224357)
  ·
    refine ⟨55150589866042972167067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294136479285562518224357 55150589866042972167067)
    ·
      refine ⟨82725884799064458250601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55150589866042972167067 82725884799064458250601)
      ·
        refine ⟨62044413599298343687951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82725884799064458250601 62044413599298343687951)
        ·
          refine ⟨93066620398947515531927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62044413599298343687951 93066620398947515531927)
          ·
            refine ⟨139599930598421273297891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93066620398947515531927 139599930598421273297891)
            ·
              refine ⟨209399895897631909946837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139599930598421273297891 209399895897631909946837)
              ·
                refine ⟨4907810060100747889379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 209399895897631909946837 4907810060100747889379)
                ·
                  rfl

theorem cell20_32258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_32258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32258 prefixEnd_32258 := by exact prefixLift 32258
  have htrace : WordTrace (prefixWord ++ tailWord_32258) baseStart_32258 baseEnd_32258 := by
    simpa [prefixWord, tailWord_32258, baseEnd_32258] using wordTrace_append hprefix tailTrace_32258
  have hstable : (prefixWord ++ tailWord_32258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32258).length < 2 ^ (prefixWord ++ tailWord_32258).sum := by decide
  have hdescent : baseEnd_32258 < baseStart_32258 := by decide
  rcases family_descends (prefixWord ++ tailWord_32258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32296 : List Nat := [2, 1, 5, 2, 3, 7]
def baseStart_32296 : Nat := 118140960795 + 32296 * 2 ^ 59
def prefixEnd_32296 : Nat := 4983230072969 + 3 ^ 40 * 32296 * 2
def baseEnd_32296 : Nat := 545954607990481496345

theorem tailTrace_32296 : CollatzResearch.WordTrace tailWord_32296 prefixEnd_32296 545954607990481496345 := by
  unfold tailWord_32296
  simp only [CollatzResearch.WordTrace]
  refine ⟨588965945502291281390371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 785287927336388375187161 588965945502291281390371)
  ·
    refine ⟨883448918253436922085557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 588965945502291281390371 883448918253436922085557)
    ·
      refine ⟨82823336086259711445521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 883448918253436922085557 82823336086259711445521)
      ·
        refine ⟨62117502064694783584141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82823336086259711445521 62117502064694783584141)
        ·
          refine ⟨23294063274260543844053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62117502064694783584141 23294063274260543844053)
          ·
            refine ⟨545954607990481496345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 23294063274260543844053 545954607990481496345)
            ·
              rfl

theorem cell20_32296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 7].length) (baseStart_32296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32296 prefixEnd_32296 := by exact prefixLift 32296
  have htrace : WordTrace (prefixWord ++ tailWord_32296) baseStart_32296 baseEnd_32296 := by
    simpa [prefixWord, tailWord_32296, baseEnd_32296] using wordTrace_append hprefix tailTrace_32296
  have hstable : (prefixWord ++ tailWord_32296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32296).length < 2 ^ (prefixWord ++ tailWord_32296).sum := by decide
  have hdescent : baseEnd_32296 < baseStart_32296 := by decide
  rcases family_descends (prefixWord ++ tailWord_32296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32365 : List Nat := [1, 5, 1, 1, 4, 1, 2, 1, 4]
def baseStart_32365 : Nat := 118140960795 + 32365 * 2 ^ 59
def prefixEnd_32365 : Nat := 4983230072969 + 3 ^ 40 * 32365 * 2
def baseEnd_32365 : Nat := 14772267895885427101033

theorem tailTrace_32365 : CollatzResearch.WordTrace tailWord_32365 prefixEnd_32365 14772267895885427101033 := by
  unfold tailWord_32365
  simp only [CollatzResearch.WordTrace]
  refine ⟨1180448527754607347042549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 786965685169738231361699 1180448527754607347042549)
  ·
    refine ⟨110667049476994438785239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1180448527754607347042549 110667049476994438785239)
    ·
      refine ⟨166000574215491658177859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110667049476994438785239 166000574215491658177859)
      ·
        refine ⟨249000861323237487266789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166000574215491658177859 249000861323237487266789)
        ·
          refine ⟨46687661498107028862523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249000861323237487266789 46687661498107028862523)
          ·
            refine ⟨70031492247160543293785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46687661498107028862523 70031492247160543293785)
            ·
              refine ⟨52523619185370407470339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70031492247160543293785 52523619185370407470339)
              ·
                refine ⟨78785428778055611205509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52523619185370407470339 78785428778055611205509)
                ·
                  refine ⟨14772267895885427101033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78785428778055611205509 14772267895885427101033)
                  ·
                    rfl

theorem cell20_32365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_32365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32365 prefixEnd_32365 := by exact prefixLift 32365
  have htrace : WordTrace (prefixWord ++ tailWord_32365) baseStart_32365 baseEnd_32365 := by
    simpa [prefixWord, tailWord_32365, baseEnd_32365] using wordTrace_append hprefix tailTrace_32365
  have hstable : (prefixWord ++ tailWord_32365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32365).length < 2 ^ (prefixWord ++ tailWord_32365).sum := by decide
  have hdescent : baseEnd_32365 < baseStart_32365 := by decide
  rcases family_descends (prefixWord ++ tailWord_32365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32379 : List Nat := [1, 1, 1, 1, 1, 4, 7, 1, 3]
def baseStart_32379 : Nat := 118140960795 + 32379 * 2 ^ 59
def prefixEnd_32379 : Nat := 4983230072969 + 3 ^ 40 * 32379 * 2
def baseEnd_32379 : Nat := 14778657877363600634309

theorem tailTrace_32379 : CollatzResearch.WordTrace tailWord_32379 prefixEnd_32379 14778657877363600634309 := by
  unfold tailWord_32379
  simp only [CollatzResearch.WordTrace]
  refine ⟨1180959149703887738052191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 787306099802591825368127 1180959149703887738052191)
  ·
    refine ⟨1771438724555831607078287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1180959149703887738052191 1771438724555831607078287)
    ·
      refine ⟨2657158086833747410617431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1771438724555831607078287 2657158086833747410617431)
      ·
        refine ⟨3985737130250621115926147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2657158086833747410617431 3985737130250621115926147)
        ·
          refine ⟨5978605695375931673889221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3985737130250621115926147 5978605695375931673889221)
          ·
            refine ⟨1120988567882987188854229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5978605695375931673889221 1120988567882987188854229)
            ·
              refine ⟨26273169559757512238771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1120988567882987188854229 26273169559757512238771)
              ·
                refine ⟨39409754339636268358157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26273169559757512238771 39409754339636268358157)
                ·
                  refine ⟨14778657877363600634309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39409754339636268358157 14778657877363600634309)
                  ·
                    rfl

theorem cell20_32379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 3].length) (baseStart_32379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32379 prefixEnd_32379 := by exact prefixLift 32379
  have htrace : WordTrace (prefixWord ++ tailWord_32379) baseStart_32379 baseEnd_32379 := by
    simpa [prefixWord, tailWord_32379, baseEnd_32379] using wordTrace_append hprefix tailTrace_32379
  have hstable : (prefixWord ++ tailWord_32379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32379).length < 2 ^ (prefixWord ++ tailWord_32379).sum := by decide
  have hdescent : baseEnd_32379 < baseStart_32379 := by decide
  rcases family_descends (prefixWord ++ tailWord_32379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32393 : List Nat := [1, 2, 1, 1, 4, 1, 6, 4]
def baseStart_32393 : Nat := 118140960795 + 32393 * 2 ^ 59
def prefixEnd_32393 : Nat := 4983230072969 + 3 ^ 40 * 32393 * 2
def baseEnd_32393 : Nat := 4928349286280591389195

theorem tailTrace_32393 : CollatzResearch.WordTrace tailWord_32393 prefixEnd_32393 4928349286280591389195 := by
  unfold tailWord_32393
  simp only [CollatzResearch.WordTrace]
  refine ⟨1181469771653168129061833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 787646514435445419374555 1181469771653168129061833)
  ·
    refine ⟨886102328739876096796375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1181469771653168129061833 886102328739876096796375)
    ·
      refine ⟨1329153493109814145194563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 886102328739876096796375 1329153493109814145194563)
      ·
        refine ⟨1993730239664721217791845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1329153493109814145194563 1993730239664721217791845)
        ·
          refine ⟨373824419937135228335971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1993730239664721217791845 373824419937135228335971)
          ·
            refine ⟨560736629905702842503957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373824419937135228335971 560736629905702842503957)
            ·
              refine ⟨26284529526829820742373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 560736629905702842503957 26284529526829820742373)
              ·
                refine ⟨4928349286280591389195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26284529526829820742373 4928349286280591389195)
                ·
                  rfl

theorem cell20_32393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 4].length) (baseStart_32393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32393 prefixEnd_32393 := by exact prefixLift 32393
  have htrace : WordTrace (prefixWord ++ tailWord_32393) baseStart_32393 baseEnd_32393 := by
    simpa [prefixWord, tailWord_32393, baseEnd_32393] using wordTrace_append hprefix tailTrace_32393
  have hstable : (prefixWord ++ tailWord_32393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32393).length < 2 ^ (prefixWord ++ tailWord_32393).sum := by decide
  have hdescent : baseEnd_32393 < baseStart_32393 := by decide
  rcases family_descends (prefixWord ++ tailWord_32393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32420 : List Nat := [2, 3, 1, 2, 2, 3, 3, 2, 2]
def baseStart_32420 : Nat := 118140960795 + 32420 * 2 ^ 59
def prefixEnd_32420 : Nat := 4983230072969 + 3 ^ 40 * 32420 * 2
def baseEnd_32420 : Nat := 14797371394549680267475

theorem tailTrace_32420 : CollatzResearch.WordTrace tailWord_32420 prefixEnd_32420 14797371394549680267475 := by
  unfold tailWord_32420
  simp only [CollatzResearch.WordTrace]
  refine ⟨591227271277675870147357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 788303028370234493529809 591227271277675870147357)
  ·
    refine ⟨221710226729128451305259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 591227271277675870147357 221710226729128451305259)
    ·
      refine ⟨332565340093692676957889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221710226729128451305259 332565340093692676957889)
      ·
        refine ⟨249424005070269507718417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332565340093692676957889 249424005070269507718417)
        ·
          refine ⟨187068003802702130788813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249424005070269507718417 187068003802702130788813)
          ·
            refine ⟨70150501426013299045805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187068003802702130788813 70150501426013299045805)
            ·
              refine ⟨26306438034754987142177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70150501426013299045805 26306438034754987142177)
              ·
                refine ⟨19729828526066240356633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26306438034754987142177 19729828526066240356633)
                ·
                  refine ⟨14797371394549680267475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19729828526066240356633 14797371394549680267475)
                  ·
                    rfl

theorem cell20_32420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_32420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32420 prefixEnd_32420 := by exact prefixLift 32420
  have htrace : WordTrace (prefixWord ++ tailWord_32420) baseStart_32420 baseEnd_32420 := by
    simpa [prefixWord, tailWord_32420, baseEnd_32420] using wordTrace_append hprefix tailTrace_32420
  have hstable : (prefixWord ++ tailWord_32420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32420).length < 2 ^ (prefixWord ++ tailWord_32420).sum := by decide
  have hdescent : baseEnd_32420 < baseStart_32420 := by decide
  rcases family_descends (prefixWord ++ tailWord_32420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32430 : List Nat := [4, 1, 4, 1, 2, 2, 2, 1, 3]
def baseStart_32430 : Nat := 118140960795 + 32430 * 2 ^ 59
def prefixEnd_32430 : Nat := 4983230072969 + 3 ^ 40 * 32430 * 2
def baseEnd_32430 : Nat := 14801935667034089934101

theorem tailTrace_32430 : CollatzResearch.WordTrace tailWord_32430 prefixEnd_32430 14801935667034089934101 := by
  unfold tailWord_32430
  simp only [CollatzResearch.WordTrace]
  refine ⟨147852409064890431019843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 788546181679415632105829 147852409064890431019843)
  ·
    refine ⟨221778613597335646529765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147852409064890431019843 221778613597335646529765)
    ·
      refine ⟨41583490049500433724331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221778613597335646529765 41583490049500433724331)
      ·
        refine ⟨62375235074250650586497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41583490049500433724331 62375235074250650586497)
        ·
          refine ⟨46781426305687987939873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62375235074250650586497 46781426305687987939873)
          ·
            refine ⟨35086069729265990954905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46781426305687987939873 35086069729265990954905)
            ·
              refine ⟨26314552296949493216179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35086069729265990954905 26314552296949493216179)
              ·
                refine ⟨39471828445424239824269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26314552296949493216179 39471828445424239824269)
                ·
                  refine ⟨14801935667034089934101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39471828445424239824269 14801935667034089934101)
                  ·
                    rfl

theorem cell20_32430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_32430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32430 prefixEnd_32430 := by exact prefixLift 32430
  have htrace : WordTrace (prefixWord ++ tailWord_32430) baseStart_32430 baseEnd_32430 := by
    simpa [prefixWord, tailWord_32430, baseEnd_32430] using wordTrace_append hprefix tailTrace_32430
  have hstable : (prefixWord ++ tailWord_32430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32430).length < 2 ^ (prefixWord ++ tailWord_32430).sum := by decide
  have hdescent : baseEnd_32430 < baseStart_32430 := by decide
  rcases family_descends (prefixWord ++ tailWord_32430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32445 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 6]
def baseStart_32445 : Nat := 118140960795 + 32445 * 2 ^ 59
def prefixEnd_32445 : Nat := 4983230072969 + 3 ^ 40 * 32445 * 2
def baseEnd_32445 : Nat := 14808782075760704434039

theorem tailTrace_32445 : CollatzResearch.WordTrace tailWord_32445 prefixEnd_32445 14808782075760704434039 := by
  unfold tailWord_32445
  simp only [CollatzResearch.WordTrace]
  refine ⟨1183366367464781009954789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 788910911643187339969859 1183366367464781009954789)
  ·
    refine ⟨221881193899646439366523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1183366367464781009954789 221881193899646439366523)
    ·
      refine ⟨332821790849469659049785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221881193899646439366523 332821790849469659049785)
      ·
        refine ⟨249616343137102244287339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332821790849469659049785 249616343137102244287339)
        ·
          refine ⟨374424514705653366431009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249616343137102244287339 374424514705653366431009)
          ·
            refine ⟨280818386029240024823257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374424514705653366431009 280818386029240024823257)
            ·
              refine ⟨210613789521930018617443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280818386029240024823257 210613789521930018617443)
              ·
                refine ⟨315920684282895027926165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210613789521930018617443 315920684282895027926165)
                ·
                  refine ⟨14808782075760704434039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 315920684282895027926165 14808782075760704434039)
                  ·
                    rfl

theorem cell20_32445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_32445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32445 prefixEnd_32445 := by exact prefixLift 32445
  have htrace : WordTrace (prefixWord ++ tailWord_32445) baseStart_32445 baseEnd_32445 := by
    simpa [prefixWord, tailWord_32445, baseEnd_32445] using wordTrace_append hprefix tailTrace_32445
  have hstable : (prefixWord ++ tailWord_32445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32445).length < 2 ^ (prefixWord ++ tailWord_32445).sum := by decide
  have hdescent : baseEnd_32445 < baseStart_32445 := by decide
  rcases family_descends (prefixWord ++ tailWord_32445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32459 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 7]
def baseStart_32459 : Nat := 118140960795 + 32459 * 2 ^ 59
def prefixEnd_32459 : Nat := 4983230072969 + 3 ^ 40 * 32459 * 2
def baseEnd_32459 : Nat := 14815172057238877967315

theorem tailTrace_32459 : CollatzResearch.WordTrace tailWord_32459 prefixEnd_32459 14815172057238877967315 := by
  unfold tailWord_32459
  simp only [CollatzResearch.WordTrace]
  refine ⟨1183876989414061400964431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 789251326276040933976287 1183876989414061400964431)
  ·
    refine ⟨1775815484121092101446647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1183876989414061400964431 1775815484121092101446647)
    ·
      refine ⟨2663723226181638152169971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1775815484121092101446647 2663723226181638152169971)
      ·
        refine ⟨3995584839272457228254957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2663723226181638152169971 3995584839272457228254957)
        ·
          refine ⟨1498344314727171460595609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3995584839272457228254957 1498344314727171460595609)
          ·
            refine ⟨1123758236045378595446707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1498344314727171460595609 1123758236045378595446707)
            ·
              refine ⟨1685637354068067893170061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123758236045378595446707 1685637354068067893170061)
              ·
                refine ⟨632114007775525459938773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1685637354068067893170061 632114007775525459938773)
                ·
                  refine ⟨14815172057238877967315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 632114007775525459938773 14815172057238877967315)
                  ·
                    rfl

theorem cell20_32459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_32459 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32459 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32459 prefixEnd_32459 := by exact prefixLift 32459
  have htrace : WordTrace (prefixWord ++ tailWord_32459) baseStart_32459 baseEnd_32459 := by
    simpa [prefixWord, tailWord_32459, baseEnd_32459] using wordTrace_append hprefix tailTrace_32459
  have hstable : (prefixWord ++ tailWord_32459).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32459).length < 2 ^ (prefixWord ++ tailWord_32459).sum := by decide
  have hdescent : baseEnd_32459 < baseStart_32459 := by decide
  rcases family_descends (prefixWord ++ tailWord_32459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32493 : List Nat := [1, 5, 1, 2, 1, 2, 2, 3, 3]
def baseStart_32493 : Nat := 118140960795 + 32493 * 2 ^ 59
def prefixEnd_32493 : Nat := 4983230072969 + 3 ^ 40 * 32493 * 2
def baseEnd_32493 : Nat := 14830690583685870833843

theorem tailTrace_32493 : CollatzResearch.WordTrace tailWord_32493 prefixEnd_32493 14830690583685870833843 := by
  unfold tailWord_32493
  simp only [CollatzResearch.WordTrace]
  refine ⟨1185117071290885207702133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 790078047527256805134755 1185117071290885207702133)
  ·
    refine ⟨111104725433520488222075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1185117071290885207702133 111104725433520488222075)
    ·
      refine ⟨166657088150280732333113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111104725433520488222075 166657088150280732333113)
      ·
        refine ⟨124992816112710549249835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166657088150280732333113 124992816112710549249835)
        ·
          refine ⟨187489224169065823874753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124992816112710549249835 187489224169065823874753)
          ·
            refine ⟨140616918126799367906065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187489224169065823874753 140616918126799367906065)
            ·
              refine ⟨105462688595099525929549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140616918126799367906065 105462688595099525929549)
              ·
                refine ⟨39548508223162322223581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105462688595099525929549 39548508223162322223581)
                ·
                  refine ⟨14830690583685870833843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39548508223162322223581 14830690583685870833843)
                  ·
                    rfl

theorem cell20_32493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_32493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32493 prefixEnd_32493 := by exact prefixLift 32493
  have htrace : WordTrace (prefixWord ++ tailWord_32493) baseStart_32493 baseEnd_32493 := by
    simpa [prefixWord, tailWord_32493, baseEnd_32493] using wordTrace_append hprefix tailTrace_32493
  have hstable : (prefixWord ++ tailWord_32493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32493).length < 2 ^ (prefixWord ++ tailWord_32493).sum := by decide
  have hdescent : baseEnd_32493 < baseStart_32493 := by decide
  rcases family_descends (prefixWord ++ tailWord_32493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32538 : List Nat := [3, 1, 1, 3, 2, 3, 2, 1, 4]
def baseStart_32538 : Nat := 118140960795 + 32538 * 2 ^ 59
def prefixEnd_32538 : Nat := 4983230072969 + 3 ^ 40 * 32538 * 2
def baseEnd_32538 : Nat := 14851229809865714333659

theorem tailTrace_32538 : CollatzResearch.WordTrace tailWord_32538 prefixEnd_32538 14851229809865714333659 := by
  unfold tailWord_32538
  simp only [CollatzResearch.WordTrace]
  refine ⟨296689589031964473272567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 791172237418571928726845 296689589031964473272567)
  ·
    refine ⟨445034383547946709908851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296689589031964473272567 445034383547946709908851)
    ·
      refine ⟨667551575321920064863277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445034383547946709908851 667551575321920064863277)
      ·
        refine ⟨250331840745720024323729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 667551575321920064863277 250331840745720024323729)
        ·
          refine ⟨187748880559290018242797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250331840745720024323729 187748880559290018242797)
          ·
            refine ⟨70405830209733756841049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187748880559290018242797 70405830209733756841049)
            ·
              refine ⟨52804372657300317630787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70405830209733756841049 52804372657300317630787)
              ·
                refine ⟨79206558985950476446181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52804372657300317630787 79206558985950476446181)
                ·
                  refine ⟨14851229809865714333659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79206558985950476446181 14851229809865714333659)
                  ·
                    rfl

theorem cell20_32538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_32538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32538 prefixEnd_32538 := by exact prefixLift 32538
  have htrace : WordTrace (prefixWord ++ tailWord_32538) baseStart_32538 baseEnd_32538 := by
    simpa [prefixWord, tailWord_32538, baseEnd_32538] using wordTrace_append hprefix tailTrace_32538
  have hstable : (prefixWord ++ tailWord_32538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32538).length < 2 ^ (prefixWord ++ tailWord_32538).sum := by decide
  have hdescent : baseEnd_32538 < baseStart_32538 := by decide
  rcases family_descends (prefixWord ++ tailWord_32538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32548 : List Nat := [2, 3, 1, 3, 2, 2, 3, 1, 3]
def baseStart_32548 : Nat := 118140960795 + 32548 * 2 ^ 59
def prefixEnd_32548 : Nat := 4983230072969 + 3 ^ 40 * 32548 * 2
def baseEnd_32548 : Nat := 14855794082350124000285

theorem tailTrace_32548 : CollatzResearch.WordTrace tailWord_32548 prefixEnd_32548 14855794082350124000285 := by
  unfold tailWord_32548
  simp only [CollatzResearch.WordTrace]
  refine ⟨593561543045814800477149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 791415390727753067302865 593561543045814800477149)
  ·
    refine ⟨222585578642180550178931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 593561543045814800477149 222585578642180550178931)
    ·
      refine ⟨333878367963270825268397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222585578642180550178931 333878367963270825268397)
      ·
        refine ⟨125204387986226559475649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333878367963270825268397 125204387986226559475649)
        ·
          refine ⟨93903290989669919606737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125204387986226559475649 93903290989669919606737)
          ·
            refine ⟨70427468242252439705053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93903290989669919606737 70427468242252439705053)
            ·
              refine ⟨26410300590844664889395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70427468242252439705053 26410300590844664889395)
              ·
                refine ⟨39615450886266997334093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26410300590844664889395 39615450886266997334093)
                ·
                  refine ⟨14855794082350124000285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39615450886266997334093 14855794082350124000285)
                  ·
                    rfl

theorem cell20_32548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_32548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32548 prefixEnd_32548 := by exact prefixLift 32548
  have htrace : WordTrace (prefixWord ++ tailWord_32548) baseStart_32548 baseEnd_32548 := by
    simpa [prefixWord, tailWord_32548, baseEnd_32548] using wordTrace_append hprefix tailTrace_32548
  have hstable : (prefixWord ++ tailWord_32548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32548).length < 2 ^ (prefixWord ++ tailWord_32548).sum := by decide
  have hdescent : baseEnd_32548 < baseStart_32548 := by decide
  rcases family_descends (prefixWord ++ tailWord_32548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32558 : List Nat := [4, 1, 3, 2, 3, 1, 2, 4]
def baseStart_32558 : Nat := 118140960795 + 32558 * 2 ^ 59
def prefixEnd_32558 : Nat := 4983230072969 + 3 ^ 40 * 32558 * 2
def baseEnd_32558 : Nat := 4953452784944844555637

theorem tailTrace_32558 : CollatzResearch.WordTrace tailWord_32558 prefixEnd_32558 4953452784944844555637 := by
  unfold tailWord_32558
  simp only [CollatzResearch.WordTrace]
  refine ⟨148435977006925163602291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 791658544036934205878885 148435977006925163602291)
  ·
    refine ⟨222653965510387745403437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148435977006925163602291 222653965510387745403437)
    ·
      refine ⟨83495237066395404526289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222653965510387745403437 83495237066395404526289)
      ·
        refine ⟨62621427799796553394717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83495237066395404526289 62621427799796553394717)
        ·
          refine ⟨23483035424923707523019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62621427799796553394717 23483035424923707523019)
          ·
            refine ⟨35224553137385561284529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23483035424923707523019 35224553137385561284529)
            ·
              refine ⟨26418414853039170963397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35224553137385561284529 26418414853039170963397)
              ·
                refine ⟨4953452784944844555637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26418414853039170963397 4953452784944844555637)
                ·
                  rfl

theorem cell20_32558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_32558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32558 prefixEnd_32558 := by exact prefixLift 32558
  have htrace : WordTrace (prefixWord ++ tailWord_32558) baseStart_32558 baseEnd_32558 := by
    simpa [prefixWord, tailWord_32558, baseEnd_32558] using wordTrace_append hprefix tailTrace_32558
  have hstable : (prefixWord ++ tailWord_32558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32558).length < 2 ^ (prefixWord ++ tailWord_32558).sum := by decide
  have hdescent : baseEnd_32558 < baseStart_32558 := by decide
  rcases family_descends (prefixWord ++ tailWord_32558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32562 : List Nat := [3, 2, 1, 1, 3, 4, 2, 4]
def baseStart_32562 : Nat := 118140960795 + 32562 * 2 ^ 59
def prefixEnd_32562 : Nat := 4983230072969 + 3 ^ 40 * 32562 * 2
def baseEnd_32562 : Nat := 4954061354609432511187

theorem tailTrace_32562 : CollatzResearch.WordTrace tailWord_32562 prefixEnd_32562 4954061354609432511187 := by
  unfold tailWord_32562
  simp only [CollatzResearch.WordTrace]
  refine ⟨296908427010227497990985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 791755805360606661309293 296908427010227497990985)
  ·
    refine ⟨222681320257670623493239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296908427010227497990985 222681320257670623493239)
    ·
      refine ⟨334021980386505935239859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222681320257670623493239 334021980386505935239859)
      ·
        refine ⟨501032970579758902859789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334021980386505935239859 501032970579758902859789)
        ·
          refine ⟨187887363967409588572421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 501032970579758902859789 187887363967409588572421)
          ·
            refine ⟨35228880743889297857329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187887363967409588572421 35228880743889297857329)
            ·
              refine ⟨26421660557916973392997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35228880743889297857329 26421660557916973392997)
              ·
                refine ⟨4954061354609432511187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26421660557916973392997 4954061354609432511187)
                ·
                  rfl

theorem cell20_32562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_32562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32562 prefixEnd_32562 := by exact prefixLift 32562
  have htrace : WordTrace (prefixWord ++ tailWord_32562) baseStart_32562 baseEnd_32562 := by
    simpa [prefixWord, tailWord_32562, baseEnd_32562] using wordTrace_append hprefix tailTrace_32562
  have hstable : (prefixWord ++ tailWord_32562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32562).length < 2 ^ (prefixWord ++ tailWord_32562).sum := by decide
  have hdescent : baseEnd_32562 < baseStart_32562 := by decide
  rcases family_descends (prefixWord ++ tailWord_32562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32589 : List Nat := [1, 6, 1, 2, 1, 2, 3, 2, 2]
def baseStart_32589 : Nat := 118140960795 + 32589 * 2 ^ 59
def prefixEnd_32589 : Nat := 4983230072969 + 3 ^ 40 * 32589 * 2
def baseEnd_32589 : Nat := 14874507599536203633451

theorem tailTrace_32589 : CollatzResearch.WordTrace tailWord_32589 prefixEnd_32589 14874507599536203633451 := by
  unfold tailWord_32589
  simp only [CollatzResearch.WordTrace]
  refine ⟨1188618478943093603196821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 792412319295395735464547 1188618478943093603196821)
  ·
    refine ⟨55716491200457512649851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1188618478943093603196821 55716491200457512649851)
    ·
      refine ⟨83574736800686268974777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55716491200457512649851 83574736800686268974777)
      ·
        refine ⟨62681052600514701731083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83574736800686268974777 62681052600514701731083)
        ·
          refine ⟨94021578900772052596625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62681052600514701731083 94021578900772052596625)
          ·
            refine ⟨70516184175579039447469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94021578900772052596625 70516184175579039447469)
            ·
              refine ⟨26443569065842139792801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70516184175579039447469 26443569065842139792801)
              ·
                refine ⟨19832676799381604844601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26443569065842139792801 19832676799381604844601)
                ·
                  refine ⟨14874507599536203633451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19832676799381604844601 14874507599536203633451)
                  ·
                    rfl

theorem cell20_32589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_32589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32589 prefixEnd_32589 := by exact prefixLift 32589
  have htrace : WordTrace (prefixWord ++ tailWord_32589) baseStart_32589 baseEnd_32589 := by
    simpa [prefixWord, tailWord_32589, baseEnd_32589] using wordTrace_append hprefix tailTrace_32589
  have hstable : (prefixWord ++ tailWord_32589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32589).length < 2 ^ (prefixWord ++ tailWord_32589).sum := by decide
  have hdescent : baseEnd_32589 < baseStart_32589 := by decide
  rcases family_descends (prefixWord ++ tailWord_32589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32607 : List Nat := [1, 1, 2, 3, 1, 4, 4, 1, 3]
def baseStart_32607 : Nat := 118140960795 + 32607 * 2 ^ 59
def prefixEnd_32607 : Nat := 4983230072969 + 3 ^ 40 * 32607 * 2
def baseEnd_32607 : Nat := 14882723290008141033377

theorem tailTrace_32607 : CollatzResearch.WordTrace tailWord_32607 prefixEnd_32607 14882723290008141033377 := by
  unfold tailWord_32607
  simp only [CollatzResearch.WordTrace]
  refine ⟨1189274992877882677352075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 792849995251921784901383 1189274992877882677352075)
  ·
    refine ⟨1783912489316824016028113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1189274992877882677352075 1783912489316824016028113)
    ·
      refine ⟨1337934366987618012021085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1783912489316824016028113 1337934366987618012021085)
      ·
        refine ⟨501725387620356754507907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1337934366987618012021085 501725387620356754507907)
        ·
          refine ⟨752588081430535131761861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501725387620356754507907 752588081430535131761861)
          ·
            refine ⟨141110265268225337205349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 752588081430535131761861 141110265268225337205349)
            ·
              refine ⟨26458174737792250726003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141110265268225337205349 26458174737792250726003)
              ·
                refine ⟨39687262106688376089005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26458174737792250726003 39687262106688376089005)
                ·
                  refine ⟨14882723290008141033377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39687262106688376089005 14882723290008141033377)
                  ·
                    rfl

theorem cell20_32607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 3].length) (baseStart_32607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32607 prefixEnd_32607 := by exact prefixLift 32607
  have htrace : WordTrace (prefixWord ++ tailWord_32607) baseStart_32607 baseEnd_32607 := by
    simpa [prefixWord, tailWord_32607, baseEnd_32607] using wordTrace_append hprefix tailTrace_32607
  have hstable : (prefixWord ++ tailWord_32607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32607).length < 2 ^ (prefixWord ++ tailWord_32607).sum := by decide
  have hdescent : baseEnd_32607 < baseStart_32607 := by decide
  rcases family_descends (prefixWord ++ tailWord_32607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32687 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 5]
def baseStart_32687 : Nat := 118140960795 + 32687 * 2 ^ 59
def prefixEnd_32687 : Nat := 4983230072969 + 3 ^ 40 * 32687 * 2
def baseEnd_32687 : Nat := 14919237469883418366383

theorem tailTrace_32687 : CollatzResearch.WordTrace tailWord_32687 prefixEnd_32687 14919237469883418366383 := by
  unfold tailWord_32687
  simp only [CollatzResearch.WordTrace]
  refine ⟨1192192832588056340264315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 794795221725370893509543 1192192832588056340264315)
  ·
    refine ⟨1788289248882084510396473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1192192832588056340264315 1788289248882084510396473)
    ·
      refine ⟨1341216936661563382797355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1788289248882084510396473 1341216936661563382797355)
      ·
        refine ⟨2011825404992345074196033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1341216936661563382797355 2011825404992345074196033)
        ·
          refine ⟨1508869053744258805647025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2011825404992345074196033 1508869053744258805647025)
          ·
            refine ⟨1131651790308194104235269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1508869053744258805647025 1131651790308194104235269)
            ·
              refine ⟨212184710682786394544113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1131651790308194104235269 212184710682786394544113)
              ·
                refine ⟨159138533012089795908085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212184710682786394544113 159138533012089795908085)
                ·
                  refine ⟨14919237469883418366383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159138533012089795908085 14919237469883418366383)
                  ·
                    rfl

theorem cell20_32687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_32687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32687 prefixEnd_32687 := by exact prefixLift 32687
  have htrace : WordTrace (prefixWord ++ tailWord_32687) baseStart_32687 baseEnd_32687 := by
    simpa [prefixWord, tailWord_32687, baseEnd_32687] using wordTrace_append hprefix tailTrace_32687
  have hstable : (prefixWord ++ tailWord_32687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32687).length < 2 ^ (prefixWord ++ tailWord_32687).sum := by decide
  have hdescent : baseEnd_32687 < baseStart_32687 := by decide
  rcases family_descends (prefixWord ++ tailWord_32687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32718 : List Nat := [4, 1, 1, 1, 2, 2, 2, 7]
def baseStart_32718 : Nat := 118140960795 + 32718 * 2 ^ 59
def prefixEnd_32718 : Nat := 4983230072969 + 3 ^ 40 * 32718 * 2
def baseEnd_32718 : Nat := 4977795571528362777641

theorem tailTrace_32718 : CollatzResearch.WordTrace tailWord_32718 prefixEnd_32718 4977795571528362777641 := by
  unfold tailWord_32718
  simp only [CollatzResearch.WordTrace]
  refine ⟨149165436934468579330351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 795548996983832423095205 149165436934468579330351)
  ·
    refine ⟨223748155401702868995527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149165436934468579330351 223748155401702868995527)
    ·
      refine ⟨335622233102554303493291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223748155401702868995527 335622233102554303493291)
      ·
        refine ⟨503433349653831455239937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335622233102554303493291 503433349653831455239937)
        ·
          refine ⟨377575012240373591429953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503433349653831455239937 377575012240373591429953)
          ·
            refine ⟨283181259180280193572465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377575012240373591429953 283181259180280193572465)
            ·
              refine ⟨212385944385210145179349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283181259180280193572465 212385944385210145179349)
              ·
                refine ⟨4977795571528362777641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 212385944385210145179349 4977795571528362777641)
                ·
                  rfl

theorem cell20_32718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_32718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32718 prefixEnd_32718 := by exact prefixLift 32718
  have htrace : WordTrace (prefixWord ++ tailWord_32718) baseStart_32718 baseEnd_32718 := by
    simpa [prefixWord, tailWord_32718, baseEnd_32718] using wordTrace_append hprefix tailTrace_32718
  have hstable : (prefixWord ++ tailWord_32718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32718).length < 2 ^ (prefixWord ++ tailWord_32718).sum := by decide
  have hdescent : baseEnd_32718 < baseStart_32718 := by decide
  rcases family_descends (prefixWord ++ tailWord_32718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32735 : List Nat := [1, 1, 2, 3, 4, 1, 4, 4]
def baseStart_32735 : Nat := 118140960795 + 32735 * 2 ^ 59
def prefixEnd_32735 : Nat := 4983230072969 + 3 ^ 40 * 32735 * 2
def baseEnd_32735 : Nat := 4980381992602861588729

theorem tailTrace_32735 : CollatzResearch.WordTrace tailWord_32735 prefixEnd_32735 4980381992602861588729 := by
  unfold tailWord_32735
  simp only [CollatzResearch.WordTrace]
  refine ⟨1193943536414160538011659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 795962357609440358674439 1193943536414160538011659)
  ·
    refine ⟨1790915304621240807017489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1193943536414160538011659 1790915304621240807017489)
    ·
      refine ⟨1343186478465930605263117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1790915304621240807017489 1343186478465930605263117)
      ·
        refine ⟨503694929424723976973669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1343186478465930605263117 503694929424723976973669)
        ·
          refine ⟨94442799267135745682563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 503694929424723976973669 94442799267135745682563)
          ·
            refine ⟨141664198900703618523845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94442799267135745682563 141664198900703618523845)
            ·
              refine ⟨26562037293881928473221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141664198900703618523845 26562037293881928473221)
              ·
                refine ⟨4980381992602861588729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26562037293881928473221 4980381992602861588729)
                ·
                  rfl

theorem cell20_32735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 4].length) (baseStart_32735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32735 prefixEnd_32735 := by exact prefixLift 32735
  have htrace : WordTrace (prefixWord ++ tailWord_32735) baseStart_32735 baseEnd_32735 := by
    simpa [prefixWord, tailWord_32735, baseEnd_32735] using wordTrace_append hprefix tailTrace_32735
  have hstable : (prefixWord ++ tailWord_32735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32735).length < 2 ^ (prefixWord ++ tailWord_32735).sum := by decide
  have hdescent : baseEnd_32735 < baseStart_32735 := by decide
  rcases family_descends (prefixWord ++ tailWord_32735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32763 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 5]
def baseStart_32763 : Nat := 118140960795 + 32763 * 2 ^ 59
def prefixEnd_32763 : Nat := 4983230072969 + 3 ^ 40 * 32763 * 2
def baseEnd_32763 : Nat := 14953925940764931832739

theorem tailTrace_32763 : CollatzResearch.WordTrace tailWord_32763 prefixEnd_32763 14953925940764931832739 := by
  unfold tailWord_32763
  simp only [CollatzResearch.WordTrace]
  refine ⟨1194964780312721320030943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 796643186875147546687295 1194964780312721320030943)
  ·
    refine ⟨1792447170469081980046415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1194964780312721320030943 1792447170469081980046415)
    ·
      refine ⟨2688670755703622970069623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1792447170469081980046415 2688670755703622970069623)
      ·
        refine ⟨4033006133555434455104435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2688670755703622970069623 4033006133555434455104435)
        ·
          refine ⟨6049509200333151682656653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4033006133555434455104435 6049509200333151682656653)
          ·
            refine ⟨2268565950124931880996245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6049509200333151682656653 2268565950124931880996245)
            ·
              refine ⟨106339028912106181921699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2268565950124931880996245 106339028912106181921699)
              ·
                refine ⟨159508543368159272882549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106339028912106181921699 159508543368159272882549)
                ·
                  refine ⟨14953925940764931832739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159508543368159272882549 14953925940764931832739)
                  ·
                    rfl

theorem cell20_32763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 5].length) (baseStart_32763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32763 prefixEnd_32763 := by exact prefixLift 32763
  have htrace : WordTrace (prefixWord ++ tailWord_32763) baseStart_32763 baseEnd_32763 := by
    simpa [prefixWord, tailWord_32763, baseEnd_32763] using wordTrace_append hprefix tailTrace_32763
  have hstable : (prefixWord ++ tailWord_32763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32763).length < 2 ^ (prefixWord ++ tailWord_32763).sum := by decide
  have hdescent : baseEnd_32763 < baseStart_32763 := by decide
  rcases family_descends (prefixWord ++ tailWord_32763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32772 : List Nat := [2, 3, 2, 4, 2, 1, 2, 1, 3]
def baseStart_32772 : Nat := 118140960795 + 32772 * 2 ^ 59
def prefixEnd_32772 : Nat := 4983230072969 + 3 ^ 40 * 32772 * 2
def baseEnd_32772 : Nat := 14958033786000900532703

theorem tailTrace_32772 : CollatzResearch.WordTrace tailWord_32772 prefixEnd_32772 14958033786000900532703 := by
  unfold tailWord_32772
  simp only [CollatzResearch.WordTrace]
  refine ⟨597646518640057928554285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 796862024853410571405713 597646518640057928554285)
  ·
    refine ⟨224117444490021723207857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 597646518640057928554285 224117444490021723207857)
    ·
      refine ⟨168088083367516292405893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224117444490021723207857 168088083367516292405893)
      ·
        refine ⟨31516515631409304826105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168088083367516292405893 31516515631409304826105)
        ·
          refine ⟨23637386723556978619579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31516515631409304826105 23637386723556978619579)
          ·
            refine ⟨35456080085335467929369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23637386723556978619579 35456080085335467929369)
            ·
              refine ⟨26592060064001600947027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35456080085335467929369 26592060064001600947027)
              ·
                refine ⟨39888090096002401420541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26592060064001600947027 39888090096002401420541)
                ·
                  refine ⟨14958033786000900532703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39888090096002401420541 14958033786000900532703)
                  ·
                    rfl

theorem cell20_32772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_32772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32772 prefixEnd_32772 := by exact prefixLift 32772
  have htrace : WordTrace (prefixWord ++ tailWord_32772) baseStart_32772 baseEnd_32772 := by
    simpa [prefixWord, tailWord_32772, baseEnd_32772] using wordTrace_append hprefix tailTrace_32772
  have hstable : (prefixWord ++ tailWord_32772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32772).length < 2 ^ (prefixWord ++ tailWord_32772).sum := by decide
  have hdescent : baseEnd_32772 < baseStart_32772 := by decide
  rcases family_descends (prefixWord ++ tailWord_32772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32780 : List Nat := [2, 2, 1, 2, 3, 1, 3, 3, 3]
def baseStart_32780 : Nat := 118140960795 + 32780 * 2 ^ 59
def prefixEnd_32780 : Nat := 4983230072969 + 3 ^ 40 * 32780 * 2
def baseEnd_32780 : Nat := 14961685203988428266003

theorem tailTrace_32780 : CollatzResearch.WordTrace tailWord_32780 prefixEnd_32780 14961685203988428266003 := by
  unfold tailWord_32780
  simp only [CollatzResearch.WordTrace]
  refine ⟨597792410625566611699897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 797056547500755482266529 597792410625566611699897)
  ·
    refine ⟨448344307969174958774923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 597792410625566611699897 448344307969174958774923)
    ·
      refine ⟨672516461953762438162385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448344307969174958774923 672516461953762438162385)
      ·
        refine ⟨504387346465321828621789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 672516461953762438162385 504387346465321828621789)
        ·
          refine ⟨189145254924495685733171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 504387346465321828621789 189145254924495685733171)
          ·
            refine ⟨283717882386743528599757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189145254924495685733171 283717882386743528599757)
            ·
              refine ⟨106394205895028823224909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283717882386743528599757 106394205895028823224909)
              ·
                refine ⟨39897827210635808709341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106394205895028823224909 39897827210635808709341)
                ·
                  refine ⟨14961685203988428266003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39897827210635808709341 14961685203988428266003)
                  ·
                    rfl

theorem cell20_32780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_32780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32780 prefixEnd_32780 := by exact prefixLift 32780
  have htrace : WordTrace (prefixWord ++ tailWord_32780) baseStart_32780 baseEnd_32780 := by
    simpa [prefixWord, tailWord_32780, baseEnd_32780] using wordTrace_append hprefix tailTrace_32780
  have hstable : (prefixWord ++ tailWord_32780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32780).length < 2 ^ (prefixWord ++ tailWord_32780).sum := by decide
  have hdescent : baseEnd_32780 < baseStart_32780 := by decide
  rcases family_descends (prefixWord ++ tailWord_32780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32794 : List Nat := [3, 1, 1, 3, 1, 3, 2, 6]
def baseStart_32794 : Nat := 118140960795 + 32794 * 2 ^ 59
def prefixEnd_32794 : Nat := 4983230072969 + 3 ^ 40 * 32794 * 2
def baseEnd_32794 : Nat := 4989358395155533933093

theorem tailTrace_32794 : CollatzResearch.WordTrace tailWord_32794 prefixEnd_32794 4989358395155533933093 := by
  unfold tailWord_32794
  simp only [CollatzResearch.WordTrace]
  refine ⟨299023860800103403602359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 797396962133609076272957 299023860800103403602359)
  ·
    refine ⟨448535791200155105403539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299023860800103403602359 448535791200155105403539)
    ·
      refine ⟨672803686800232658105309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448535791200155105403539 672803686800232658105309)
      ·
        refine ⟨252301382550087246789491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 672803686800232658105309 252301382550087246789491)
        ·
          refine ⟨378452073825130870184237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252301382550087246789491 378452073825130870184237)
          ·
            refine ⟨141919527684424076319089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 378452073825130870184237 141919527684424076319089)
            ·
              refine ⟨106439645763318057239317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141919527684424076319089 106439645763318057239317)
              ·
                refine ⟨4989358395155533933093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106439645763318057239317 4989358395155533933093)
                ·
                  rfl

theorem cell20_32794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_32794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32794 prefixEnd_32794 := by exact prefixLift 32794
  have htrace : WordTrace (prefixWord ++ tailWord_32794) baseStart_32794 baseEnd_32794 := by
    simpa [prefixWord, tailWord_32794, baseEnd_32794] using wordTrace_append hprefix tailTrace_32794
  have hstable : (prefixWord ++ tailWord_32794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32794).length < 2 ^ (prefixWord ++ tailWord_32794).sum := by decide
  have hdescent : baseEnd_32794 < baseStart_32794 := by decide
  rcases family_descends (prefixWord ++ tailWord_32794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32818 : List Nat := [3, 2, 1, 1, 2, 3, 1, 4, 3]
def baseStart_32818 : Nat := 118140960795 + 32818 * 2 ^ 59
def prefixEnd_32818 : Nat := 4983230072969 + 3 ^ 40 * 32818 * 2
def baseEnd_32818 : Nat := 14979029439429184999181

theorem tailTrace_32818 : CollatzResearch.WordTrace tailWord_32818 prefixEnd_32818 14979029439429184999181 := by
  unfold tailWord_32818
  simp only [CollatzResearch.WordTrace]
  refine ⟨299242698778366428320777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 797980530075643808855405 299242698778366428320777)
  ·
    refine ⟨224432024083774821240583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299242698778366428320777 224432024083774821240583)
    ·
      refine ⟨336648036125662231860875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224432024083774821240583 336648036125662231860875)
      ·
        refine ⟨504972054188493347791313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336648036125662231860875 504972054188493347791313)
        ·
          refine ⟨378729040641370010843485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504972054188493347791313 378729040641370010843485)
          ·
            refine ⟨142023390240513754066307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 378729040641370010843485 142023390240513754066307)
            ·
              refine ⟨213035085360770631099461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142023390240513754066307 213035085360770631099461)
              ·
                refine ⟨39944078505144493331149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213035085360770631099461 39944078505144493331149)
                ·
                  refine ⟨14979029439429184999181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39944078505144493331149 14979029439429184999181)
                  ·
                    rfl

theorem cell20_32818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_32818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32818 prefixEnd_32818 := by exact prefixLift 32818
  have htrace : WordTrace (prefixWord ++ tailWord_32818) baseStart_32818 baseEnd_32818 := by
    simpa [prefixWord, tailWord_32818, baseEnd_32818] using wordTrace_append hprefix tailTrace_32818
  have hstable : (prefixWord ++ tailWord_32818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32818).length < 2 ^ (prefixWord ++ tailWord_32818).sum := by decide
  have hdescent : baseEnd_32818 < baseStart_32818 := by decide
  rcases family_descends (prefixWord ++ tailWord_32818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32821 : List Nat := [1, 3, 3, 1, 1, 1, 6, 2, 2]
def baseStart_32821 : Nat := 118140960795 + 32821 * 2 ^ 59
def prefixEnd_32821 : Nat := 4983230072969 + 3 ^ 40 * 32821 * 2
def baseEnd_32821 : Nat := 14980398721174507899169

theorem tailTrace_32821 : CollatzResearch.WordTrace tailWord_32821 prefixEnd_32821 14980398721174507899169 := by
  unfold tailWord_32821
  simp only [CollatzResearch.WordTrace]
  refine ⟨1197080214102597225642317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 798053476068398150428211 1197080214102597225642317)
  ·
    refine ⟨448905080288473959615869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1197080214102597225642317 448905080288473959615869)
    ·
      refine ⟨168339405108177734855951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448905080288473959615869 168339405108177734855951)
      ·
        refine ⟨252509107662266602283927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168339405108177734855951 252509107662266602283927)
        ·
          refine ⟨378763661493399903425891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252509107662266602283927 378763661493399903425891)
          ·
            refine ⟨568145492240099855138837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378763661493399903425891 568145492240099855138837)
            ·
              refine ⟨26631819948754680709633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 568145492240099855138837 26631819948754680709633)
              ·
                refine ⟨19973864961566010532225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26631819948754680709633 19973864961566010532225)
                ·
                  refine ⟨14980398721174507899169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19973864961566010532225 14980398721174507899169)
                  ·
                    rfl

theorem cell20_32821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 2].length) (baseStart_32821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32821 prefixEnd_32821 := by exact prefixLift 32821
  have htrace : WordTrace (prefixWord ++ tailWord_32821) baseStart_32821 baseEnd_32821 := by
    simpa [prefixWord, tailWord_32821, baseEnd_32821] using wordTrace_append hprefix tailTrace_32821
  have hstable : (prefixWord ++ tailWord_32821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32821).length < 2 ^ (prefixWord ++ tailWord_32821).sum := by decide
  have hdescent : baseEnd_32821 < baseStart_32821 := by decide
  rcases family_descends (prefixWord ++ tailWord_32821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32832 : List Nat := [2, 1, 1, 2, 2, 4, 3, 5]
def baseStart_32832 : Nat := 118140960795 + 32832 * 2 ^ 59
def prefixEnd_32832 : Nat := 4983230072969 + 3 ^ 40 * 32832 * 2
def baseEnd_32832 : Nat := 4995139806969119510819

theorem tailTrace_32832 : CollatzResearch.WordTrace tailWord_32832 prefixEnd_32832 4995139806969119510819 := by
  unfold tailWord_32832
  simp only [CollatzResearch.WordTrace]
  refine ⟨598740708531373052146375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 798320944708497402861833 598740708531373052146375)
  ·
    refine ⟨898111062797059578219563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 598740708531373052146375 898111062797059578219563)
    ·
      refine ⟨1347166594195589367329345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 898111062797059578219563 1347166594195589367329345)
      ·
        refine ⟨1010374945646692025497009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1347166594195589367329345 1010374945646692025497009)
        ·
          refine ⟨757781209235019019122757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1010374945646692025497009 757781209235019019122757)
          ·
            refine ⟨142083976731566066085517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 757781209235019019122757 142083976731566066085517)
            ·
              refine ⟨53281491274337274782069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142083976731566066085517 53281491274337274782069)
              ·
                refine ⟨4995139806969119510819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53281491274337274782069 4995139806969119510819)
                ·
                  rfl

theorem cell20_32832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_32832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32832 prefixEnd_32832 := by exact prefixLift 32832
  have htrace : WordTrace (prefixWord ++ tailWord_32832) baseStart_32832 baseEnd_32832 := by
    simpa [prefixWord, tailWord_32832, baseEnd_32832] using wordTrace_append hprefix tailTrace_32832
  have hstable : (prefixWord ++ tailWord_32832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32832).length < 2 ^ (prefixWord ++ tailWord_32832).sum := by decide
  have hdescent : baseEnd_32832 < baseStart_32832 := by decide
  rcases family_descends (prefixWord ++ tailWord_32832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32880 : List Nat := [2, 1, 1, 1, 5, 2, 2, 4, 2]
def baseStart_32880 : Nat := 118140960795 + 32880 * 2 ^ 59
def prefixEnd_32880 : Nat := 4983230072969 + 3 ^ 40 * 32880 * 2
def baseEnd_32880 : Nat := 15007327928832524932261

theorem tailTrace_32880 : CollatzResearch.WordTrace tailWord_32880 prefixEnd_32880 15007327928832524932261 := by
  unfold tailWord_32880
  simp only [CollatzResearch.WordTrace]
  refine ⟨599616060444425151020047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 799488080592566868026729 599616060444425151020047)
  ·
    refine ⟨899424090666637726530071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 599616060444425151020047 899424090666637726530071)
    ·
      refine ⟨1349136135999956589795107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 899424090666637726530071 1349136135999956589795107)
      ·
        refine ⟨2023704203999934884692661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1349136135999956589795107 2023704203999934884692661)
        ·
          refine ⟨189722269124993895439937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2023704203999934884692661 189722269124993895439937)
          ·
            refine ⟨142291701843745421579953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189722269124993895439937 142291701843745421579953)
            ·
              refine ⟨106718776382809066184965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142291701843745421579953 106718776382809066184965)
              ·
                refine ⟨20009770571776699909681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106718776382809066184965 20009770571776699909681)
                ·
                  refine ⟨15007327928832524932261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20009770571776699909681 15007327928832524932261)
                  ·
                    rfl

theorem cell20_32880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 2].length) (baseStart_32880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32880 prefixEnd_32880 := by exact prefixLift 32880
  have htrace : WordTrace (prefixWord ++ tailWord_32880) baseStart_32880 baseEnd_32880 := by
    simpa [prefixWord, tailWord_32880, baseEnd_32880] using wordTrace_append hprefix tailTrace_32880
  have hstable : (prefixWord ++ tailWord_32880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32880).length < 2 ^ (prefixWord ++ tailWord_32880).sum := by decide
  have hdescent : baseEnd_32880 < baseStart_32880 := by decide
  rcases family_descends (prefixWord ++ tailWord_32880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32901 : List Nat := [1, 3, 1, 1, 5, 1, 2, 2, 4]
def baseStart_32901 : Nat := 118140960795 + 32901 * 2 ^ 59
def prefixEnd_32901 : Nat := 4983230072969 + 3 ^ 40 * 32901 * 2
def baseEnd_32901 : Nat := 15016912901049785232175

theorem tailTrace_32901 : CollatzResearch.WordTrace tailWord_32901 prefixEnd_32901 15016912901049785232175 := by
  unfold tailWord_32901
  simp only [CollatzResearch.WordTrace]
  refine ⟨1199998053812770888554557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 799998702541847259036371 1199998053812770888554557)
  ·
    refine ⟨449999270179789083207959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1199998053812770888554557 449999270179789083207959)
    ·
      refine ⟨674998905269683624811939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449999270179789083207959 674998905269683624811939)
      ·
        refine ⟨1012498357904525437217909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674998905269683624811939 1012498357904525437217909)
        ·
          refine ⟨94921721053549259739179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1012498357904525437217909 94921721053549259739179)
          ·
            refine ⟨142382581580323889608769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94921721053549259739179 142382581580323889608769)
            ·
              refine ⟨106786936185242917206577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142382581580323889608769 106786936185242917206577)
              ·
                refine ⟨80090202138932187904933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106786936185242917206577 80090202138932187904933)
                ·
                  refine ⟨15016912901049785232175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80090202138932187904933 15016912901049785232175)
                  ·
                    rfl

theorem cell20_32901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_32901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32901 prefixEnd_32901 := by exact prefixLift 32901
  have htrace : WordTrace (prefixWord ++ tailWord_32901) baseStart_32901 baseEnd_32901 := by
    simpa [prefixWord, tailWord_32901, baseEnd_32901] using wordTrace_append hprefix tailTrace_32901
  have hstable : (prefixWord ++ tailWord_32901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32901).length < 2 ^ (prefixWord ++ tailWord_32901).sum := by decide
  have hdescent : baseEnd_32901 < baseStart_32901 := by decide
  rcases family_descends (prefixWord ++ tailWord_32901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32904 : List Nat := [2, 1, 3, 4, 1, 3, 2, 4]
def baseStart_32904 : Nat := 118140960795 + 32904 * 2 ^ 59
def prefixEnd_32904 : Nat := 4983230072969 + 3 ^ 40 * 32904 * 2
def baseEnd_32904 : Nat := 5006094060931702710721

theorem tailTrace_32904 : CollatzResearch.WordTrace tailWord_32904 prefixEnd_32904 5006094060931702710721 := by
  unfold tailWord_32904
  simp only [CollatzResearch.WordTrace]
  refine ⟨600053736400951200456883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 800071648534601600609177 600053736400951200456883)
  ·
    refine ⟨900080604601426800685325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 600053736400951200456883 900080604601426800685325)
    ·
      refine ⟨337530226725535050256997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 900080604601426800685325 337530226725535050256997)
      ·
        refine ⟨63286917511037821923187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 337530226725535050256997 63286917511037821923187)
        ·
          refine ⟨94930376266556732884781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63286917511037821923187 94930376266556732884781)
          ·
            refine ⟨35598891099958774831793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94930376266556732884781 35598891099958774831793)
            ·
              refine ⟨26699168324969081123845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35598891099958774831793 26699168324969081123845)
              ·
                refine ⟨5006094060931702710721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26699168324969081123845 5006094060931702710721)
                ·
                  rfl

theorem cell20_32904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 4].length) (baseStart_32904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32904 prefixEnd_32904 := by exact prefixLift 32904
  have htrace : WordTrace (prefixWord ++ tailWord_32904) baseStart_32904 baseEnd_32904 := by
    simpa [prefixWord, tailWord_32904, baseEnd_32904] using wordTrace_append hprefix tailTrace_32904
  have hstable : (prefixWord ++ tailWord_32904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32904).length < 2 ^ (prefixWord ++ tailWord_32904).sum := by decide
  have hdescent : baseEnd_32904 < baseStart_32904 := by decide
  rcases family_descends (prefixWord ++ tailWord_32904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32935 : List Nat := [1, 1, 6, 2, 2, 2, 1, 1, 4]
def baseStart_32935 : Nat := 118140960795 + 32935 * 2 ^ 59
def prefixEnd_32935 : Nat := 4983230072969 + 3 ^ 40 * 32935 * 2
def baseEnd_32935 : Nat := 15032431427496778098703

theorem tailTrace_32935 : CollatzResearch.WordTrace tailWord_32935 prefixEnd_32935 15032431427496778098703 := by
  unfold tailWord_32935
  simp only [CollatzResearch.WordTrace]
  refine ⟨1201238135689594695292259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 800825423793063130194839 1201238135689594695292259)
  ·
    refine ⟨1801857203534392042938389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1201238135689594695292259 1801857203534392042938389)
    ·
      refine ⟨84462056415674627012737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1801857203534392042938389 84462056415674627012737)
      ·
        refine ⟨63346542311755970259553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84462056415674627012737 63346542311755970259553)
        ·
          refine ⟨47509906733816977694665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63346542311755970259553 47509906733816977694665)
          ·
            refine ⟨35632430050362733270999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47509906733816977694665 35632430050362733270999)
            ·
              refine ⟨53448645075544099906499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35632430050362733270999 53448645075544099906499)
              ·
                refine ⟨80172967613316149859749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53448645075544099906499 80172967613316149859749)
                ·
                  refine ⟨15032431427496778098703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80172967613316149859749 15032431427496778098703)
                  ·
                    rfl

theorem cell20_32935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 4].length) (baseStart_32935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32935 prefixEnd_32935 := by exact prefixLift 32935
  have htrace : WordTrace (prefixWord ++ tailWord_32935) baseStart_32935 baseEnd_32935 := by
    simpa [prefixWord, tailWord_32935, baseEnd_32935] using wordTrace_append hprefix tailTrace_32935
  have hstable : (prefixWord ++ tailWord_32935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32935).length < 2 ^ (prefixWord ++ tailWord_32935).sum := by decide
  have hdescent : baseEnd_32935 < baseStart_32935 := by decide
  rcases family_descends (prefixWord ++ tailWord_32935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32945 : List Nat := [1, 2, 2, 5, 3, 1, 2, 1, 3]
def baseStart_32945 : Nat := 118140960795 + 32945 * 2 ^ 59
def prefixEnd_32945 : Nat := 4983230072969 + 3 ^ 40 * 32945 * 2
def baseEnd_32945 : Nat := 15036995699981187765329

theorem tailTrace_32945 : CollatzResearch.WordTrace tailWord_32945 prefixEnd_32945 15036995699981187765329 := by
  unfold tailWord_32945
  simp only [CollatzResearch.WordTrace]
  refine ⟨1201602865653366403156289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 801068577102244268770859 1201602865653366403156289)
  ·
    refine ⟨901202149240024802367217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1201602865653366403156289 901202149240024802367217)
    ·
      refine ⟨675901611930018601775413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 901202149240024802367217 675901611930018601775413)
      ·
        refine ⟨63365776118439243916445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 675901611930018601775413 63365776118439243916445)
        ·
          refine ⟨23762166044414716468667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63365776118439243916445 23762166044414716468667)
          ·
            refine ⟨35643249066622074703001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23762166044414716468667 35643249066622074703001)
            ·
              refine ⟨26732436799966556027251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35643249066622074703001 26732436799966556027251)
              ·
                refine ⟨40098655199949834040877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26732436799966556027251 40098655199949834040877)
                ·
                  refine ⟨15036995699981187765329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40098655199949834040877 15036995699981187765329)
                  ·
                    rfl

theorem cell20_32945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 3].length) (baseStart_32945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32945 prefixEnd_32945 := by exact prefixLift 32945
  have htrace : WordTrace (prefixWord ++ tailWord_32945) baseStart_32945 baseEnd_32945 := by
    simpa [prefixWord, tailWord_32945, baseEnd_32945] using wordTrace_append hprefix tailTrace_32945
  have hstable : (prefixWord ++ tailWord_32945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32945).length < 2 ^ (prefixWord ++ tailWord_32945).sum := by decide
  have hdescent : baseEnd_32945 < baseStart_32945 := by decide
  rcases family_descends (prefixWord ++ tailWord_32945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32946 : List Nat := [3, 2, 1, 1, 1, 3, 4, 5]
def baseStart_32946 : Nat := 118140960795 + 32946 * 2 ^ 59
def prefixEnd_32946 : Nat := 4983230072969 + 3 ^ 40 * 32946 * 2
def baseEnd_32946 : Nat := 5012484042409876243997

theorem tailTrace_32946 : CollatzResearch.WordTrace tailWord_32946 prefixEnd_32946 5012484042409876243997 := by
  unfold tailWord_32946
  simp only [CollatzResearch.WordTrace]
  refine ⟨300409834662435893485673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 801092892433162382628461 300409834662435893485673)
  ·
    refine ⟨225307375996826920114255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300409834662435893485673 225307375996826920114255)
    ·
      refine ⟨337961063995240380171383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225307375996826920114255 337961063995240380171383)
      ·
        refine ⟨506941595992860570257075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337961063995240380171383 506941595992860570257075)
        ·
          refine ⟨760412393989290855385613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506941595992860570257075 760412393989290855385613)
          ·
            refine ⟨285154647745984070769605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 760412393989290855385613 285154647745984070769605)
            ·
              refine ⟨53466496452372013269301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 285154647745984070769605 53466496452372013269301)
              ·
                refine ⟨5012484042409876243997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53466496452372013269301 5012484042409876243997)
                ·
                  rfl

theorem cell20_32946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_32946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_32946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_32946 prefixEnd_32946 := by exact prefixLift 32946
  have htrace : WordTrace (prefixWord ++ tailWord_32946) baseStart_32946 baseEnd_32946 := by
    simpa [prefixWord, tailWord_32946, baseEnd_32946] using wordTrace_append hprefix tailTrace_32946
  have hstable : (prefixWord ++ tailWord_32946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32946).length < 2 ^ (prefixWord ++ tailWord_32946).sum := by decide
  have hdescent : baseEnd_32946 < baseStart_32946 := by decide
  rcases family_descends (prefixWord ++ tailWord_32946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33032 : List Nat := [2, 1, 3, 2, 3, 1, 1, 5, 2]
def baseStart_33032 : Nat := 118140960795 + 33032 * 2 ^ 59
def prefixEnd_33032 : Nat := 4983230072969 + 3 ^ 40 * 33032 * 2
def baseEnd_33032 : Nat := 15076704870595551864973

theorem tailTrace_33032 : CollatzResearch.WordTrace tailWord_33032 prefixEnd_33032 15076704870595551864973 := by
  unfold tailWord_33032
  simp only [CollatzResearch.WordTrace]
  refine ⟨602388008169090130786675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 803184010892120174382233 602388008169090130786675)
  ·
    refine ⟨903582012253635196180013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 602388008169090130786675 903582012253635196180013)
    ·
      refine ⟨338843254595113198567505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 903582012253635196180013 338843254595113198567505)
      ·
        refine ⟨254132440946334898925629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338843254595113198567505 254132440946334898925629)
        ·
          refine ⟨95299665354875587097111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254132440946334898925629 95299665354875587097111)
          ·
            refine ⟨142949498032313380645667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95299665354875587097111 142949498032313380645667)
            ·
              refine ⟨214424247048470070968501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142949498032313380645667 214424247048470070968501)
              ·
                refine ⟨20102273160794069153297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214424247048470070968501 20102273160794069153297)
                ·
                  refine ⟨15076704870595551864973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20102273160794069153297 15076704870595551864973)
                  ·
                    rfl

theorem cell20_33032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 2].length) (baseStart_33032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33032 prefixEnd_33032 := by exact prefixLift 33032
  have htrace : WordTrace (prefixWord ++ tailWord_33032) baseStart_33032 baseEnd_33032 := by
    simpa [prefixWord, tailWord_33032, baseEnd_33032] using wordTrace_append hprefix tailTrace_33032
  have hstable : (prefixWord ++ tailWord_33032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33032).length < 2 ^ (prefixWord ++ tailWord_33032).sum := by decide
  have hdescent : baseEnd_33032 < baseStart_33032 := by decide
  rcases family_descends (prefixWord ++ tailWord_33032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33036 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 6]
def baseStart_33036 : Nat := 118140960795 + 33036 * 2 ^ 59
def prefixEnd_33036 : Nat := 4983230072969 + 3 ^ 40 * 33036 * 2
def baseEnd_33036 : Nat := 15078530579589315731623

theorem tailTrace_33036 : CollatzResearch.WordTrace tailWord_33036 prefixEnd_33036 15078530579589315731623 := by
  unfold tailWord_33036
  simp only [CollatzResearch.WordTrace]
  refine ⟨602460954161844472359481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 803281272215792629812641 602460954161844472359481)
  ·
    refine ⟨451845715621383354269611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 602460954161844472359481 451845715621383354269611)
    ·
      refine ⟨677768573432075031404417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451845715621383354269611 677768573432075031404417)
      ·
        refine ⟨508326430074056273553313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 677768573432075031404417 508326430074056273553313)
        ·
          refine ⟨381244822555542205164985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508326430074056273553313 381244822555542205164985)
          ·
            refine ⟨285933616916656653873739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381244822555542205164985 285933616916656653873739)
            ·
              refine ⟨428900425374984980810609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285933616916656653873739 428900425374984980810609)
              ·
                refine ⟨321675319031238735607957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428900425374984980810609 321675319031238735607957)
                ·
                  refine ⟨15078530579589315731623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 321675319031238735607957 15078530579589315731623)
                  ·
                    rfl

theorem cell20_33036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_33036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33036 prefixEnd_33036 := by exact prefixLift 33036
  have htrace : WordTrace (prefixWord ++ tailWord_33036) baseStart_33036 baseEnd_33036 := by
    simpa [prefixWord, tailWord_33036, baseEnd_33036] using wordTrace_append hprefix tailTrace_33036
  have hstable : (prefixWord ++ tailWord_33036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33036).length < 2 ^ (prefixWord ++ tailWord_33036).sum := by decide
  have hdescent : baseEnd_33036 < baseStart_33036 := by decide
  rcases family_descends (prefixWord ++ tailWord_33036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33105 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 5]
def baseStart_33105 : Nat := 118140960795 + 33105 * 2 ^ 59
def prefixEnd_33105 : Nat := 4983230072969 + 3 ^ 40 * 33105 * 2
def baseEnd_33105 : Nat := 15110024059731742431341

theorem tailTrace_33105 : CollatzResearch.WordTrace tailWord_33105 prefixEnd_33105 15110024059731742431341 := by
  unfold tailWord_33105
  simp only [CollatzResearch.WordTrace]
  refine ⟨1207438545073713728980769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 804959030049142485987179 1207438545073713728980769)
  ·
    refine ⟨905578908805285296735577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1207438545073713728980769 905578908805285296735577)
    ·
      refine ⟨679184181603963972551683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 905578908805285296735577 679184181603963972551683)
      ·
        refine ⟨1018776272405945958827525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679184181603963972551683 1018776272405945958827525)
        ·
          refine ⟨191020551076114867280161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1018776272405945958827525 191020551076114867280161)
          ·
            refine ⟨143265413307086150460121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191020551076114867280161 143265413307086150460121)
            ·
              refine ⟨107449059980314612845091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143265413307086150460121 107449059980314612845091)
              ·
                refine ⟨161173589970471919267637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107449059980314612845091 161173589970471919267637)
                ·
                  refine ⟨15110024059731742431341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161173589970471919267637 15110024059731742431341)
                  ·
                    rfl

theorem cell20_33105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_33105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33105 prefixEnd_33105 := by exact prefixLift 33105
  have htrace : WordTrace (prefixWord ++ tailWord_33105) baseStart_33105 baseEnd_33105 := by
    simpa [prefixWord, tailWord_33105, baseEnd_33105] using wordTrace_append hprefix tailTrace_33105
  have hstable : (prefixWord ++ tailWord_33105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33105).length < 2 ^ (prefixWord ++ tailWord_33105).sum := by decide
  have hdescent : baseEnd_33105 < baseStart_33105 := by decide
  rcases family_descends (prefixWord ++ tailWord_33105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33108 : List Nat := [2, 4, 1, 1, 2, 4, 1, 1, 4]
def baseStart_33108 : Nat := 118140960795 + 33108 * 2 ^ 59
def prefixEnd_33108 : Nat := 4983230072969 + 3 ^ 40 * 33108 * 2
def baseEnd_33108 : Nat := 15111393341477065331329

theorem tailTrace_33108 : CollatzResearch.WordTrace tailWord_33108 prefixEnd_33108 15111393341477065331329 := by
  unfold tailWord_33108
  simp only [CollatzResearch.WordTrace]
  refine ⟨603773982031422620669989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 805031976041896827559985 603773982031422620669989)
  ·
    refine ⟨113207621630891741375623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 603773982031422620669989 113207621630891741375623)
    ·
      refine ⟨169811432446337612063435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113207621630891741375623 169811432446337612063435)
      ·
        refine ⟨254717148669506418095153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169811432446337612063435 254717148669506418095153)
        ·
          refine ⟨191037861502129813571365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254717148669506418095153 191037861502129813571365)
          ·
            refine ⟨35819599031649340044631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191037861502129813571365 35819599031649340044631)
            ·
              refine ⟨53729398547474010066947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35819599031649340044631 53729398547474010066947)
              ·
                refine ⟨80594097821211015100421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53729398547474010066947 80594097821211015100421)
                ·
                  refine ⟨15111393341477065331329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80594097821211015100421 15111393341477065331329)
                  ·
                    rfl

theorem cell20_33108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_33108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33108 prefixEnd_33108 := by exact prefixLift 33108
  have htrace : WordTrace (prefixWord ++ tailWord_33108) baseStart_33108 baseEnd_33108 := by
    simpa [prefixWord, tailWord_33108, baseEnd_33108] using wordTrace_append hprefix tailTrace_33108
  have hstable : (prefixWord ++ tailWord_33108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33108).length < 2 ^ (prefixWord ++ tailWord_33108).sum := by decide
  have hdescent : baseEnd_33108 < baseStart_33108 := by decide
  rcases family_descends (prefixWord ++ tailWord_33108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33112 : List Nat := [2, 1, 2, 2, 1, 1, 2, 5, 4]
def baseStart_33112 : Nat := 118140960795 + 33112 * 2 ^ 59
def prefixEnd_33112 : Nat := 4983230072969 + 3 ^ 40 * 33112 * 2
def baseEnd_33112 : Nat := 15113219050470829197979

theorem tailTrace_33112 : CollatzResearch.WordTrace tailWord_33112 prefixEnd_33112 15113219050470829197979 := by
  unfold tailWord_33112
  simp only [CollatzResearch.WordTrace]
  refine ⟨603846928024176962242795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 805129237365569282990393 603846928024176962242795)
  ·
    refine ⟨905770392036265443364193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 603846928024176962242795 905770392036265443364193)
    ·
      refine ⟨679327794027199082523145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 905770392036265443364193 679327794027199082523145)
      ·
        refine ⟨509495845520399311892359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 679327794027199082523145 509495845520399311892359)
        ·
          refine ⟨764243768280598967838539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509495845520399311892359 764243768280598967838539)
          ·
            refine ⟨1146365652420898451757809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764243768280598967838539 1146365652420898451757809)
            ·
              refine ⟨859774239315673838818357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1146365652420898451757809 859774239315673838818357)
              ·
                refine ⟨80603834935844422389221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 859774239315673838818357 80603834935844422389221)
                ·
                  refine ⟨15113219050470829197979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80603834935844422389221 15113219050470829197979)
                  ·
                    rfl

theorem cell20_33112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_33112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33112 prefixEnd_33112 := by exact prefixLift 33112
  have htrace : WordTrace (prefixWord ++ tailWord_33112) baseStart_33112 baseEnd_33112 := by
    simpa [prefixWord, tailWord_33112, baseEnd_33112] using wordTrace_append hprefix tailTrace_33112
  have hstable : (prefixWord ++ tailWord_33112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33112).length < 2 ^ (prefixWord ++ tailWord_33112).sum := by decide
  have hdescent : baseEnd_33112 < baseStart_33112 := by decide
  rcases family_descends (prefixWord ++ tailWord_33112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33119 : List Nat := [1, 1, 2, 3, 1, 2, 3, 7]
def baseStart_33119 : Nat := 118140960795 + 33119 * 2 ^ 59
def prefixEnd_33119 : Nat := 4983230072969 + 3 ^ 40 * 33119 * 2
def baseEnd_33119 : Nat := 5038804680403305321539

theorem tailTrace_33119 : CollatzResearch.WordTrace tailWord_33119 prefixEnd_33119 5038804680403305321539 := by
  unfold tailWord_33119
  simp only [CollatzResearch.WordTrace]
  refine ⟨1207949167022994119990411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 805299444681996079993607 1207949167022994119990411)
  ·
    refine ⟨1811923750534491179985617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1207949167022994119990411 1811923750534491179985617)
    ·
      refine ⟨1358942812900868384989213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1811923750534491179985617 1358942812900868384989213)
      ·
        refine ⟨509603554837825644370955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1358942812900868384989213 509603554837825644370955)
        ·
          refine ⟨764405332256738466556433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509603554837825644370955 764405332256738466556433)
          ·
            refine ⟨573303999192553849917325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 764405332256738466556433 573303999192553849917325)
            ·
              refine ⟨214988999697207693718997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 573303999192553849917325 214988999697207693718997)
              ·
                refine ⟨5038804680403305321539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 214988999697207693718997 5038804680403305321539)
                ·
                  rfl

theorem cell20_33119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 7].length) (baseStart_33119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33119 prefixEnd_33119 := by exact prefixLift 33119
  have htrace : WordTrace (prefixWord ++ tailWord_33119) baseStart_33119 baseEnd_33119 := by
    simpa [prefixWord, tailWord_33119, baseEnd_33119] using wordTrace_append hprefix tailTrace_33119
  have hstable : (prefixWord ++ tailWord_33119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33119).length < 2 ^ (prefixWord ++ tailWord_33119).sum := by decide
  have hdescent : baseEnd_33119 < baseStart_33119 := by decide
  rcases family_descends (prefixWord ++ tailWord_33119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33160 : List Nat := [2, 1, 3, 3, 1, 1, 4, 2, 3]
def baseStart_33160 : Nat := 118140960795 + 33160 * 2 ^ 59
def prefixEnd_33160 : Nat := 4983230072969 + 3 ^ 40 * 33160 * 2
def baseEnd_33160 : Nat := 15135127558395995597783

theorem tailTrace_33160 : CollatzResearch.WordTrace tailWord_33160 prefixEnd_33160 15135127558395995597783 := by
  unfold tailWord_33160
  simp only [CollatzResearch.WordTrace]
  refine ⟨604722279937229061116467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 806296373249638748155289 604722279937229061116467)
  ·
    refine ⟨907083419905843591674701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 604722279937229061116467 907083419905843591674701)
    ·
      refine ⟨340156282464691346878013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 907083419905843591674701 340156282464691346878013)
      ·
        refine ⟨127558605924259255079255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340156282464691346878013 127558605924259255079255)
        ·
          refine ⟨191337908886388882618883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127558605924259255079255 191337908886388882618883)
          ·
            refine ⟨287006863329583323928325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191337908886388882618883 287006863329583323928325)
            ·
              refine ⟨53813786874296873236561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 287006863329583323928325 53813786874296873236561)
              ·
                refine ⟨40360340155722654927421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53813786874296873236561 40360340155722654927421)
                ·
                  refine ⟨15135127558395995597783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40360340155722654927421 15135127558395995597783)
                  ·
                    rfl

theorem cell20_33160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 3].length) (baseStart_33160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33160 prefixEnd_33160 := by exact prefixLift 33160
  have htrace : WordTrace (prefixWord ++ tailWord_33160) baseStart_33160 baseEnd_33160 := by
    simpa [prefixWord, tailWord_33160, baseEnd_33160] using wordTrace_append hprefix tailTrace_33160
  have hstable : (prefixWord ++ tailWord_33160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33160).length < 2 ^ (prefixWord ++ tailWord_33160).sum := by decide
  have hdescent : baseEnd_33160 < baseStart_33160 := by decide
  rcases family_descends (prefixWord ++ tailWord_33160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33163 : List Nat := [1, 1, 1, 1, 4, 6, 2, 2, 2]
def baseStart_33163 : Nat := 118140960795 + 33163 * 2 ^ 59
def prefixEnd_33163 : Nat := 4983230072969 + 3 ^ 40 * 33163 * 2
def baseEnd_33163 : Nat := 15136496840141318497771

theorem tailTrace_33163 : CollatzResearch.WordTrace tailWord_33163 prefixEnd_33163 15136496840141318497771 := by
  unfold tailWord_33163
  simp only [CollatzResearch.WordTrace]
  refine ⟨1209553978863589634592143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 806369319242393089728095 1209553978863589634592143)
  ·
    refine ⟨1814330968295384451888215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1209553978863589634592143 1814330968295384451888215)
    ·
      refine ⟨2721496452443076677832323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1814330968295384451888215 2721496452443076677832323)
      ·
        refine ⟨4082244678664615016748485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2721496452443076677832323 4082244678664615016748485)
        ·
          refine ⟨765420877249615315640341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4082244678664615016748485 765420877249615315640341)
          ·
            refine ⟨35879103621075717920641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 765420877249615315640341 35879103621075717920641)
            ·
              refine ⟨26909327715806788440481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35879103621075717920641 26909327715806788440481)
              ·
                refine ⟨20181995786855091330361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26909327715806788440481 20181995786855091330361)
                ·
                  refine ⟨15136496840141318497771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20181995786855091330361 15136496840141318497771)
                  ·
                    rfl

theorem cell20_33163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 2].length) (baseStart_33163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33163 prefixEnd_33163 := by exact prefixLift 33163
  have htrace : WordTrace (prefixWord ++ tailWord_33163) baseStart_33163 baseEnd_33163 := by
    simpa [prefixWord, tailWord_33163, baseEnd_33163] using wordTrace_append hprefix tailTrace_33163
  have hstable : (prefixWord ++ tailWord_33163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33163).length < 2 ^ (prefixWord ++ tailWord_33163).sum := by decide
  have hdescent : baseEnd_33163 < baseStart_33163 := by decide
  rcases family_descends (prefixWord ++ tailWord_33163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33188 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 6]
def baseStart_33188 : Nat := 118140960795 + 33188 * 2 ^ 59
def prefixEnd_33188 : Nat := 4983230072969 + 3 ^ 40 * 33188 * 2
def baseEnd_33188 : Nat := 15147907521352342664335

theorem tailTrace_33188 : CollatzResearch.WordTrace tailWord_33188 prefixEnd_33188 15147907521352342664335 := by
  unfold tailWord_33188
  simp only [CollatzResearch.WordTrace]
  refine ⟨605232901886509452126109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 806977202515345936168145 605232901886509452126109)
  ·
    refine ⟨226962338207441044547291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 605232901886509452126109 226962338207441044547291)
    ·
      refine ⟨340443507311161566820937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226962338207441044547291 340443507311161566820937)
      ·
        refine ⟨255332630483371175115703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340443507311161566820937 255332630483371175115703)
        ·
          refine ⟨382998945725056762673555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255332630483371175115703 382998945725056762673555)
          ·
            refine ⟨574498418587585144010333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382998945725056762673555 574498418587585144010333)
            ·
              refine ⟨215436906970344429003875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 574498418587585144010333 215436906970344429003875)
              ·
                refine ⟨323155360455516643505813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215436906970344429003875 323155360455516643505813)
                ·
                  refine ⟨15147907521352342664335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 323155360455516643505813 15147907521352342664335)
                  ·
                    rfl

theorem cell20_33188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_33188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33188 prefixEnd_33188 := by exact prefixLift 33188
  have htrace : WordTrace (prefixWord ++ tailWord_33188) baseStart_33188 baseEnd_33188 := by
    simpa [prefixWord, tailWord_33188, baseEnd_33188] using wordTrace_append hprefix tailTrace_33188
  have hstable : (prefixWord ++ tailWord_33188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33188).length < 2 ^ (prefixWord ++ tailWord_33188).sum := by decide
  have hdescent : baseEnd_33188 < baseStart_33188 := by decide
  rcases family_descends (prefixWord ++ tailWord_33188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33191 : List Nat := [1, 1, 6, 1, 1, 3, 3, 4]
def baseStart_33191 : Nat := 118140960795 + 33191 * 2 ^ 59
def prefixEnd_33191 : Nat := 4983230072969 + 3 ^ 40 * 33191 * 2
def baseEnd_33191 : Nat := 5049758934365888521441

theorem tailTrace_33191 : CollatzResearch.WordTrace tailWord_33191 prefixEnd_33191 5049758934365888521441 := by
  unfold tailWord_33191
  simp only [CollatzResearch.WordTrace]
  refine ⟨1210575222762150416611427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 807050148508100277740951 1210575222762150416611427)
  ·
    refine ⟨1815862834143225624917141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1210575222762150416611427 1815862834143225624917141)
    ·
      refine ⟨85118570350463701167991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1815862834143225624917141 85118570350463701167991)
      ·
        refine ⟨127677855525695551751987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85118570350463701167991 127677855525695551751987)
        ·
          refine ⟨191516783288543327627981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127677855525695551751987 191516783288543327627981)
          ·
            refine ⟨71818793733203747860493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191516783288543327627981 71818793733203747860493)
            ·
              refine ⟨26932047649951405447685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71818793733203747860493 26932047649951405447685)
              ·
                refine ⟨5049758934365888521441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26932047649951405447685 5049758934365888521441)
                ·
                  rfl

theorem cell20_33191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 4].length) (baseStart_33191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33191 prefixEnd_33191 := by exact prefixLift 33191
  have htrace : WordTrace (prefixWord ++ tailWord_33191) baseStart_33191 baseEnd_33191 := by
    simpa [prefixWord, tailWord_33191, baseEnd_33191] using wordTrace_append hprefix tailTrace_33191
  have hstable : (prefixWord ++ tailWord_33191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33191).length < 2 ^ (prefixWord ++ tailWord_33191).sum := by decide
  have hdescent : baseEnd_33191 < baseStart_33191 := by decide
  rcases family_descends (prefixWord ++ tailWord_33191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33212 : List Nat := [2, 2, 2, 4, 1, 2, 7]
def baseStart_33212 : Nat := 118140960795 + 33212 * 2 ^ 59
def prefixEnd_33212 : Nat := 4983230072969 + 3 ^ 40 * 33212 * 2
def baseEnd_33212 : Nat := 1684317975034991762693

theorem tailTrace_33212 : CollatzResearch.WordTrace tailWord_33212 prefixEnd_33212 1684317975034991762693 := by
  unfold tailWord_33212
  simp only [CollatzResearch.WordTrace]
  refine ⟨605670577843035501562945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 807560770457380668750593 605670577843035501562945)
  ·
    refine ⟨454252933382276626172209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 605670577843035501562945 454252933382276626172209)
    ·
      refine ⟨340689700036707469629157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454252933382276626172209 340689700036707469629157)
      ·
        refine ⟨63879318756882650555467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340689700036707469629157 63879318756882650555467)
        ·
          refine ⟨95818978135323975833201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63879318756882650555467 95818978135323975833201)
          ·
            refine ⟨71864233601492981874901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95818978135323975833201 71864233601492981874901)
            ·
              refine ⟨1684317975034991762693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 71864233601492981874901 1684317975034991762693)
              ·
                rfl

theorem cell20_33212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 7].length) (baseStart_33212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33212 prefixEnd_33212 := by exact prefixLift 33212
  have htrace : WordTrace (prefixWord ++ tailWord_33212) baseStart_33212 baseEnd_33212 := by
    simpa [prefixWord, tailWord_33212, baseEnd_33212] using wordTrace_append hprefix tailTrace_33212
  have hstable : (prefixWord ++ tailWord_33212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33212).length < 2 ^ (prefixWord ++ tailWord_33212).sum := by decide
  have hdescent : baseEnd_33212 < baseStart_33212 := by decide
  rcases family_descends (prefixWord ++ tailWord_33212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33281 : List Nat := [1, 2, 4, 1, 3, 1, 3, 1, 4]
def baseStart_33281 : Nat := 118140960795 + 33281 * 2 ^ 59
def prefixEnd_33281 : Nat := 4983230072969 + 3 ^ 40 * 33281 * 2
def baseEnd_33281 : Nat := 15190355255457352563955

theorem tailTrace_33281 : CollatzResearch.WordTrace tailWord_33281 prefixEnd_33281 15190355255457352563955 := by
  unfold tailWord_33281
  simp only [CollatzResearch.WordTrace]
  refine ⟨1213857792436095787387697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 809238528290730524925131 1213857792436095787387697)
  ·
    refine ⟨910393344327071840540773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1213857792436095787387697 910393344327071840540773)
    ·
      refine ⟨170698752061325970101395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 910393344327071840540773 170698752061325970101395)
      ·
        refine ⟨256048128091988955152093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170698752061325970101395 256048128091988955152093)
        ·
          refine ⟨96018048034495858182035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256048128091988955152093 96018048034495858182035)
          ·
            refine ⟨144027072051743787273053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96018048034495858182035 144027072051743787273053)
            ·
              refine ⟨54010152019403920227395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144027072051743787273053 54010152019403920227395)
              ·
                refine ⟨81015228029105880341093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54010152019403920227395 81015228029105880341093)
                ·
                  refine ⟨15190355255457352563955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81015228029105880341093 15190355255457352563955)
                  ·
                    rfl

theorem cell20_33281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_33281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33281 prefixEnd_33281 := by exact prefixLift 33281
  have htrace : WordTrace (prefixWord ++ tailWord_33281) baseStart_33281 baseEnd_33281 := by
    simpa [prefixWord, tailWord_33281, baseEnd_33281] using wordTrace_append hprefix tailTrace_33281
  have hstable : (prefixWord ++ tailWord_33281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33281).length < 2 ^ (prefixWord ++ tailWord_33281).sum := by decide
  have hdescent : baseEnd_33281 < baseStart_33281 := by decide
  rcases family_descends (prefixWord ++ tailWord_33281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33291 : List Nat := [1, 1, 1, 1, 7, 3, 2, 1, 3]
def baseStart_33291 : Nat := 118140960795 + 33291 * 2 ^ 59
def prefixEnd_33291 : Nat := 4983230072969 + 3 ^ 40 * 33291 * 2
def baseEnd_33291 : Nat := 15194919527941762230581

theorem tailTrace_33291 : CollatzResearch.WordTrace tailWord_33291 prefixEnd_33291 15194919527941762230581 := by
  unfold tailWord_33291
  simp only [CollatzResearch.WordTrace]
  refine ⟨1214222522399867495251727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 809481681599911663501151 1214222522399867495251727)
  ·
    refine ⟨1821333783599801242877591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1214222522399867495251727 1821333783599801242877591)
    ·
      refine ⟨2732000675399701864316387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1821333783599801242877591 2732000675399701864316387)
      ·
        refine ⟨4098001013099552796474581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2732000675399701864316387 4098001013099552796474581)
        ·
          refine ⟨96046898744520768667373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 4098001013099552796474581 96046898744520768667373)
          ·
            refine ⟨36017587029195288250265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96046898744520768667373 36017587029195288250265)
            ·
              refine ⟨27013190271896466187699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36017587029195288250265 27013190271896466187699)
              ·
                refine ⟨40519785407844699281549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27013190271896466187699 40519785407844699281549)
                ·
                  refine ⟨15194919527941762230581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40519785407844699281549 15194919527941762230581)
                  ·
                    rfl

theorem cell20_33291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 3].length) (baseStart_33291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33291 prefixEnd_33291 := by exact prefixLift 33291
  have htrace : WordTrace (prefixWord ++ tailWord_33291) baseStart_33291 baseEnd_33291 := by
    simpa [prefixWord, tailWord_33291, baseEnd_33291] using wordTrace_append hprefix tailTrace_33291
  have hstable : (prefixWord ++ tailWord_33291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33291).length < 2 ^ (prefixWord ++ tailWord_33291).sum := by decide
  have hdescent : baseEnd_33291 < baseStart_33291 := by decide
  rcases family_descends (prefixWord ++ tailWord_33291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33325 : List Nat := [1, 5, 4, 1, 1, 1, 2, 2, 3]
def baseStart_33325 : Nat := 118140960795 + 33325 * 2 ^ 59
def prefixEnd_33325 : Nat := 4983230072969 + 3 ^ 40 * 33325 * 2
def baseEnd_33325 : Nat := 15210438054388755097109

theorem tailTrace_33325 : CollatzResearch.WordTrace tailWord_33325 prefixEnd_33325 15210438054388755097109 := by
  unfold tailWord_33325
  simp only [CollatzResearch.WordTrace]
  refine ⟨1215462604276691301989429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 810308402851127534659619 1215462604276691301989429)
  ·
    refine ⟨113949619150939809561509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1215462604276691301989429 113949619150939809561509)
    ·
      refine ⟨21365553590801214292783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113949619150939809561509 21365553590801214292783)
      ·
        refine ⟨32048330386201821439175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21365553590801214292783 32048330386201821439175)
        ·
          refine ⟨48072495579302732158763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32048330386201821439175 48072495579302732158763)
          ·
            refine ⟨72108743368954098238145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48072495579302732158763 72108743368954098238145)
            ·
              refine ⟨54081557526715573678609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72108743368954098238145 54081557526715573678609)
              ·
                refine ⟨40561168145036680258957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54081557526715573678609 40561168145036680258957)
                ·
                  refine ⟨15210438054388755097109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40561168145036680258957 15210438054388755097109)
                  ·
                    rfl

theorem cell20_33325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_33325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33325 prefixEnd_33325 := by exact prefixLift 33325
  have htrace : WordTrace (prefixWord ++ tailWord_33325) baseStart_33325 baseEnd_33325 := by
    simpa [prefixWord, tailWord_33325, baseEnd_33325] using wordTrace_append hprefix tailTrace_33325
  have hstable : (prefixWord ++ tailWord_33325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33325).length < 2 ^ (prefixWord ++ tailWord_33325).sum := by decide
  have hdescent : baseEnd_33325 < baseStart_33325 := by decide
  rcases family_descends (prefixWord ++ tailWord_33325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33326 : List Nat := [4, 1, 3, 1, 3, 8]
def baseStart_33326 : Nat := 118140960795 + 33326 * 2 ^ 59
def prefixEnd_33326 : Nat := 4983230072969 + 3 ^ 40 * 33326 * 2
def baseEnd_33326 : Nat := 563366462282859113473

theorem tailTrace_33326 : CollatzResearch.WordTrace tailWord_33326 prefixEnd_33326 563366462282859113473 := by
  unfold tailWord_33326
  simp only [CollatzResearch.WordTrace]
  refine ⟨151937384659133559096979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 810332718182045648517221 151937384659133559096979)
  ·
    refine ⟨227906076988700338645469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151937384659133559096979 227906076988700338645469)
    ·
      refine ⟨85464778870762626992051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227906076988700338645469 85464778870762626992051)
      ·
        refine ⟨128197168306143940488077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85464778870762626992051 128197168306143940488077)
        ·
          refine ⟨48073938114803977683029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128197168306143940488077 48073938114803977683029)
          ·
            refine ⟨563366462282859113473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 48073938114803977683029 563366462282859113473)
            ·
              rfl

theorem cell20_33326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 8].length) (baseStart_33326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33326 prefixEnd_33326 := by exact prefixLift 33326
  have htrace : WordTrace (prefixWord ++ tailWord_33326) baseStart_33326 baseEnd_33326 := by
    simpa [prefixWord, tailWord_33326, baseEnd_33326] using wordTrace_append hprefix tailTrace_33326
  have hstable : (prefixWord ++ tailWord_33326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33326).length < 2 ^ (prefixWord ++ tailWord_33326).sum := by decide
  have hdescent : baseEnd_33326 < baseStart_33326 := by decide
  rcases family_descends (prefixWord ++ tailWord_33326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33332 : List Nat := [2, 5, 1, 3, 1, 1, 1, 4, 2]
def baseStart_33332 : Nat := 118140960795 + 33332 * 2 ^ 59
def prefixEnd_33332 : Nat := 4983230072969 + 3 ^ 40 * 33332 * 2
def baseEnd_33332 : Nat := 15213633045127841863747

theorem tailTrace_33332 : CollatzResearch.WordTrace tailWord_33332 prefixEnd_33332 15213633045127841863747 := by
  unfold tailWord_33332
  simp only [CollatzResearch.WordTrace]
  refine ⟨607858957625665748747125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 810478610167554331662833 607858957625665748747125)
  ·
    refine ⟨56986777277406163945043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 607858957625665748747125 56986777277406163945043)
    ·
      refine ⟨85480165916109245917565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56986777277406163945043 85480165916109245917565)
      ·
        refine ⟨32055062218540967219087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85480165916109245917565 32055062218540967219087)
        ·
          refine ⟨48082593327811450828631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32055062218540967219087 48082593327811450828631)
          ·
            refine ⟨72123889991717176242947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48082593327811450828631 72123889991717176242947)
            ·
              refine ⟨108185834987575764364421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72123889991717176242947 108185834987575764364421)
              ·
                refine ⟨20284844060170455818329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108185834987575764364421 20284844060170455818329)
                ·
                  refine ⟨15213633045127841863747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20284844060170455818329 15213633045127841863747)
                  ·
                    rfl

theorem cell20_33332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_33332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33332 prefixEnd_33332 := by exact prefixLift 33332
  have htrace : WordTrace (prefixWord ++ tailWord_33332) baseStart_33332 baseEnd_33332 := by
    simpa [prefixWord, tailWord_33332, baseEnd_33332] using wordTrace_append hprefix tailTrace_33332
  have hstable : (prefixWord ++ tailWord_33332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33332).length < 2 ^ (prefixWord ++ tailWord_33332).sum := by decide
  have hdescent : baseEnd_33332 < baseStart_33332 := by decide
  rcases family_descends (prefixWord ++ tailWord_33332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33357 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 6]
def baseStart_33357 : Nat := 118140960795 + 33357 * 2 ^ 59
def prefixEnd_33357 : Nat := 4983230072969 + 3 ^ 40 * 33357 * 2
def baseEnd_33357 : Nat := 15225043726338866030311

theorem tailTrace_33357 : CollatzResearch.WordTrace tailWord_33357 prefixEnd_33357 15225043726338866030311 := by
  unfold tailWord_33357
  simp only [CollatzResearch.WordTrace]
  refine ⟨1216629740160760767154325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 811086493440507178102883 1216629740160760767154325)
  ·
    refine ⟨57029519070035660960359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1216629740160760767154325 57029519070035660960359)
    ·
      refine ⟨85544278605053491440539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57029519070035660960359 85544278605053491440539)
      ·
        refine ⟨128316417907580237160809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85544278605053491440539 128316417907580237160809)
        ·
          refine ⟨96237313430685177870607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128316417907580237160809 96237313430685177870607)
          ·
            refine ⟨144355970146027766805911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96237313430685177870607 144355970146027766805911)
            ·
              refine ⟨216533955219041650208867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144355970146027766805911 216533955219041650208867)
              ·
                refine ⟨324800932828562475313301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216533955219041650208867 324800932828562475313301)
                ·
                  refine ⟨15225043726338866030311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 324800932828562475313301 15225043726338866030311)
                  ·
                    rfl

theorem cell20_33357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_33357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33357 prefixEnd_33357 := by exact prefixLift 33357
  have htrace : WordTrace (prefixWord ++ tailWord_33357) baseStart_33357 baseEnd_33357 := by
    simpa [prefixWord, tailWord_33357, baseEnd_33357] using wordTrace_append hprefix tailTrace_33357
  have hstable : (prefixWord ++ tailWord_33357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33357).length < 2 ^ (prefixWord ++ tailWord_33357).sum := by decide
  have hdescent : baseEnd_33357 < baseStart_33357 := by decide
  rcases family_descends (prefixWord ++ tailWord_33357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33384 : List Nat := [2, 1, 4, 3, 3, 1, 1, 2, 3]
def baseStart_33384 : Nat := 118140960795 + 33384 * 2 ^ 59
def prefixEnd_33384 : Nat := 4983230072969 + 3 ^ 40 * 33384 * 2
def baseEnd_33384 : Nat := 15237367262046772130201

theorem tailTrace_33384 : CollatzResearch.WordTrace tailWord_33384 prefixEnd_33384 15237367262046772130201 := by
  unfold tailWord_33384
  simp only [CollatzResearch.WordTrace]
  refine ⟨608807255531472189193603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 811743007375296252258137 608807255531472189193603)
  ·
    refine ⟨913210883297208283790405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 608807255531472189193603 913210883297208283790405)
    ·
      refine ⟨171227040618226553210701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 913210883297208283790405 171227040618226553210701)
      ·
        refine ⟨64210140231834957454013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171227040618226553210701 64210140231834957454013)
        ·
          refine ⟨24078802586938109045255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64210140231834957454013 24078802586938109045255)
          ·
            refine ⟨36118203880407163567883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24078802586938109045255 36118203880407163567883)
            ·
              refine ⟨54177305820610745351825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36118203880407163567883 54177305820610745351825)
              ·
                refine ⟨40632979365458059013869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54177305820610745351825 40632979365458059013869)
                ·
                  refine ⟨15237367262046772130201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40632979365458059013869 15237367262046772130201)
                  ·
                    rfl

theorem cell20_33384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 3].length) (baseStart_33384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33384 prefixEnd_33384 := by exact prefixLift 33384
  have htrace : WordTrace (prefixWord ++ tailWord_33384) baseStart_33384 baseEnd_33384 := by
    simpa [prefixWord, tailWord_33384, baseEnd_33384] using wordTrace_append hprefix tailTrace_33384
  have hstable : (prefixWord ++ tailWord_33384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33384).length < 2 ^ (prefixWord ++ tailWord_33384).sum := by decide
  have hdescent : baseEnd_33384 < baseStart_33384 := by decide
  rcases family_descends (prefixWord ++ tailWord_33384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33405 : List Nat := [1, 4, 1, 1, 5, 1, 3, 1, 3]
def baseStart_33405 : Nat := 118140960795 + 33405 * 2 ^ 59
def prefixEnd_33405 : Nat := 4983230072969 + 3 ^ 40 * 33405 * 2
def baseEnd_33405 : Nat := 15246952234264032430115

theorem tailTrace_33405 : CollatzResearch.WordTrace tailWord_33405 prefixEnd_33405 15246952234264032430115 := by
  unfold tailWord_33405
  simp only [CollatzResearch.WordTrace]
  refine ⟨1218380443986864964901669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 812253629324576643267779 1218380443986864964901669)
  ·
    refine ⟨228446333247537180919063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1218380443986864964901669 228446333247537180919063)
    ·
      refine ⟨342669499871305771378595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228446333247537180919063 342669499871305771378595)
      ·
        refine ⟨514004249806958657067893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342669499871305771378595 514004249806958657067893)
        ·
          refine ⟨48187898419402374100115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 514004249806958657067893 48187898419402374100115)
          ·
            refine ⟨72281847629103561150173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48187898419402374100115 72281847629103561150173)
            ·
              refine ⟨27105692860913835431315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72281847629103561150173 27105692860913835431315)
              ·
                refine ⟨40658539291370753146973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27105692860913835431315 40658539291370753146973)
                ·
                  refine ⟨15246952234264032430115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40658539291370753146973 15246952234264032430115)
                  ·
                    rfl

theorem cell20_33405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_33405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33405 prefixEnd_33405 := by exact prefixLift 33405
  have htrace : WordTrace (prefixWord ++ tailWord_33405) baseStart_33405 baseEnd_33405 := by
    simpa [prefixWord, tailWord_33405, baseEnd_33405] using wordTrace_append hprefix tailTrace_33405
  have hstable : (prefixWord ++ tailWord_33405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33405).length < 2 ^ (prefixWord ++ tailWord_33405).sum := by decide
  have hdescent : baseEnd_33405 < baseStart_33405 := by decide
  rcases family_descends (prefixWord ++ tailWord_33405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33440 : List Nat := [2, 1, 1, 4, 4, 2, 6]
def baseStart_33440 : Nat := 118140960795 + 33440 * 2 ^ 59
def prefixEnd_33440 : Nat := 4983230072969 + 3 ^ 40 * 33440 * 2
def baseEnd_33440 : Nat := 1695880798662162918145

theorem tailTrace_33440 : CollatzResearch.WordTrace tailWord_33440 prefixEnd_33440 1695880798662162918145 := by
  unfold tailWord_33440
  simp only [CollatzResearch.WordTrace]
  refine ⟨609828499430032971212887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 813104665906710628283849 609828499430032971212887)
  ·
    refine ⟨914742749145049456819331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 609828499430032971212887 914742749145049456819331)
    ·
      refine ⟨1372114123717574185228997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 914742749145049456819331 1372114123717574185228997)
      ·
        refine ⟨257271398197045159730437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1372114123717574185228997 257271398197045159730437)
        ·
          refine ⟨48238387161945967449457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257271398197045159730437 48238387161945967449457)
          ·
            refine ⟨36178790371459475587093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48238387161945967449457 36178790371459475587093)
            ·
              refine ⟨1695880798662162918145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36178790371459475587093 1695880798662162918145)
              ·
                rfl

theorem cell20_33440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 6].length) (baseStart_33440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33440 prefixEnd_33440 := by exact prefixLift 33440
  have htrace : WordTrace (prefixWord ++ tailWord_33440) baseStart_33440 baseEnd_33440 := by
    simpa [prefixWord, tailWord_33440, baseEnd_33440] using wordTrace_append hprefix tailTrace_33440
  have hstable : (prefixWord ++ tailWord_33440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33440).length < 2 ^ (prefixWord ++ tailWord_33440).sum := by decide
  have hdescent : baseEnd_33440 < baseStart_33440 := by decide
  rcases family_descends (prefixWord ++ tailWord_33440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33457 : List Nat := [1, 2, 2, 6, 1, 1, 2, 5]
def baseStart_33457 : Nat := 118140960795 + 33457 * 2 ^ 59
def prefixEnd_33457 : Nat := 4983230072969 + 3 ^ 40 * 33457 * 2
def baseEnd_33457 : Nat := 5090228817060987565523

theorem tailTrace_33457 : CollatzResearch.WordTrace tailWord_33457 prefixEnd_33457 5090228817060987565523 := by
  unfold tailWord_33457
  simp only [CollatzResearch.WordTrace]
  refine ⟨1220277039798477845794625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 813518026532318563863083 1220277039798477845794625)
  ·
    refine ⟨915207779848858384345969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1220277039798477845794625 915207779848858384345969)
    ·
      refine ⟨686405834886643788259477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 915207779848858384345969 686405834886643788259477)
      ·
        refine ⟨32175273510311427574663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 686405834886643788259477 32175273510311427574663)
        ·
          refine ⟨48262910265467141361995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32175273510311427574663 48262910265467141361995)
          ·
            refine ⟨72394365398200712042993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48262910265467141361995 72394365398200712042993)
            ·
              refine ⟨54295774048650534032245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72394365398200712042993 54295774048650534032245)
              ·
                refine ⟨5090228817060987565523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54295774048650534032245 5090228817060987565523)
                ·
                  rfl

theorem cell20_33457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 5].length) (baseStart_33457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33457 prefixEnd_33457 := by exact prefixLift 33457
  have htrace : WordTrace (prefixWord ++ tailWord_33457) baseStart_33457 baseEnd_33457 := by
    simpa [prefixWord, tailWord_33457, baseEnd_33457] using wordTrace_append hprefix tailTrace_33457
  have hstable : (prefixWord ++ tailWord_33457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33457).length < 2 ^ (prefixWord ++ tailWord_33457).sum := by decide
  have hdescent : baseEnd_33457 < baseStart_33457 := by decide
  rcases family_descends (prefixWord ++ tailWord_33457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33505 : List Nat := [1, 2, 3, 1, 4, 3, 2, 2, 2]
def baseStart_33505 : Nat := 118140960795 + 33505 * 2 ^ 59
def prefixEnd_33505 : Nat := 4983230072969 + 3 ^ 40 * 33505 * 2
def baseEnd_33505 : Nat := 15292594959108129096373

theorem tailTrace_33505 : CollatzResearch.WordTrace tailWord_33505 prefixEnd_33505 15292594959108129096373 := by
  unfold tailWord_33505
  simp only [CollatzResearch.WordTrace]
  refine ⟨1222027743624582043541969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 814685162416388029027979 1222027743624582043541969)
  ·
    refine ⟨916520807718436532656477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1222027743624582043541969 916520807718436532656477)
    ·
      refine ⟨343695302894413699746179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 916520807718436532656477 343695302894413699746179)
      ·
        refine ⟨515542954341620549619269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343695302894413699746179 515542954341620549619269)
        ·
          refine ⟨96664303939053853053613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 515542954341620549619269 96664303939053853053613)
          ·
            refine ⟨36249113977145194895105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96664303939053853053613 36249113977145194895105)
            ·
              refine ⟨27186835482858896171329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36249113977145194895105 27186835482858896171329)
              ·
                refine ⟨20390126612144172128497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27186835482858896171329 20390126612144172128497)
                ·
                  refine ⟨15292594959108129096373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20390126612144172128497 15292594959108129096373)
                  ·
                    rfl

theorem cell20_33505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 2].length) (baseStart_33505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33505 prefixEnd_33505 := by exact prefixLift 33505
  have htrace : WordTrace (prefixWord ++ tailWord_33505) baseStart_33505 baseEnd_33505 := by
    simpa [prefixWord, tailWord_33505, baseEnd_33505] using wordTrace_append hprefix tailTrace_33505
  have hstable : (prefixWord ++ tailWord_33505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33505).length < 2 ^ (prefixWord ++ tailWord_33505).sum := by decide
  have hdescent : baseEnd_33505 < baseStart_33505 := by decide
  rcases family_descends (prefixWord ++ tailWord_33505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33551 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 6]
def baseStart_33551 : Nat := 118140960795 + 33551 * 2 ^ 59
def prefixEnd_33551 : Nat := 4983230072969 + 3 ^ 40 * 33551 * 2
def baseEnd_33551 : Nat := 15313590612536413562851

theorem tailTrace_33551 : CollatzResearch.WordTrace tailWord_33551 prefixEnd_33551 15313590612536413562851 := by
  unfold tailWord_33551
  simp only [CollatzResearch.WordTrace]
  refine ⟨1223705501457931899716507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 815803667638621266477671 1223705501457931899716507)
  ·
    refine ⟨1835558252186897849574761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1223705501457931899716507 1835558252186897849574761)
    ·
      refine ⟨1376668689140173387181071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1835558252186897849574761 1376668689140173387181071)
      ·
        refine ⟨2065003033710260080771607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1376668689140173387181071 2065003033710260080771607)
        ·
          refine ⟨3097504550565390121157411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2065003033710260080771607 3097504550565390121157411)
          ·
            refine ⟨4646256825848085181736117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3097504550565390121157411 4646256825848085181736117)
            ·
              refine ⟨435586577423257985787761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4646256825848085181736117 435586577423257985787761)
              ·
                refine ⟨326689933067443489340821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 435586577423257985787761 326689933067443489340821)
                ·
                  refine ⟨15313590612536413562851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 326689933067443489340821 15313590612536413562851)
                  ·
                    rfl

theorem cell20_33551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_33551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33551 prefixEnd_33551 := by exact prefixLift 33551
  have htrace : WordTrace (prefixWord ++ tailWord_33551) baseStart_33551 baseEnd_33551 := by
    simpa [prefixWord, tailWord_33551, baseEnd_33551] using wordTrace_append hprefix tailTrace_33551
  have hstable : (prefixWord ++ tailWord_33551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33551).length < 2 ^ (prefixWord ++ tailWord_33551).sum := by decide
  have hdescent : baseEnd_33551 < baseStart_33551 := by decide
  rcases family_descends (prefixWord ++ tailWord_33551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33568 : List Nat := [2, 1, 1, 5, 1, 2, 1, 3, 4]
def baseStart_33568 : Nat := 118140960795 + 33568 * 2 ^ 59
def prefixEnd_33568 : Nat := 4983230072969 + 3 ^ 40 * 33568 * 2
def baseEnd_33568 : Nat := 15321349875759909996115

theorem tailTrace_33568 : CollatzResearch.WordTrace tailWord_33568 prefixEnd_33568 15321349875759909996115 := by
  unfold tailWord_33568
  simp only [CollatzResearch.WordTrace]
  refine ⟨612162771198171901542679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 816217028264229202056905 612162771198171901542679)
  ·
    refine ⟨918244156797257852314019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 612162771198171901542679 918244156797257852314019)
    ·
      refine ⟨1377366235195886778471029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 918244156797257852314019 1377366235195886778471029)
      ·
        refine ⟨129128084549614385481659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1377366235195886778471029 129128084549614385481659)
        ·
          refine ⟨193692126824421578222489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129128084549614385481659 193692126824421578222489)
          ·
            refine ⟨145269095118316183666867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193692126824421578222489 145269095118316183666867)
            ·
              refine ⟨217903642677474275500301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145269095118316183666867 217903642677474275500301)
              ·
                refine ⟨81713866004052853312613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217903642677474275500301 81713866004052853312613)
                ·
                  refine ⟨15321349875759909996115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81713866004052853312613 15321349875759909996115)
                  ·
                    rfl

theorem cell20_33568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_33568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33568 prefixEnd_33568 := by exact prefixLift 33568
  have htrace : WordTrace (prefixWord ++ tailWord_33568) baseStart_33568 baseEnd_33568 := by
    simpa [prefixWord, tailWord_33568, baseEnd_33568] using wordTrace_append hprefix tailTrace_33568
  have hstable : (prefixWord ++ tailWord_33568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33568).length < 2 ^ (prefixWord ++ tailWord_33568).sum := by decide
  have hdescent : baseEnd_33568 < baseStart_33568 := by decide
  rcases family_descends (prefixWord ++ tailWord_33568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33588 : List Nat := [2, 5, 1, 1, 3, 2, 2, 4]
def baseStart_33588 : Nat := 118140960795 + 33588 * 2 ^ 59
def prefixEnd_33588 : Nat := 4983230072969 + 3 ^ 40 * 33588 * 2
def baseEnd_33588 : Nat := 5110159473576243109789

theorem tailTrace_33588 : CollatzResearch.WordTrace tailWord_33588 prefixEnd_33588 5110159473576243109789 := by
  unfold tailWord_33588
  simp only [CollatzResearch.WordTrace]
  refine ⟨612527501161943609406709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 816703334882591479208945 612527501161943609406709)
  ·
    refine ⟨57424453233932213381879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 612527501161943609406709 57424453233932213381879)
    ·
      refine ⟨86136679850898320072819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57424453233932213381879 86136679850898320072819)
      ·
        refine ⟨129205019776347480109229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86136679850898320072819 129205019776347480109229)
        ·
          refine ⟨48451882416130305040961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129205019776347480109229 48451882416130305040961)
          ·
            refine ⟨36338911812097728780721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48451882416130305040961 36338911812097728780721)
            ·
              refine ⟨27254183859073296585541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36338911812097728780721 27254183859073296585541)
              ·
                refine ⟨5110159473576243109789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27254183859073296585541 5110159473576243109789)
                ·
                  rfl

theorem cell20_33588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 4].length) (baseStart_33588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33588 prefixEnd_33588 := by exact prefixLift 33588
  have htrace : WordTrace (prefixWord ++ tailWord_33588) baseStart_33588 baseEnd_33588 := by
    simpa [prefixWord, tailWord_33588, baseEnd_33588] using wordTrace_append hprefix tailTrace_33588
  have hstable : (prefixWord ++ tailWord_33588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33588).length < 2 ^ (prefixWord ++ tailWord_33588).sum := by decide
  have hdescent : baseEnd_33588 < baseStart_33588 := by decide
  rcases family_descends (prefixWord ++ tailWord_33588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33598 : List Nat := [4, 2, 1, 2, 4, 1, 1, 3, 2]
def baseStart_33598 : Nat := 118140960795 + 33598 * 2 ^ 59
def prefixEnd_33598 : Nat := 4983230072969 + 3 ^ 40 * 33598 * 2
def baseEnd_33598 : Nat := 15335042693213138995993

theorem tailTrace_33598 : CollatzResearch.WordTrace tailWord_33598 prefixEnd_33598 15335042693213138995993 := by
  unfold tailWord_33598
  simp only [CollatzResearch.WordTrace]
  refine ⟨153177466535957365834681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 816946488191772617784965 153177466535957365834681)
  ·
    refine ⟨114883099901968024376011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153177466535957365834681 114883099901968024376011)
    ·
      refine ⟨172324649852952036564017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114883099901968024376011 172324649852952036564017)
      ·
        refine ⟨129243487389714027423013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172324649852952036564017 129243487389714027423013)
        ·
          refine ⟨24233153885571380141815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129243487389714027423013 24233153885571380141815)
          ·
            refine ⟨36349730828357070212723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24233153885571380141815 36349730828357070212723)
            ·
              refine ⟨54524596242535605319085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36349730828357070212723 54524596242535605319085)
              ·
                refine ⟨20446723590950851994657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54524596242535605319085 20446723590950851994657)
                ·
                  refine ⟨15335042693213138995993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20446723590950851994657 15335042693213138995993)
                  ·
                    rfl

theorem cell20_33598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_33598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33598 prefixEnd_33598 := by exact prefixLift 33598
  have htrace : WordTrace (prefixWord ++ tailWord_33598) baseStart_33598 baseEnd_33598 := by
    simpa [prefixWord, tailWord_33598, baseEnd_33598] using wordTrace_append hprefix tailTrace_33598
  have hstable : (prefixWord ++ tailWord_33598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33598).length < 2 ^ (prefixWord ++ tailWord_33598).sum := by decide
  have hdescent : baseEnd_33598 < baseStart_33598 := by decide
  rcases family_descends (prefixWord ++ tailWord_33598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33623 : List Nat := [1, 1, 3, 2, 4, 3, 1, 1, 4]
def baseStart_33623 : Nat := 118140960795 + 33623 * 2 ^ 59
def prefixEnd_33623 : Nat := 4983230072969 + 3 ^ 40 * 33623 * 2
def baseEnd_33623 : Nat := 15346453374424163162557

theorem tailTrace_33623 : CollatzResearch.WordTrace tailWord_33623 prefixEnd_33623 15346453374424163162557 := by
  unfold tailWord_33623
  simp only [CollatzResearch.WordTrace]
  refine ⟨1226331557197088196337523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 817554371464725464225015 1226331557197088196337523)
  ·
    refine ⟨1839497335795632294506285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1226331557197088196337523 1839497335795632294506285)
    ·
      refine ⟨689811500923362110439857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1839497335795632294506285 689811500923362110439857)
      ·
        refine ⟨517358625692521582829893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 689811500923362110439857 517358625692521582829893)
        ·
          refine ⟨97004742317347796780605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 517358625692521582829893 97004742317347796780605)
          ·
            refine ⟨36376778369005423792727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97004742317347796780605 36376778369005423792727)
            ·
              refine ⟨54565167553508135689091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36376778369005423792727 54565167553508135689091)
              ·
                refine ⟨81847751330262203533637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54565167553508135689091 81847751330262203533637)
                ·
                  refine ⟨15346453374424163162557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81847751330262203533637 15346453374424163162557)
                  ·
                    rfl

theorem cell20_33623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 4].length) (baseStart_33623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33623 prefixEnd_33623 := by exact prefixLift 33623
  have htrace : WordTrace (prefixWord ++ tailWord_33623) baseStart_33623 baseEnd_33623 := by
    simpa [prefixWord, tailWord_33623, baseEnd_33623] using wordTrace_append hprefix tailTrace_33623
  have hstable : (prefixWord ++ tailWord_33623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33623).length < 2 ^ (prefixWord ++ tailWord_33623).sum := by decide
  have hdescent : baseEnd_33623 < baseStart_33623 := by decide
  rcases family_descends (prefixWord ++ tailWord_33623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33775 : List Nat := [1, 1, 2, 1, 4, 3, 3, 3, 2]
def baseStart_33775 : Nat := 118140960795 + 33775 * 2 ^ 59
def prefixEnd_33775 : Nat := 4983230072969 + 3 ^ 40 * 33775 * 2
def baseEnd_33775 : Nat := 15415830316187190095269

theorem tailTrace_33775 : CollatzResearch.WordTrace tailWord_33775 prefixEnd_33775 15415830316187190095269 := by
  unfold tailWord_33775
  simp only [CollatzResearch.WordTrace]
  refine ⟨1231875452646418155870779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 821250301764278770580519 1231875452646418155870779)
  ·
    refine ⟨1847813178969627233806169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1231875452646418155870779 1847813178969627233806169)
    ·
      refine ⟨1385859884227220425354627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1847813178969627233806169 1385859884227220425354627)
      ·
        refine ⟨2078789826340830638031941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1385859884227220425354627 2078789826340830638031941)
        ·
          refine ⟨389773092438905744630989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2078789826340830638031941 389773092438905744630989)
          ·
            refine ⟨146164909664589654236621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 389773092438905744630989 146164909664589654236621)
            ·
              refine ⟨54811841124221120338733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146164909664589654236621 54811841124221120338733)
              ·
                refine ⟨20554440421582920127025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54811841124221120338733 20554440421582920127025)
                ·
                  refine ⟨15415830316187190095269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20554440421582920127025 15415830316187190095269)
                  ·
                    rfl

theorem cell20_33775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 2].length) (baseStart_33775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33775 prefixEnd_33775 := by exact prefixLift 33775
  have htrace : WordTrace (prefixWord ++ tailWord_33775) baseStart_33775 baseEnd_33775 := by
    simpa [prefixWord, tailWord_33775, baseEnd_33775] using wordTrace_append hprefix tailTrace_33775
  have hstable : (prefixWord ++ tailWord_33775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33775).length < 2 ^ (prefixWord ++ tailWord_33775).sum := by decide
  have hdescent : baseEnd_33775 < baseStart_33775 := by decide
  rcases family_descends (prefixWord ++ tailWord_33775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33782 : List Nat := [5, 1, 1, 1, 3, 3, 6]
def baseStart_33782 : Nat := 118140960795 + 33782 * 2 ^ 59
def prefixEnd_33782 : Nat := 4983230072969 + 3 ^ 40 * 33782 * 2
def baseEnd_33782 : Nat := 1713225034102919651323

theorem tailTrace_33782 : CollatzResearch.WordTrace tailWord_33782 prefixEnd_33782 1713225034102919651323 := by
  unfold tailWord_33782
  simp only [CollatzResearch.WordTrace]
  refine ⟨77008172726316146960975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 821420509080705567583733 77008172726316146960975)
  ·
    refine ⟨115512259089474220441463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77008172726316146960975 115512259089474220441463)
    ·
      refine ⟨173268388634211330662195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115512259089474220441463 173268388634211330662195)
      ·
        refine ⟨259902582951316995993293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173268388634211330662195 259902582951316995993293)
        ·
          refine ⟨97463468606743873497485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 259902582951316995993293 97463468606743873497485)
          ·
            refine ⟨36548800727528952561557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97463468606743873497485 36548800727528952561557)
            ·
              refine ⟨1713225034102919651323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36548800727528952561557 1713225034102919651323)
              ·
                rfl

theorem cell20_33782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 6].length) (baseStart_33782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33782 prefixEnd_33782 := by exact prefixLift 33782
  have htrace : WordTrace (prefixWord ++ tailWord_33782) baseStart_33782 baseEnd_33782 := by
    simpa [prefixWord, tailWord_33782, baseEnd_33782] using wordTrace_append hprefix tailTrace_33782
  have hstable : (prefixWord ++ tailWord_33782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33782).length < 2 ^ (prefixWord ++ tailWord_33782).sum := by decide
  have hdescent : baseEnd_33782 < baseStart_33782 := by decide
  rcases family_descends (prefixWord ++ tailWord_33782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33803 : List Nat := [1, 1, 1, 1, 6, 3, 2, 5]
def baseStart_33803 : Nat := 118140960795 + 33803 * 2 ^ 59
def prefixEnd_33803 : Nat := 4983230072969 + 3 ^ 40 * 33803 * 2
def baseEnd_33803 : Nat := 5142870093047845720607

theorem tailTrace_33803 : CollatzResearch.WordTrace tailWord_33803 prefixEnd_33803 5142870093047845720607 := by
  unfold tailWord_33803
  simp only [CollatzResearch.WordTrace]
  refine ⟨1232896696544978937890063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 821931131029985958593375 1232896696544978937890063)
  ·
    refine ⟨1849345044817468406835095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1232896696544978937890063 1849345044817468406835095)
    ·
      refine ⟨2774017567226202610252643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1849345044817468406835095 2774017567226202610252643)
      ·
        refine ⟨4161026350839303915378965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2774017567226202610252643 4161026350839303915378965)
        ·
          refine ⟨195048110195592371033389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4161026350839303915378965 195048110195592371033389)
          ·
            refine ⟨73143041323347139137521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 195048110195592371033389 73143041323347139137521)
            ·
              refine ⟨54857280992510354353141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73143041323347139137521 54857280992510354353141)
              ·
                refine ⟨5142870093047845720607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54857280992510354353141 5142870093047845720607)
                ·
                  rfl

theorem cell20_33803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 5].length) (baseStart_33803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33803 prefixEnd_33803 := by exact prefixLift 33803
  have htrace : WordTrace (prefixWord ++ tailWord_33803) baseStart_33803 baseEnd_33803 := by
    simpa [prefixWord, tailWord_33803, baseEnd_33803] using wordTrace_append hprefix tailTrace_33803
  have hstable : (prefixWord ++ tailWord_33803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33803).length < 2 ^ (prefixWord ++ tailWord_33803).sum := by decide
  have hdescent : baseEnd_33803 < baseStart_33803 := by decide
  rcases family_descends (prefixWord ++ tailWord_33803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33806 : List Nat := [4, 1, 1, 2, 2, 2, 4, 1, 3]
def baseStart_33806 : Nat := 118140960795 + 33806 * 2 ^ 59
def prefixEnd_33806 : Nat := 4983230072969 + 3 ^ 40 * 33806 * 2
def baseEnd_33806 : Nat := 15429979560888860061809

theorem tailTrace_33806 : CollatzResearch.WordTrace tailWord_33806 prefixEnd_33806 15429979560888860061809 := by
  unfold tailWord_33806
  simp only [CollatzResearch.WordTrace]
  refine ⟨154125764441763806281159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 822004077022740300166181 154125764441763806281159)
  ·
    refine ⟨231188646662645709421739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154125764441763806281159 231188646662645709421739)
    ·
      refine ⟨346782969993968564132609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231188646662645709421739 346782969993968564132609)
      ·
        refine ⟨260087227495476423099457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 346782969993968564132609 260087227495476423099457)
        ·
          refine ⟨195065420621607317324593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260087227495476423099457 195065420621607317324593)
          ·
            refine ⟨146299065466205487993445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195065420621607317324593 146299065466205487993445)
            ·
              refine ⟨27431074774913528998771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146299065466205487993445 27431074774913528998771)
              ·
                refine ⟨41146612162370293498157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27431074774913528998771 41146612162370293498157)
                ·
                  refine ⟨15429979560888860061809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41146612162370293498157 15429979560888860061809)
                  ·
                    rfl

theorem cell20_33806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_33806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33806 prefixEnd_33806 := by exact prefixLift 33806
  have htrace : WordTrace (prefixWord ++ tailWord_33806) baseStart_33806 baseEnd_33806 := by
    simpa [prefixWord, tailWord_33806, baseEnd_33806] using wordTrace_append hprefix tailTrace_33806
  have hstable : (prefixWord ++ tailWord_33806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33806).length < 2 ^ (prefixWord ++ tailWord_33806).sum := by decide
  have hdescent : baseEnd_33806 < baseStart_33806 := by decide
  rcases family_descends (prefixWord ++ tailWord_33806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33817 : List Nat := [1, 2, 1, 2, 1, 1, 4, 4, 4]
def baseStart_33817 : Nat := 118140960795 + 33817 * 2 ^ 59
def prefixEnd_33817 : Nat := 4983230072969 + 3 ^ 40 * 33817 * 2
def baseEnd_33817 : Nat := 15435000260621710695097

theorem tailTrace_33817 : CollatzResearch.WordTrace tailWord_33817 prefixEnd_33817 15435000260621710695097 := by
  unfold tailWord_33817
  simp only [CollatzResearch.WordTrace]
  refine ⟨1233407318494259328899705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 822271545662839552599803 1233407318494259328899705)
  ·
    refine ⟨925055488870694496674779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1233407318494259328899705 925055488870694496674779)
    ·
      refine ⟨1387583233306041745012169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 925055488870694496674779 1387583233306041745012169)
      ·
        refine ⟨1040687424979531308759127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1387583233306041745012169 1040687424979531308759127)
        ·
          refine ⟨1561031137469296963138691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1040687424979531308759127 1561031137469296963138691)
          ·
            refine ⟨2341546706203945444708037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1561031137469296963138691 2341546706203945444708037)
            ·
              refine ⟨439040007413239770882757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2341546706203945444708037 439040007413239770882757)
              ·
                refine ⟨82320001389982457040517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 439040007413239770882757 82320001389982457040517)
                ·
                  refine ⟨15435000260621710695097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82320001389982457040517 15435000260621710695097)
                  ·
                    rfl

theorem cell20_33817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_33817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33817 prefixEnd_33817 := by exact prefixLift 33817
  have htrace : WordTrace (prefixWord ++ tailWord_33817) baseStart_33817 baseEnd_33817 := by
    simpa [prefixWord, tailWord_33817, baseEnd_33817] using wordTrace_append hprefix tailTrace_33817
  have hstable : (prefixWord ++ tailWord_33817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33817).length < 2 ^ (prefixWord ++ tailWord_33817).sum := by decide
  have hdescent : baseEnd_33817 < baseStart_33817 := by decide
  rcases family_descends (prefixWord ++ tailWord_33817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33844 : List Nat := [2, 5, 1, 2, 1, 1, 1, 4, 3]
def baseStart_33844 : Nat := 118140960795 + 33844 * 2 ^ 59
def prefixEnd_33844 : Nat := 4983230072969 + 3 ^ 40 * 33844 * 2
def baseEnd_33844 : Nat := 15447323796329616794987

theorem tailTrace_33844 : CollatzResearch.WordTrace tailWord_33844 prefixEnd_33844 15447323796329616794987 := by
  unfold tailWord_33844
  simp only [CollatzResearch.WordTrace]
  refine ⟨617196044698221470066293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 822928059597628626755057 617196044698221470066293)
  ·
    refine ⟨57862129190458262818715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 617196044698221470066293 57862129190458262818715)
    ·
      refine ⟨86793193785687394228073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57862129190458262818715 86793193785687394228073)
      ·
        refine ⟨65094895339265545671055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86793193785687394228073 65094895339265545671055)
        ·
          refine ⟨97642343008898318506583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65094895339265545671055 97642343008898318506583)
          ·
            refine ⟨146463514513347477759875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97642343008898318506583 146463514513347477759875)
            ·
              refine ⟨219695271770021216639813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146463514513347477759875 219695271770021216639813)
              ·
                refine ⟨41192863456878978119965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 219695271770021216639813 41192863456878978119965)
                ·
                  refine ⟨15447323796329616794987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41192863456878978119965 15447323796329616794987)
                  ·
                    rfl

theorem cell20_33844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_33844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33844 prefixEnd_33844 := by exact prefixLift 33844
  have htrace : WordTrace (prefixWord ++ tailWord_33844) baseStart_33844 baseEnd_33844 := by
    simpa [prefixWord, tailWord_33844, baseEnd_33844] using wordTrace_append hprefix tailTrace_33844
  have hstable : (prefixWord ++ tailWord_33844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33844).length < 2 ^ (prefixWord ++ tailWord_33844).sum := by decide
  have hdescent : baseEnd_33844 < baseStart_33844 := by decide
  rcases family_descends (prefixWord ++ tailWord_33844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33855 : List Nat := [1, 1, 2, 2, 3, 1, 1, 5, 4]
def baseStart_33855 : Nat := 118140960795 + 33855 * 2 ^ 59
def prefixEnd_33855 : Nat := 4983230072969 + 3 ^ 40 * 33855 * 2
def baseEnd_33855 : Nat := 15452344496062467428275

theorem tailTrace_33855 : CollatzResearch.WordTrace tailWord_33855 prefixEnd_33855 15452344496062467428275 := by
  unfold tailWord_33855
  simp only [CollatzResearch.WordTrace]
  refine ⟨1234793292356591818783019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 823195528237727879188679 1234793292356591818783019)
  ·
    refine ⟨1852189938534887728174529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1234793292356591818783019 1852189938534887728174529)
    ·
      refine ⟨1389142453901165796130897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1852189938534887728174529 1389142453901165796130897)
      ·
        refine ⟨1041856840425874347098173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1389142453901165796130897 1041856840425874347098173)
        ·
          refine ⟨390696315159702880161815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1041856840425874347098173 390696315159702880161815)
          ·
            refine ⟨586044472739554320242723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390696315159702880161815 586044472739554320242723)
            ·
              refine ⟨879066709109331480364085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586044472739554320242723 879066709109331480364085)
              ·
                refine ⟨82412503978999826284133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 879066709109331480364085 82412503978999826284133)
                ·
                  refine ⟨15452344496062467428275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82412503978999826284133 15452344496062467428275)
                  ·
                    rfl

theorem cell20_33855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 4].length) (baseStart_33855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33855 prefixEnd_33855 := by exact prefixLift 33855
  have htrace : WordTrace (prefixWord ++ tailWord_33855) baseStart_33855 baseEnd_33855 := by
    simpa [prefixWord, tailWord_33855, baseEnd_33855] using wordTrace_append hprefix tailTrace_33855
  have hstable : (prefixWord ++ tailWord_33855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33855).length < 2 ^ (prefixWord ++ tailWord_33855).sum := by decide
  have hdescent : baseEnd_33855 < baseStart_33855 := by decide
  rcases family_descends (prefixWord ++ tailWord_33855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33885 : List Nat := [1, 4, 4, 1, 2, 1, 2, 3, 2]
def baseStart_33885 : Nat := 118140960795 + 33885 * 2 ^ 59
def prefixEnd_33885 : Nat := 4983230072969 + 3 ^ 40 * 33885 * 2
def baseEnd_33885 : Nat := 15466037313515696428153

theorem tailTrace_33885 : CollatzResearch.WordTrace tailWord_33885 prefixEnd_33885 15466037313515696428153 := by
  unfold tailWord_33885
  simp only [CollatzResearch.WordTrace]
  refine ⟨1235887482247906942375109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 823924988165271294916739 1235887482247906942375109)
  ·
    refine ⟨231728902921482551695333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1235887482247906942375109 231728902921482551695333)
    ·
      refine ⟨43449169297777978442875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 231728902921482551695333 43449169297777978442875)
      ·
        refine ⟨65173753946666967664313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43449169297777978442875 65173753946666967664313)
        ·
          refine ⟨48880315460000225748235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65173753946666967664313 48880315460000225748235)
          ·
            refine ⟨73320473190000338622353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48880315460000225748235 73320473190000338622353)
            ·
              refine ⟨54990354892500253966765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73320473190000338622353 54990354892500253966765)
              ·
                refine ⟨20621383084687595237537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54990354892500253966765 20621383084687595237537)
                ·
                  refine ⟨15466037313515696428153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20621383084687595237537 15466037313515696428153)
                  ·
                    rfl

theorem cell20_33885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_33885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33885 prefixEnd_33885 := by exact prefixLift 33885
  have htrace : WordTrace (prefixWord ++ tailWord_33885) baseStart_33885 baseEnd_33885 := by
    simpa [prefixWord, tailWord_33885, baseEnd_33885] using wordTrace_append hprefix tailTrace_33885
  have hstable : (prefixWord ++ tailWord_33885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33885).length < 2 ^ (prefixWord ++ tailWord_33885).sum := by decide
  have hdescent : baseEnd_33885 < baseStart_33885 := by decide
  rcases family_descends (prefixWord ++ tailWord_33885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33893 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 6]
def baseStart_33893 : Nat := 118140960795 + 33893 * 2 ^ 59
def prefixEnd_33893 : Nat := 4983230072969 + 3 ^ 40 * 33893 * 2
def baseEnd_33893 : Nat := 15469688731503224161453

theorem tailTrace_33893 : CollatzResearch.WordTrace tailWord_33893 prefixEnd_33893 15469688731503224161453 := by
  unfold tailWord_33893
  simp only [CollatzResearch.WordTrace]
  refine ⟨1236179266218924308666333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 824119510812616205777555 1236179266218924308666333)
  ·
    refine ⟨463567224832096615749875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1236179266218924308666333 463567224832096615749875)
    ·
      refine ⟨695350837248144923624813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 463567224832096615749875 695350837248144923624813)
      ·
        refine ⟨260756563968054346359305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 695350837248144923624813 260756563968054346359305)
        ·
          refine ⟨195567422976040759769479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260756563968054346359305 195567422976040759769479)
          ·
            refine ⟨293351134464061139654219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195567422976040759769479 293351134464061139654219)
            ·
              refine ⟨440026701696091709481329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293351134464061139654219 440026701696091709481329)
              ·
                refine ⟨330020026272068782110997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 440026701696091709481329 330020026272068782110997)
                ·
                  refine ⟨15469688731503224161453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 330020026272068782110997 15469688731503224161453)
                  ·
                    rfl

theorem cell20_33893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_33893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33893 prefixEnd_33893 := by exact prefixLift 33893
  have htrace : WordTrace (prefixWord ++ tailWord_33893) baseStart_33893 baseEnd_33893 := by
    simpa [prefixWord, tailWord_33893, baseEnd_33893] using wordTrace_append hprefix tailTrace_33893
  have hstable : (prefixWord ++ tailWord_33893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33893).length < 2 ^ (prefixWord ++ tailWord_33893).sum := by decide
  have hdescent : baseEnd_33893 < baseStart_33893 := by decide
  rcases family_descends (prefixWord ++ tailWord_33893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33896 : List Nat := [2, 1, 4, 4, 1, 1, 7]
def baseStart_33896 : Nat := 118140960795 + 33896 * 2 ^ 59
def prefixEnd_33896 : Nat := 4983230072969 + 3 ^ 40 * 33896 * 2
def baseEnd_33896 : Nat := 1719006445916505229049

theorem tailTrace_33896 : CollatzResearch.WordTrace tailWord_33896 prefixEnd_33896 1719006445916505229049 := by
  unfold tailWord_33896
  simp only [CollatzResearch.WordTrace]
  refine ⟨618144342604027910512771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 824192456805370547350361 618144342604027910512771)
  ·
    refine ⟨927216513906041865769157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 618144342604027910512771 927216513906041865769157)
    ·
      refine ⟨173853096357382849831717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 927216513906041865769157 173853096357382849831717)
      ·
        refine ⟨32597455567009284343447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173853096357382849831717 32597455567009284343447)
        ·
          refine ⟨48896183350513926515171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32597455567009284343447 48896183350513926515171)
          ·
            refine ⟨73344275025770889772757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48896183350513926515171 73344275025770889772757)
            ·
              refine ⟨1719006445916505229049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 73344275025770889772757 1719006445916505229049)
              ·
                rfl

theorem cell20_33896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 7].length) (baseStart_33896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33896 prefixEnd_33896 := by exact prefixLift 33896
  have htrace : WordTrace (prefixWord ++ tailWord_33896) baseStart_33896 baseEnd_33896 := by
    simpa [prefixWord, tailWord_33896, baseEnd_33896] using wordTrace_append hprefix tailTrace_33896
  have hstable : (prefixWord ++ tailWord_33896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33896).length < 2 ^ (prefixWord ++ tailWord_33896).sum := by decide
  have hdescent : baseEnd_33896 < baseStart_33896 := by decide
  rcases family_descends (prefixWord ++ tailWord_33896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33900 : List Nat := [2, 2, 1, 1, 3, 2, 9]
def baseStart_33900 : Nat := 118140960795 + 33900 * 2 ^ 59
def prefixEnd_33900 : Nat := 4983230072969 + 3 ^ 40 * 33900 * 2
def baseEnd_33900 : Nat := 1719209302471367880899

theorem tailTrace_33900 : CollatzResearch.WordTrace tailWord_33900 prefixEnd_33900 1719209302471367880899 := by
  unfold tailWord_33900
  simp only [CollatzResearch.WordTrace]
  refine ⟨618217288596782252085577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 824289718129043002780769 618217288596782252085577)
  ·
    refine ⟨463662966447586689064183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 618217288596782252085577 463662966447586689064183)
    ·
      refine ⟨695494449671380033596275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 463662966447586689064183 695494449671380033596275)
      ·
        refine ⟨1043241674507070050394413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 695494449671380033596275 1043241674507070050394413)
        ·
          refine ⟨391215627940151268897905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1043241674507070050394413 391215627940151268897905)
          ·
            refine ⟨293411720955113451673429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 391215627940151268897905 293411720955113451673429)
            ·
              refine ⟨1719209302471367880899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 293411720955113451673429 1719209302471367880899)
              ·
                rfl

theorem cell20_33900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 9].length) (baseStart_33900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33900 prefixEnd_33900 := by exact prefixLift 33900
  have htrace : WordTrace (prefixWord ++ tailWord_33900) baseStart_33900 baseEnd_33900 := by
    simpa [prefixWord, tailWord_33900, baseEnd_33900] using wordTrace_append hprefix tailTrace_33900
  have hstable : (prefixWord ++ tailWord_33900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33900).length < 2 ^ (prefixWord ++ tailWord_33900).sum := by decide
  have hdescent : baseEnd_33900 < baseStart_33900 := by decide
  rcases family_descends (prefixWord ++ tailWord_33900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33934 : List Nat := [4, 1, 1, 3, 2, 1, 4, 4]
def baseStart_33934 : Nat := 118140960795 + 33934 * 2 ^ 59
def prefixEnd_33934 : Nat := 4983230072969 + 3 ^ 40 * 33934 * 2
def baseEnd_33934 : Nat := 5162800749563101264873

theorem tailTrace_33934 : CollatzResearch.WordTrace tailWord_33934 prefixEnd_33934 5162800749563101264873 := by
  unfold tailWord_33934
  simp only [CollatzResearch.WordTrace]
  refine ⟨154709332383798538863607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 825116439380258873939237 154709332383798538863607)
  ·
    refine ⟨232063998575697808295411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154709332383798538863607 232063998575697808295411)
    ·
      refine ⟨348095997863546712443117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232063998575697808295411 348095997863546712443117)
      ·
        refine ⟨130535999198830017166169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 348095997863546712443117 130535999198830017166169)
        ·
          refine ⟨97901999399122512874627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130535999198830017166169 97901999399122512874627)
          ·
            refine ⟨146852999098683769311941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97901999399122512874627 146852999098683769311941)
            ·
              refine ⟨27534937331003206745989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146852999098683769311941 27534937331003206745989)
              ·
                refine ⟨5162800749563101264873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27534937331003206745989 5162800749563101264873)
                ·
                  rfl

theorem cell20_33934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_33934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33934 prefixEnd_33934 := by exact prefixLift 33934
  have htrace : WordTrace (prefixWord ++ tailWord_33934) baseStart_33934 baseEnd_33934 := by
    simpa [prefixWord, tailWord_33934, baseEnd_33934] using wordTrace_append hprefix tailTrace_33934
  have hstable : (prefixWord ++ tailWord_33934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33934).length < 2 ^ (prefixWord ++ tailWord_33934).sum := by decide
  have hdescent : baseEnd_33934 < baseStart_33934 := by decide
  rcases family_descends (prefixWord ++ tailWord_33934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33944 : List Nat := [2, 1, 2, 4, 2, 3, 1, 3, 2]
def baseStart_33944 : Nat := 118140960795 + 33944 * 2 ^ 59
def prefixEnd_33944 : Nat := 4983230072969 + 3 ^ 40 * 33944 * 2
def baseEnd_33944 : Nat := 15492966521173713461245

theorem tailTrace_33944 : CollatzResearch.WordTrace tailWord_33944 prefixEnd_33944 15492966521173713461245 := by
  unfold tailWord_33944
  simp only [CollatzResearch.WordTrace]
  refine ⟨619019694517080009386443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 825359592689440012515257 619019694517080009386443)
  ·
    refine ⟨928529541775620014079665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 619019694517080009386443 928529541775620014079665)
    ·
      refine ⟨696397156331715010559749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 928529541775620014079665 696397156331715010559749)
      ·
        refine ⟨130574466812196564479953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 696397156331715010559749 130574466812196564479953)
        ·
          refine ⟨97930850109147423359965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130574466812196564479953 97930850109147423359965)
          ·
            refine ⟨36724068790930283759987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97930850109147423359965 36724068790930283759987)
            ·
              refine ⟨55086103186395425639981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36724068790930283759987 55086103186395425639981)
              ·
                refine ⟨20657288694898284614993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55086103186395425639981 20657288694898284614993)
                ·
                  refine ⟨15492966521173713461245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20657288694898284614993 15492966521173713461245)
                  ·
                    rfl

theorem cell20_33944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 2].length) (baseStart_33944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_33944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_33944 prefixEnd_33944 := by exact prefixLift 33944
  have htrace : WordTrace (prefixWord ++ tailWord_33944) baseStart_33944 baseEnd_33944 := by
    simpa [prefixWord, tailWord_33944, baseEnd_33944] using wordTrace_append hprefix tailTrace_33944
  have hstable : (prefixWord ++ tailWord_33944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33944).length < 2 ^ (prefixWord ++ tailWord_33944).sum := by decide
  have hdescent : baseEnd_33944 < baseStart_33944 := by decide
  rcases family_descends (prefixWord ++ tailWord_33944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34017 : List Nat := [1, 2, 3, 1, 3, 3, 2, 2, 3]
def baseStart_34017 : Nat := 118140960795 + 34017 * 2 ^ 59
def prefixEnd_34017 : Nat := 4983230072969 + 3 ^ 40 * 34017 * 2
def baseEnd_34017 : Nat := 15526285710309904027613

theorem tailTrace_34017 : CollatzResearch.WordTrace tailWord_34017 prefixEnd_34017 15526285710309904027613 := by
  unfold tailWord_34017
  simp only [CollatzResearch.WordTrace]
  refine ⟨1240701917769693486180305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 827134611846462324120203 1240701917769693486180305)
  ·
    refine ⟨930526438327270114635229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1240701917769693486180305 930526438327270114635229)
    ·
      refine ⟨348947414372726292988211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 930526438327270114635229 348947414372726292988211)
      ·
        refine ⟨523421121559089439482317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348947414372726292988211 523421121559089439482317)
        ·
          refine ⟨196282920584658539805869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 523421121559089439482317 196282920584658539805869)
          ·
            refine ⟨73606095219246952427201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 196282920584658539805869 73606095219246952427201)
            ·
              refine ⟨55204571414435214320401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73606095219246952427201 55204571414435214320401)
              ·
                refine ⟨41403428560826410740301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55204571414435214320401 41403428560826410740301)
                ·
                  refine ⟨15526285710309904027613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41403428560826410740301 15526285710309904027613)
                  ·
                    rfl

theorem cell20_34017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 3].length) (baseStart_34017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34017 prefixEnd_34017 := by exact prefixLift 34017
  have htrace : WordTrace (prefixWord ++ tailWord_34017) baseStart_34017 baseEnd_34017 := by
    simpa [prefixWord, tailWord_34017, baseEnd_34017] using wordTrace_append hprefix tailTrace_34017
  have hstable : (prefixWord ++ tailWord_34017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34017).length < 2 ^ (prefixWord ++ tailWord_34017).sum := by decide
  have hdescent : baseEnd_34017 < baseStart_34017 := by decide
  rcases family_descends (prefixWord ++ tailWord_34017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34038 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_34038 : Nat := 118140960795 + 34038 * 2 ^ 59
def prefixEnd_34038 : Nat := 4983230072969 + 3 ^ 40 * 34038 * 2
def baseEnd_34038 : Nat := 15535870682527164327527

theorem tailTrace_34038 : CollatzResearch.WordTrace tailWord_34038 prefixEnd_34038 15535870682527164327527 := by
  unfold tailWord_34038
  simp only [CollatzResearch.WordTrace]
  refine ⟨77591740668350879543423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 827645233795742715129845 77591740668350879543423)
  ·
    refine ⟨116387611002526319315135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77591740668350879543423 116387611002526319315135)
    ·
      refine ⟨174581416503789478972703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116387611002526319315135 174581416503789478972703)
      ·
        refine ⟨261872124755684218459055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174581416503789478972703 261872124755684218459055)
        ·
          refine ⟨392808187133526327688583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261872124755684218459055 392808187133526327688583)
          ·
            refine ⟨589212280700289491532875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392808187133526327688583 589212280700289491532875)
            ·
              refine ⟨883818421050434237299313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 589212280700289491532875 883818421050434237299313)
              ·
                refine ⟨662863815787825677974485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 883818421050434237299313 662863815787825677974485)
                ·
                  refine ⟨15535870682527164327527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 662863815787825677974485 15535870682527164327527)
                  ·
                    rfl

theorem cell20_34038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_34038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34038 prefixEnd_34038 := by exact prefixLift 34038
  have htrace : WordTrace (prefixWord ++ tailWord_34038) baseStart_34038 baseEnd_34038 := by
    simpa [prefixWord, tailWord_34038, baseEnd_34038] using wordTrace_append hprefix tailTrace_34038
  have hstable : (prefixWord ++ tailWord_34038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34038).length < 2 ^ (prefixWord ++ tailWord_34038).sum := by decide
  have hdescent : baseEnd_34038 < baseStart_34038 := by decide
  rcases family_descends (prefixWord ++ tailWord_34038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34083 : List Nat := [1, 1, 1, 4, 2, 3, 1, 3, 4]
def baseStart_34083 : Nat := 118140960795 + 34083 * 2 ^ 59
def prefixEnd_34083 : Nat := 4983230072969 + 3 ^ 40 * 34083 * 2
def baseEnd_34083 : Nat := 15556409908707007827343

theorem tailTrace_34083 : CollatzResearch.WordTrace tailWord_34083 prefixEnd_34083 15556409908707007827343 := by
  unfold tailWord_34083
  simp only [CollatzResearch.WordTrace]
  refine ⟨1243109135530586758082903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 828739423687057838721935 1243109135530586758082903)
  ·
    refine ⟨1864663703295880137124355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1243109135530586758082903 1864663703295880137124355)
    ·
      refine ⟨2796995554943820205686533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1864663703295880137124355 2796995554943820205686533)
      ·
        refine ⟨524436666551966288566225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2796995554943820205686533 524436666551966288566225)
        ·
          refine ⟨393327499913974716424669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 524436666551966288566225 393327499913974716424669)
          ·
            refine ⟨147497812467740518659251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 393327499913974716424669 147497812467740518659251)
            ·
              refine ⟨221246718701610777988877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147497812467740518659251 221246718701610777988877)
              ·
                refine ⟨82967519513104041745829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 221246718701610777988877 82967519513104041745829)
                ·
                  refine ⟨15556409908707007827343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82967519513104041745829 15556409908707007827343)
                  ·
                    rfl

theorem cell20_34083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 4].length) (baseStart_34083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34083 prefixEnd_34083 := by exact prefixLift 34083
  have htrace : WordTrace (prefixWord ++ tailWord_34083) baseStart_34083 baseEnd_34083 := by
    simpa [prefixWord, tailWord_34083, baseEnd_34083] using wordTrace_append hprefix tailTrace_34083
  have hstable : (prefixWord ++ tailWord_34083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34083).length < 2 ^ (prefixWord ++ tailWord_34083).sum := by decide
  have hdescent : baseEnd_34083 < baseStart_34083 := by decide
  rcases family_descends (prefixWord ++ tailWord_34083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34100 : List Nat := [2, 5, 1, 1, 1, 1, 1, 4, 4]
def baseStart_34100 : Nat := 118140960795 + 34100 * 2 ^ 59
def prefixEnd_34100 : Nat := 4983230072969 + 3 ^ 40 * 34100 * 2
def baseEnd_34100 : Nat := 15564169171930504260607

theorem tailTrace_34100 : CollatzResearch.WordTrace tailWord_34100 prefixEnd_34100 15564169171930504260607 := by
  unfold tailWord_34100
  simp only [CollatzResearch.WordTrace]
  refine ⟨621864588234499330725877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 829152784312665774301169 621864588234499330725877)
  ·
    refine ⟨58299805146984312255551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 621864588234499330725877 58299805146984312255551)
    ·
      refine ⟨87449707720476468383327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58299805146984312255551 87449707720476468383327)
      ·
        refine ⟨131174561580714702574991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87449707720476468383327 131174561580714702574991)
        ·
          refine ⟨196761842371072053862487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131174561580714702574991 196761842371072053862487)
          ·
            refine ⟨295142763556608080793731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196761842371072053862487 295142763556608080793731)
            ·
              refine ⟨442714145334912121190597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295142763556608080793731 442714145334912121190597)
              ·
                refine ⟨83008902250296022723237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 442714145334912121190597 83008902250296022723237)
                ·
                  refine ⟨15564169171930504260607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83008902250296022723237 15564169171930504260607)
                  ·
                    rfl

theorem cell20_34100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_34100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34100 prefixEnd_34100 := by exact prefixLift 34100
  have htrace : WordTrace (prefixWord ++ tailWord_34100) baseStart_34100 baseEnd_34100 := by
    simpa [prefixWord, tailWord_34100, baseEnd_34100] using wordTrace_append hprefix tailTrace_34100
  have hstable : (prefixWord ++ tailWord_34100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34100).length < 2 ^ (prefixWord ++ tailWord_34100).sum := by decide
  have hdescent : baseEnd_34100 < baseStart_34100 := by decide
  rcases family_descends (prefixWord ++ tailWord_34100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34138 : List Nat := [3, 1, 1, 2, 1, 2, 2, 6, 2]
def baseStart_34138 : Nat := 118140960795 + 34138 * 2 ^ 59
def prefixEnd_34138 : Nat := 4983230072969 + 3 ^ 40 * 34138 * 2
def baseEnd_34138 : Nat := 15581513407371260993785

theorem tailTrace_34138 : CollatzResearch.WordTrace tailWord_34138 prefixEnd_34138 15581513407371260993785 := by
  unfold tailWord_34138
  simp only [CollatzResearch.WordTrace]
  refine ⟨311278787582832787833767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 830076766887554100890045 311278787582832787833767)
  ·
    refine ⟨466918181374249181750651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 311278787582832787833767 466918181374249181750651)
    ·
      refine ⟨700377272061373772625977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 466918181374249181750651 700377272061373772625977)
      ·
        refine ⟨525282954046030329469483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 700377272061373772625977 525282954046030329469483)
        ·
          refine ⟨787924431069045494204225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525282954046030329469483 787924431069045494204225)
          ·
            refine ⟨590943323301784120653169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 787924431069045494204225 590943323301784120653169)
            ·
              refine ⟨443207492476338090489877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 590943323301784120653169 443207492476338090489877)
              ·
                refine ⟨20775351209828347991713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 443207492476338090489877 20775351209828347991713)
                ·
                  refine ⟨15581513407371260993785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20775351209828347991713 15581513407371260993785)
                  ·
                    rfl

theorem cell20_34138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 2].length) (baseStart_34138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34138 prefixEnd_34138 := by exact prefixLift 34138
  have htrace : WordTrace (prefixWord ++ tailWord_34138) baseStart_34138 baseEnd_34138 := by
    simpa [prefixWord, tailWord_34138, baseEnd_34138] using wordTrace_append hprefix tailTrace_34138
  have hstable : (prefixWord ++ tailWord_34138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34138).length < 2 ^ (prefixWord ++ tailWord_34138).sum := by decide
  have hdescent : baseEnd_34138 < baseStart_34138 := by decide
  rcases family_descends (prefixWord ++ tailWord_34138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34148 : List Nat := [2, 3, 1, 1, 3, 4, 2, 1, 3]
def baseStart_34148 : Nat := 118140960795 + 34148 * 2 ^ 59
def prefixEnd_34148 : Nat := 4983230072969 + 3 ^ 40 * 34148 * 2
def baseEnd_34148 : Nat := 15586077679855670660411

theorem tailTrace_34148 : CollatzResearch.WordTrace tailWord_34148 prefixEnd_34148 15586077679855670660411 := by
  unfold tailWord_34148
  simp only [CollatzResearch.WordTrace]
  refine ⟨622739940147551429599549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 830319920196735239466065 622739940147551429599549)
  ·
    refine ⟨233527477555331786099831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 622739940147551429599549 233527477555331786099831)
    ·
      refine ⟨350291216332997679149747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233527477555331786099831 350291216332997679149747)
      ·
        refine ⟨525436824499496518724621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350291216332997679149747 525436824499496518724621)
        ·
          refine ⟨197038809187311194521733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 525436824499496518724621 197038809187311194521733)
          ·
            refine ⟨36944776722620848972825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 197038809187311194521733 36944776722620848972825)
            ·
              refine ⟨27708582541965636729619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36944776722620848972825 27708582541965636729619)
              ·
                refine ⟨41562873812948455094429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27708582541965636729619 41562873812948455094429)
                ·
                  refine ⟨15586077679855670660411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41562873812948455094429 15586077679855670660411)
                  ·
                    rfl

theorem cell20_34148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_34148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34148 prefixEnd_34148 := by exact prefixLift 34148
  have htrace : WordTrace (prefixWord ++ tailWord_34148) baseStart_34148 baseEnd_34148 := by
    simpa [prefixWord, tailWord_34148, baseEnd_34148] using wordTrace_append hprefix tailTrace_34148
  have hstable : (prefixWord ++ tailWord_34148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34148).length < 2 ^ (prefixWord ++ tailWord_34148).sum := by decide
  have hdescent : baseEnd_34148 < baseStart_34148 := by decide
  rcases family_descends (prefixWord ++ tailWord_34148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34200 : List Nat := [2, 1, 2, 5, 2, 2, 1, 5]
def baseStart_34200 : Nat := 118140960795 + 34200 * 2 ^ 59
def prefixEnd_34200 : Nat := 4983230072969 + 3 ^ 40 * 34200 * 2
def baseEnd_34200 : Nat := 5203270632258200308955

theorem tailTrace_34200 : CollatzResearch.WordTrace tailWord_34200 prefixEnd_34200 5203270632258200308955 := by
  unfold tailWord_34200
  simp only [CollatzResearch.WordTrace]
  refine ⟨623688238053357870046027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 831584317404477160061369 623688238053357870046027)
  ·
    refine ⟨935532357080036805069041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 623688238053357870046027 935532357080036805069041)
    ·
      refine ⟨701649267810027603801781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 935532357080036805069041 701649267810027603801781)
      ·
        refine ⟨65779618857190087856417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 701649267810027603801781 65779618857190087856417)
        ·
          refine ⟨49334714142892565892313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65779618857190087856417 49334714142892565892313)
          ·
            refine ⟨37001035607169424419235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49334714142892565892313 37001035607169424419235)
            ·
              refine ⟨55501553410754136628853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37001035607169424419235 55501553410754136628853)
              ·
                refine ⟨5203270632258200308955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55501553410754136628853 5203270632258200308955)
                ·
                  rfl

theorem cell20_34200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 5].length) (baseStart_34200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34200 prefixEnd_34200 := by exact prefixLift 34200
  have htrace : WordTrace (prefixWord ++ tailWord_34200) baseStart_34200 baseEnd_34200 := by
    simpa [prefixWord, tailWord_34200, baseEnd_34200] using wordTrace_append hprefix tailTrace_34200
  have hstable : (prefixWord ++ tailWord_34200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34200).length < 2 ^ (prefixWord ++ tailWord_34200).sum := by decide
  have hdescent : baseEnd_34200 < baseStart_34200 := by decide
  rcases family_descends (prefixWord ++ tailWord_34200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34252 : List Nat := [2, 2, 1, 4, 2, 2, 2, 1, 4]
def baseStart_34252 : Nat := 118140960795 + 34252 * 2 ^ 59
def prefixEnd_34252 : Nat := 4983230072969 + 3 ^ 40 * 34252 * 2
def baseEnd_34252 : Nat := 15633546113693531193319

theorem tailTrace_34252 : CollatzResearch.WordTrace tailWord_34252 prefixEnd_34252 15633546113693531193319 := by
  unfold tailWord_34252
  simp only [CollatzResearch.WordTrace]
  refine ⟨624636535959164310492505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 832848714612219080656673 624636535959164310492505)
  ·
    refine ⟨468477401969373232869379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 624636535959164310492505 468477401969373232869379)
    ·
      refine ⟨702716102954059849304069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 468477401969373232869379 702716102954059849304069)
      ·
        refine ⟨131759269303886221744513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 702716102954059849304069 131759269303886221744513)
        ·
          refine ⟨98819451977914666308385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131759269303886221744513 98819451977914666308385)
          ·
            refine ⟨74114588983435999731289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98819451977914666308385 74114588983435999731289)
            ·
              refine ⟨55585941737576999798467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74114588983435999731289 55585941737576999798467)
              ·
                refine ⟨83378912606365499697701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55585941737576999798467 83378912606365499697701)
                ·
                  refine ⟨15633546113693531193319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83378912606365499697701 15633546113693531193319)
                  ·
                    rfl

theorem cell20_34252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_34252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34252 prefixEnd_34252 := by exact prefixLift 34252
  have htrace : WordTrace (prefixWord ++ tailWord_34252) baseStart_34252 baseEnd_34252 := by
    simpa [prefixWord, tailWord_34252, baseEnd_34252] using wordTrace_append hprefix tailTrace_34252
  have hstable : (prefixWord ++ tailWord_34252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34252).length < 2 ^ (prefixWord ++ tailWord_34252).sum := by decide
  have hdescent : baseEnd_34252 < baseStart_34252 := by decide
  rcases family_descends (prefixWord ++ tailWord_34252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34256 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 8]
def baseStart_34256 : Nat := 118140960795 + 34256 * 2 ^ 59
def prefixEnd_34256 : Nat := 4983230072969 + 3 ^ 40 * 34256 * 2
def baseEnd_34256 : Nat := 15635371822687295059969

theorem tailTrace_34256 : CollatzResearch.WordTrace tailWord_34256 prefixEnd_34256 15635371822687295059969 := by
  unfold tailWord_34256
  simp only [CollatzResearch.WordTrace]
  refine ⟨624709481951918652065311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 832945975935891536087081 624709481951918652065311)
  ·
    refine ⟨937064222927877978097967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 624709481951918652065311 937064222927877978097967)
    ·
      refine ⟨1405596334391816967146951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 937064222927877978097967 1405596334391816967146951)
      ·
        refine ⟨2108394501587725450720427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1405596334391816967146951 2108394501587725450720427)
        ·
          refine ⟨3162591752381588176080641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2108394501587725450720427 3162591752381588176080641)
          ·
            refine ⟨2371943814286191132060481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3162591752381588176080641 2371943814286191132060481)
            ·
              refine ⟨1778957860714643349045361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2371943814286191132060481 1778957860714643349045361)
              ·
                refine ⟨1334218395535982511784021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1778957860714643349045361 1334218395535982511784021)
                ·
                  refine ⟨15635371822687295059969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1334218395535982511784021 15635371822687295059969)
                  ·
                    rfl

theorem cell20_34256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_34256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34256 prefixEnd_34256 := by exact prefixLift 34256
  have htrace : WordTrace (prefixWord ++ tailWord_34256) baseStart_34256 baseEnd_34256 := by
    simpa [prefixWord, tailWord_34256, baseEnd_34256] using wordTrace_append hprefix tailTrace_34256
  have hstable : (prefixWord ++ tailWord_34256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34256).length < 2 ^ (prefixWord ++ tailWord_34256).sum := by decide
  have hdescent : baseEnd_34256 < baseStart_34256 := by decide
  rcases family_descends (prefixWord ++ tailWord_34256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34273 : List Nat := [1, 2, 3, 1, 2, 3, 2, 2, 4]
def baseStart_34273 : Nat := 118140960795 + 34273 * 2 ^ 59
def prefixEnd_34273 : Nat := 4983230072969 + 3 ^ 40 * 34273 * 2
def baseEnd_34273 : Nat := 15643131085910791493233

theorem tailTrace_34273 : CollatzResearch.WordTrace tailWord_34273 prefixEnd_34273 15643131085910791493233 := by
  unfold tailWord_34273
  simp only [CollatzResearch.WordTrace]
  refine ⟨1250039004842249207499473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 833359336561499471666315 1250039004842249207499473)
  ·
    refine ⟨937529253631686905624605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1250039004842249207499473 937529253631686905624605)
    ·
      refine ⟨351573470111882589609227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 937529253631686905624605 351573470111882589609227)
      ·
        refine ⟨527360205167823884413841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351573470111882589609227 527360205167823884413841)
        ·
          refine ⟨395520153875867913310381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 527360205167823884413841 395520153875867913310381)
          ·
            refine ⟨148320057703450467491393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 395520153875867913310381 148320057703450467491393)
            ·
              refine ⟨111240043277587850618545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148320057703450467491393 111240043277587850618545)
              ·
                refine ⟨83430032458190887963909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111240043277587850618545 83430032458190887963909)
                ·
                  refine ⟨15643131085910791493233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83430032458190887963909 15643131085910791493233)
                  ·
                    rfl

theorem cell20_34273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_34273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34273 prefixEnd_34273 := by exact prefixLift 34273
  have htrace : WordTrace (prefixWord ++ tailWord_34273) baseStart_34273 baseEnd_34273 := by
    simpa [prefixWord, tailWord_34273, baseEnd_34273] using wordTrace_append hprefix tailTrace_34273
  have hstable : (prefixWord ++ tailWord_34273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34273).length < 2 ^ (prefixWord ++ tailWord_34273).sum := by decide
  have hdescent : baseEnd_34273 < baseStart_34273 := by decide
  rcases family_descends (prefixWord ++ tailWord_34273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34280 : List Nat := [2, 1, 4, 1, 1, 2, 3, 6]
def baseStart_34280 : Nat := 118140960795 + 34280 * 2 ^ 59
def prefixEnd_34280 : Nat := 4983230072969 + 3 ^ 40 * 34280 * 2
def baseEnd_34280 : Nat := 5215442025549959419957

theorem tailTrace_34280 : CollatzResearch.WordTrace tailWord_34280 prefixEnd_34280 5215442025549959419957 := by
  unfold tailWord_34280
  simp only [CollatzResearch.WordTrace]
  refine ⟨625147157908444701502147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 833529543877926268669529 625147157908444701502147)
  ·
    refine ⟨937720736862667052253221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 625147157908444701502147 937720736862667052253221)
    ·
      refine ⟨175822638161750072297479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 937720736862667052253221 175822638161750072297479)
      ·
        refine ⟨263733957242625108446219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175822638161750072297479 263733957242625108446219)
        ·
          refine ⟨395600935863937662669329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263733957242625108446219 395600935863937662669329)
          ·
            refine ⟨296700701897953247001997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 395600935863937662669329 296700701897953247001997)
            ·
              refine ⟨111262763211732467625749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 296700701897953247001997 111262763211732467625749)
              ·
                refine ⟨5215442025549959419957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 111262763211732467625749 5215442025549959419957)
                ·
                  rfl

theorem cell20_34280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_34280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34280 prefixEnd_34280 := by exact prefixLift 34280
  have htrace : WordTrace (prefixWord ++ tailWord_34280) baseStart_34280 baseEnd_34280 := by
    simpa [prefixWord, tailWord_34280, baseEnd_34280] using wordTrace_append hprefix tailTrace_34280
  have hstable : (prefixWord ++ tailWord_34280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34280).length < 2 ^ (prefixWord ++ tailWord_34280).sum := by decide
  have hdescent : baseEnd_34280 < baseStart_34280 := by decide
  rcases family_descends (prefixWord ++ tailWord_34280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34287 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 5]
def baseStart_34287 : Nat := 118140960795 + 34287 * 2 ^ 59
def prefixEnd_34287 : Nat := 4983230072969 + 3 ^ 40 * 34287 * 2
def baseEnd_34287 : Nat := 15649521067388965026509

theorem tailTrace_34287 : CollatzResearch.WordTrace tailWord_34287 prefixEnd_34287 15649521067388965026509 := by
  unfold tailWord_34287
  simp only [CollatzResearch.WordTrace]
  refine ⟨1250549626791529598509115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 833699751194353065672743 1250549626791529598509115)
  ·
    refine ⟨1875824440187294397763673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1250549626791529598509115 1875824440187294397763673)
    ·
      refine ⟨1406868330140470798322755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1875824440187294397763673 1406868330140470798322755)
      ·
        refine ⟨2110302495210706197484133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1406868330140470798322755 2110302495210706197484133)
        ·
          refine ⟨395681717852007412028275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2110302495210706197484133 395681717852007412028275)
          ·
            refine ⟨593522576778011118042413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395681717852007412028275 593522576778011118042413)
            ·
              refine ⟨222570966291754169265905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 593522576778011118042413 222570966291754169265905)
              ·
                refine ⟨166928224718815626949429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 222570966291754169265905 166928224718815626949429)
                ·
                  refine ⟨15649521067388965026509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 166928224718815626949429 15649521067388965026509)
                  ·
                    rfl

theorem cell20_34287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_34287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34287 prefixEnd_34287 := by exact prefixLift 34287
  have htrace : WordTrace (prefixWord ++ tailWord_34287) baseStart_34287 baseEnd_34287 := by
    simpa [prefixWord, tailWord_34287, baseEnd_34287] using wordTrace_append hprefix tailTrace_34287
  have hstable : (prefixWord ++ tailWord_34287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34287).length < 2 ^ (prefixWord ++ tailWord_34287).sum := by decide
  have hdescent : baseEnd_34287 < baseStart_34287 := by decide
  rcases family_descends (prefixWord ++ tailWord_34287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34310 : List Nat := [6, 2, 1, 1, 2, 1, 2, 5]
def baseStart_34310 : Nat := 118140960795 + 34310 * 2 ^ 59
def prefixEnd_34310 : Nat := 4983230072969 + 3 ^ 40 * 34310 * 2
def baseEnd_34310 : Nat := 5220006298034369086583

theorem tailTrace_34310 : CollatzResearch.WordTrace tailWord_34310 prefixEnd_34310 5220006298034369086583 := by
  unfold tailWord_34310
  simp only [CollatzResearch.WordTrace]
  refine ⟨39105890803381391456137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 834259003805469684397589 39105890803381391456137)
  ·
    refine ⟨29329418102536043592103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39105890803381391456137 29329418102536043592103)
    ·
      refine ⟨43994127153804065388155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29329418102536043592103 43994127153804065388155)
      ·
        refine ⟨65991190730706098082233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43994127153804065388155 65991190730706098082233)
        ·
          refine ⟨49493393048029573561675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65991190730706098082233 49493393048029573561675)
          ·
            refine ⟨74240089572044360342513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49493393048029573561675 74240089572044360342513)
            ·
              refine ⟨55680067179033270256885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74240089572044360342513 55680067179033270256885)
              ·
                refine ⟨5220006298034369086583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55680067179033270256885 5220006298034369086583)
                ·
                  rfl

theorem cell20_34310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_34310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34310 prefixEnd_34310 := by exact prefixLift 34310
  have htrace : WordTrace (prefixWord ++ tailWord_34310) baseStart_34310 baseEnd_34310 := by
    simpa [prefixWord, tailWord_34310, baseEnd_34310] using wordTrace_append hprefix tailTrace_34310
  have hstable : (prefixWord ++ tailWord_34310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34310).length < 2 ^ (prefixWord ++ tailWord_34310).sum := by decide
  have hdescent : baseEnd_34310 < baseStart_34310 := by decide
  rcases family_descends (prefixWord ++ tailWord_34310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34317 : List Nat := [1, 7, 1, 1, 2, 1, 1, 3, 3]
def baseStart_34317 : Nat := 118140960795 + 34317 * 2 ^ 59
def prefixEnd_34317 : Nat := 4983230072969 + 3 ^ 40 * 34317 * 2
def baseEnd_34317 : Nat := 15663213884842194026387

theorem tailTrace_34317 : CollatzResearch.WordTrace tailWord_34317 prefixEnd_34317 15663213884842194026387 := by
  unfold tailWord_34317
  simp only [CollatzResearch.WordTrace]
  refine ⟨1251643816682844722101205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 834429211121896481400803 1251643816682844722101205)
  ·
    refine ⟨29335401953504173174247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 1251643816682844722101205 29335401953504173174247)
    ·
      refine ⟨44003102930256259761371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29335401953504173174247 44003102930256259761371)
      ·
        refine ⟨66004654395384389642057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44003102930256259761371 66004654395384389642057)
        ·
          refine ⟨49503490796538292231543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66004654395384389642057 49503490796538292231543)
          ·
            refine ⟨74255236194807438347315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49503490796538292231543 74255236194807438347315)
            ·
              refine ⟨111382854292211157520973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74255236194807438347315 111382854292211157520973)
              ·
                refine ⟨41768570359579184070365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111382854292211157520973 41768570359579184070365)
                ·
                  refine ⟨15663213884842194026387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41768570359579184070365 15663213884842194026387)
                  ·
                    rfl

theorem cell20_34317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_34317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34317 prefixEnd_34317 := by exact prefixLift 34317
  have htrace : WordTrace (prefixWord ++ tailWord_34317) baseStart_34317 baseEnd_34317 := by
    simpa [prefixWord, tailWord_34317, baseEnd_34317] using wordTrace_append hprefix tailTrace_34317
  have hstable : (prefixWord ++ tailWord_34317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34317).length < 2 ^ (prefixWord ++ tailWord_34317).sum := by decide
  have hdescent : baseEnd_34317 < baseStart_34317 := by decide
  rcases family_descends (prefixWord ++ tailWord_34317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34356 : List Nat := [2, 5, 1, 12]
def baseStart_34356 : Nat := 118140960795 + 34356 * 2 ^ 59
def prefixEnd_34356 : Nat := 4983230072969 + 3 ^ 40 * 34356 * 2
def baseEnd_34356 : Nat := 64530924063915192289

theorem tailTrace_34356 : CollatzResearch.WordTrace tailWord_34356 prefixEnd_34356 64530924063915192289 := by
  unfold tailWord_34356
  simp only [CollatzResearch.WordTrace]
  refine ⟨626533131770777191385461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 835377509027702921847281 626533131770777191385461)
  ·
    refine ⟨58737481103510361692387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 626533131770777191385461 58737481103510361692387)
    ·
      refine ⟨88106221655265542538581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58737481103510361692387 88106221655265542538581)
      ·
        refine ⟨64530924063915192289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 88106221655265542538581 64530924063915192289)
        ·
          rfl

theorem cell20_34356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 12].length) (baseStart_34356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34356 prefixEnd_34356 := by exact prefixLift 34356
  have htrace : WordTrace (prefixWord ++ tailWord_34356) baseStart_34356 baseEnd_34356 := by
    simpa [prefixWord, tailWord_34356, baseEnd_34356] using wordTrace_append hprefix tailTrace_34356
  have hstable : (prefixWord ++ tailWord_34356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34356).length < 2 ^ (prefixWord ++ tailWord_34356).sum := by decide
  have hdescent : baseEnd_34356 < baseStart_34356 := by decide
  rcases family_descends (prefixWord ++ tailWord_34356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34358 : List Nat := [5, 1, 2, 1, 4, 1, 2, 2, 2]
def baseStart_34358 : Nat := 118140960795 + 34358 * 2 ^ 59
def prefixEnd_34358 : Nat := 4983230072969 + 3 ^ 40 * 34358 * 2
def baseEnd_34358 : Nat := 15681927402028273659553

theorem tailTrace_34358 : CollatzResearch.WordTrace tailWord_34358 prefixEnd_34358 15681927402028273659553 := by
  unfold tailWord_34358
  simp only [CollatzResearch.WordTrace]
  refine ⟨78321200595894295271483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 835426139689539149562485 78321200595894295271483)
  ·
    refine ⟨117481800893841442907225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78321200595894295271483 117481800893841442907225)
    ·
      refine ⟨88111350670381082180419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117481800893841442907225 88111350670381082180419)
      ·
        refine ⟨132167026005571623270629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88111350670381082180419 132167026005571623270629)
        ·
          refine ⟨24781317376044679363243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132167026005571623270629 24781317376044679363243)
          ·
            refine ⟨37171976064067019044865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24781317376044679363243 37171976064067019044865)
            ·
              refine ⟨27878982048050264283649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37171976064067019044865 27878982048050264283649)
              ·
                refine ⟨20909236536037698212737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27878982048050264283649 20909236536037698212737)
                ·
                  refine ⟨15681927402028273659553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20909236536037698212737 15681927402028273659553)
                  ·
                    rfl

theorem cell20_34358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_34358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34358 prefixEnd_34358 := by exact prefixLift 34358
  have htrace : WordTrace (prefixWord ++ tailWord_34358) baseStart_34358 baseEnd_34358 := by
    simpa [prefixWord, tailWord_34358, baseEnd_34358] using wordTrace_append hprefix tailTrace_34358
  have hstable : (prefixWord ++ tailWord_34358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34358).length < 2 ^ (prefixWord ++ tailWord_34358).sum := by decide
  have hdescent : baseEnd_34358 < baseStart_34358 := by decide
  rcases family_descends (prefixWord ++ tailWord_34358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34380 : List Nat := [2, 2, 1, 3, 1, 3, 2, 3, 3]
def baseStart_34380 : Nat := 118140960795 + 34380 * 2 ^ 59
def prefixEnd_34380 : Nat := 4983230072969 + 3 ^ 40 * 34380 * 2
def baseEnd_34380 : Nat := 15691968801493974926129

theorem tailTrace_34380 : CollatzResearch.WordTrace tailWord_34380 prefixEnd_34380 15691968801493974926129 := by
  unfold tailWord_34380
  simp only [CollatzResearch.WordTrace]
  refine ⟨626970807727303240822297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 835961076969737654429729 626970807727303240822297)
  ·
    refine ⟨470228105795477430616723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 626970807727303240822297 470228105795477430616723)
    ·
      refine ⟨705342158693216145925085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 470228105795477430616723 705342158693216145925085)
      ·
        refine ⟨264503309509956054721907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 705342158693216145925085 264503309509956054721907)
        ·
          refine ⟨396754964264934082082861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264503309509956054721907 396754964264934082082861)
          ·
            refine ⟨148783111599350280781073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 396754964264934082082861 148783111599350280781073)
            ·
              refine ⟨111587333699512710585805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148783111599350280781073 111587333699512710585805)
              ·
                refine ⟨41845250137317266469677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111587333699512710585805 41845250137317266469677)
                ·
                  refine ⟨15691968801493974926129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41845250137317266469677 15691968801493974926129)
                  ·
                    rfl

theorem cell20_34380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_34380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34380 prefixEnd_34380 := by exact prefixLift 34380
  have htrace : WordTrace (prefixWord ++ tailWord_34380) baseStart_34380 baseEnd_34380 := by
    simpa [prefixWord, tailWord_34380, baseEnd_34380] using wordTrace_append hprefix tailTrace_34380
  have hstable : (prefixWord ++ tailWord_34380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34380).length < 2 ^ (prefixWord ++ tailWord_34380).sum := by decide
  have hdescent : baseEnd_34380 < baseStart_34380 := by decide
  rcases family_descends (prefixWord ++ tailWord_34380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34401 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 5]
def baseStart_34401 : Nat := 118140960795 + 34401 * 2 ^ 59
def prefixEnd_34401 : Nat := 4983230072969 + 3 ^ 40 * 34401 * 2
def baseEnd_34401 : Nat := 15701553773711235226043

theorem tailTrace_34401 : CollatzResearch.WordTrace tailWord_34401 prefixEnd_34401 15701553773711235226043 := by
  unfold tailWord_34401
  simp only [CollatzResearch.WordTrace]
  refine ⟨1254707548378527068159057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 836471698919018045439371 1254707548378527068159057)
  ·
    refine ⟨941030661283895301119293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1254707548378527068159057 941030661283895301119293)
    ·
      refine ⟨352886497981460737919735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 941030661283895301119293 352886497981460737919735)
      ·
        refine ⟨529329746972191106879603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352886497981460737919735 529329746972191106879603)
        ·
          refine ⟨793994620458286660319405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529329746972191106879603 793994620458286660319405)
          ·
            refine ⟨297747982671857497619777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 793994620458286660319405 297747982671857497619777)
            ·
              refine ⟨223310987003893123214833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297747982671857497619777 223310987003893123214833)
              ·
                refine ⟨167483240252919842411125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223310987003893123214833 167483240252919842411125)
                ·
                  refine ⟨15701553773711235226043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 167483240252919842411125 15701553773711235226043)
                  ·
                    rfl

theorem cell20_34401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_34401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34401 prefixEnd_34401 := by exact prefixLift 34401
  have htrace : WordTrace (prefixWord ++ tailWord_34401) baseStart_34401 baseEnd_34401 := by
    simpa [prefixWord, tailWord_34401, baseEnd_34401] using wordTrace_append hprefix tailTrace_34401
  have hstable : (prefixWord ++ tailWord_34401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34401).length < 2 ^ (prefixWord ++ tailWord_34401).sum := by decide
  have hdescent : baseEnd_34401 < baseStart_34401 := by decide
  rcases family_descends (prefixWord ++ tailWord_34401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34404 : List Nat := [2, 3, 1, 1, 2, 3, 1, 5, 2]
def baseStart_34404 : Nat := 118140960795 + 34404 * 2 ^ 59
def prefixEnd_34404 : Nat := 4983230072969 + 3 ^ 40 * 34404 * 2
def baseEnd_34404 : Nat := 15702923055456558126031

theorem tailTrace_34404 : CollatzResearch.WordTrace tailWord_34404 prefixEnd_34404 15702923055456558126031 := by
  unfold tailWord_34404
  simp only [CollatzResearch.WordTrace]
  refine ⟨627408483683829290259133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 836544644911772387012177 627408483683829290259133)
  ·
    refine ⟨235278181381435983847175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 627408483683829290259133 235278181381435983847175)
    ·
      refine ⟨352917272072153975770763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235278181381435983847175 352917272072153975770763)
      ·
        refine ⟨529375908108230963656145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352917272072153975770763 529375908108230963656145)
        ·
          refine ⟨397031931081173222742109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 529375908108230963656145 397031931081173222742109)
          ·
            refine ⟨148886974155439958528291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 397031931081173222742109 148886974155439958528291)
            ·
              refine ⟨223330461233159937792437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148886974155439958528291 223330461233159937792437)
              ·
                refine ⟨20937230740608744168041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 223330461233159937792437 20937230740608744168041)
                ·
                  refine ⟨15702923055456558126031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20937230740608744168041 15702923055456558126031)
                  ·
                    rfl

theorem cell20_34404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_34404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34404 prefixEnd_34404 := by exact prefixLift 34404
  have htrace : WordTrace (prefixWord ++ tailWord_34404) baseStart_34404 baseEnd_34404 := by
    simpa [prefixWord, tailWord_34404, baseEnd_34404] using wordTrace_append hprefix tailTrace_34404
  have hstable : (prefixWord ++ tailWord_34404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34404).length < 2 ^ (prefixWord ++ tailWord_34404).sum := by decide
  have hdescent : baseEnd_34404 < baseStart_34404 := by decide
  rcases family_descends (prefixWord ++ tailWord_34404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34414 : List Nat := [4, 1, 2, 2, 3, 2, 1, 2, 3]
def baseStart_34414 : Nat := 118140960795 + 34414 * 2 ^ 59
def prefixEnd_34414 : Nat := 4983230072969 + 3 ^ 40 * 34414 * 2
def baseEnd_34414 : Nat := 15707487327940967792657

theorem tailTrace_34414 : CollatzResearch.WordTrace tailWord_34414 prefixEnd_34414 15707487327940967792657 := by
  unfold tailWord_34414
  simp only [CollatzResearch.WordTrace]
  refine ⟨156897712166428786047787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 836787798220953525588197 156897712166428786047787)
  ·
    refine ⟨235346568249643179071681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156897712166428786047787 235346568249643179071681)
    ·
      refine ⟨176509926187232384303761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235346568249643179071681 176509926187232384303761)
      ·
        refine ⟨132382444640424288227821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176509926187232384303761 132382444640424288227821)
        ·
          refine ⟨49643416740159108085433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132382444640424288227821 49643416740159108085433)
          ·
            refine ⟨37232562555119331064075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49643416740159108085433 37232562555119331064075)
            ·
              refine ⟨55848843832678996596113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37232562555119331064075 55848843832678996596113)
              ·
                refine ⟨41886632874509247447085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55848843832678996596113 41886632874509247447085)
                ·
                  refine ⟨15707487327940967792657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41886632874509247447085 15707487327940967792657)
                  ·
                    rfl

theorem cell20_34414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_34414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34414 prefixEnd_34414 := by exact prefixLift 34414
  have htrace : WordTrace (prefixWord ++ tailWord_34414) baseStart_34414 baseEnd_34414 := by
    simpa [prefixWord, tailWord_34414, baseEnd_34414] using wordTrace_append hprefix tailTrace_34414
  have hstable : (prefixWord ++ tailWord_34414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34414).length < 2 ^ (prefixWord ++ tailWord_34414).sum := by decide
  have hdescent : baseEnd_34414 < baseStart_34414 := by decide
  rcases family_descends (prefixWord ++ tailWord_34414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34418 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 5]
def baseStart_34418 : Nat := 118140960795 + 34418 * 2 ^ 59
def prefixEnd_34418 : Nat := 4983230072969 + 3 ^ 40 * 34418 * 2
def baseEnd_34418 : Nat := 15709313036934731659307

theorem tailTrace_34418 : CollatzResearch.WordTrace tailWord_34418 prefixEnd_34418 15709313036934731659307 := by
  unfold tailWord_34418
  simp only [CollatzResearch.WordTrace]
  refine ⟨313831897329234742881977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 836885059544625981018605 313831897329234742881977)
  ·
    refine ⟨235373922996926057161483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 313831897329234742881977 235373922996926057161483)
    ·
      refine ⟨353060884495389085742225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235373922996926057161483 353060884495389085742225)
      ·
        refine ⟨264795663371541814306669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 353060884495389085742225 264795663371541814306669)
        ·
          refine ⟨99298373764328180365001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 264795663371541814306669 99298373764328180365001)
          ·
            refine ⟨74473780323246135273751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99298373764328180365001 74473780323246135273751)
            ·
              refine ⟨111710670484869202910627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74473780323246135273751 111710670484869202910627)
              ·
                refine ⟨167566005727303804365941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111710670484869202910627 167566005727303804365941)
                ·
                  refine ⟨15709313036934731659307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 167566005727303804365941 15709313036934731659307)
                  ·
                    rfl

theorem cell20_34418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_34418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34418 prefixEnd_34418 := by exact prefixLift 34418
  have htrace : WordTrace (prefixWord ++ tailWord_34418) baseStart_34418 baseEnd_34418 := by
    simpa [prefixWord, tailWord_34418, baseEnd_34418] using wordTrace_append hprefix tailTrace_34418
  have hstable : (prefixWord ++ tailWord_34418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34418).length < 2 ^ (prefixWord ++ tailWord_34418).sum := by decide
  have hdescent : baseEnd_34418 < baseStart_34418 := by decide
  rcases family_descends (prefixWord ++ tailWord_34418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34421 : List Nat := [1, 3, 4, 2, 1, 1, 2, 4, 2]
def baseStart_34421 : Nat := 118140960795 + 34421 * 2 ^ 59
def prefixEnd_34421 : Nat := 4983230072969 + 3 ^ 40 * 34421 * 2
def baseEnd_34421 : Nat := 15710682318680054559295

theorem tailTrace_34421 : CollatzResearch.WordTrace tailWord_34421 prefixEnd_34421 15710682318680054559295 := by
  unfold tailWord_34421
  simp only [CollatzResearch.WordTrace]
  refine ⟨1255437008306070483887117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 836958005537380322591411 1255437008306070483887117)
  ·
    refine ⟨470788878114776431457669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1255437008306070483887117 470788878114776431457669)
    ·
      refine ⟨88272914646520580898313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 470788878114776431457669 88272914646520580898313)
      ·
        refine ⟨66204685984890435673735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88272914646520580898313 66204685984890435673735)
        ·
          refine ⟨99307028977335653510603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66204685984890435673735 99307028977335653510603)
          ·
            refine ⟨148960543466003480265905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99307028977335653510603 148960543466003480265905)
            ·
              refine ⟨111720407599502610199429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148960543466003480265905 111720407599502610199429)
              ·
                refine ⟨20947576424906739412393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111720407599502610199429 20947576424906739412393)
                ·
                  refine ⟨15710682318680054559295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20947576424906739412393 15710682318680054559295)
                  ·
                    rfl

theorem cell20_34421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 2].length) (baseStart_34421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34421 prefixEnd_34421 := by exact prefixLift 34421
  have htrace : WordTrace (prefixWord ++ tailWord_34421) baseStart_34421 baseEnd_34421 := by
    simpa [prefixWord, tailWord_34421, baseEnd_34421] using wordTrace_append hprefix tailTrace_34421
  have hstable : (prefixWord ++ tailWord_34421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34421).length < 2 ^ (prefixWord ++ tailWord_34421).sum := by decide
  have hdescent : baseEnd_34421 < baseStart_34421 := by decide
  rcases family_descends (prefixWord ++ tailWord_34421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34425 : List Nat := [1, 2, 1, 3, 3, 1, 4, 1, 4]
def baseStart_34425 : Nat := 118140960795 + 34425 * 2 ^ 59
def prefixEnd_34425 : Nat := 4983230072969 + 3 ^ 40 * 34425 * 2
def baseEnd_34425 : Nat := 15712508027673818425945

theorem tailTrace_34425 : CollatzResearch.WordTrace tailWord_34425 prefixEnd_34425 15712508027673818425945 := by
  unfold tailWord_34425
  simp only [CollatzResearch.WordTrace]
  refine ⟨1255582900291579167032729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 837055266861052778021819 1255582900291579167032729)
  ·
    refine ⟨941687175218684375274547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1255582900291579167032729 941687175218684375274547)
    ·
      refine ⟨1412530762828026562911821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 941687175218684375274547 1412530762828026562911821)
      ·
        refine ⟨529699036060509961091933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1412530762828026562911821 529699036060509961091933)
        ·
          refine ⟨198637138522691235409475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 529699036060509961091933 198637138522691235409475)
          ·
            refine ⟨297955707784036853114213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198637138522691235409475 297955707784036853114213)
            ·
              refine ⟨55866695209506909958915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 297955707784036853114213 55866695209506909958915)
              ·
                refine ⟨83800042814260364938373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55866695209506909958915 83800042814260364938373)
                ·
                  refine ⟨15712508027673818425945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83800042814260364938373 15712508027673818425945)
                  ·
                    rfl

theorem cell20_34425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_34425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34425 prefixEnd_34425 := by exact prefixLift 34425
  have htrace : WordTrace (prefixWord ++ tailWord_34425) baseStart_34425 baseEnd_34425 := by
    simpa [prefixWord, tailWord_34425, baseEnd_34425] using wordTrace_append hprefix tailTrace_34425
  have hstable : (prefixWord ++ tailWord_34425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34425).length < 2 ^ (prefixWord ++ tailWord_34425).sum := by decide
  have hdescent : baseEnd_34425 < baseStart_34425 := by decide
  rcases family_descends (prefixWord ++ tailWord_34425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34466 : List Nat := [3, 3, 1, 4, 1, 2, 6]
def baseStart_34466 : Nat := 118140960795 + 34466 * 2 ^ 59
def prefixEnd_34466 : Nat := 4983230072969 + 3 ^ 40 * 34466 * 2
def baseEnd_34466 : Nat := 1747913504984433117679

theorem tailTrace_34466 : CollatzResearch.WordTrace tailWord_34466 prefixEnd_34466 1747913504984433117679 := by
  unfold tailWord_34466
  simp only [CollatzResearch.WordTrace]
  refine ⟨314269573285760792318813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 838052195428695446183501 314269573285760792318813)
  ·
    refine ⟨117851089982160297119555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 314269573285760792318813 117851089982160297119555)
    ·
      refine ⟨176776634973240445679333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117851089982160297119555 176776634973240445679333)
      ·
        refine ⟨33145619057482583564875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176776634973240445679333 33145619057482583564875)
        ·
          refine ⟨49718428586223875347313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33145619057482583564875 49718428586223875347313)
          ·
            refine ⟨37288821439667906510485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49718428586223875347313 37288821439667906510485)
            ·
              refine ⟨1747913504984433117679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37288821439667906510485 1747913504984433117679)
              ·
                rfl

theorem cell20_34466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 6].length) (baseStart_34466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34466 prefixEnd_34466 := by exact prefixLift 34466
  have htrace : WordTrace (prefixWord ++ tailWord_34466) baseStart_34466 baseEnd_34466 := by
    simpa [prefixWord, tailWord_34466, baseEnd_34466] using wordTrace_append hprefix tailTrace_34466
  have hstable : (prefixWord ++ tailWord_34466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34466).length < 2 ^ (prefixWord ++ tailWord_34466).sum := by decide
  have hdescent : baseEnd_34466 < baseStart_34466 := by decide
  rcases family_descends (prefixWord ++ tailWord_34466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34472 : List Nat := [2, 1, 7, 1, 1, 1, 3, 2, 2]
def baseStart_34472 : Nat := 118140960795 + 34472 * 2 ^ 59
def prefixEnd_34472 : Nat := 4983230072969 + 3 ^ 40 * 34472 * 2
def baseEnd_34472 : Nat := 15733960108350543859087

theorem tailTrace_34472 : CollatzResearch.WordTrace tailWord_34472 prefixEnd_34472 15733960108350543859087 := by
  unfold tailWord_34472
  simp only [CollatzResearch.WordTrace]
  refine ⟨628648565560653096996835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 838198087414204129329113 628648565560653096996835)
  ·
    refine ⟨942972848340979645495253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 628648565560653096996835 942972848340979645495253)
    ·
      refine ⟨22100926132991710441295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 942972848340979645495253 22100926132991710441295)
      ·
        refine ⟨33151389199487565661943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22100926132991710441295 33151389199487565661943)
        ·
          refine ⟨49727083799231348492915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33151389199487565661943 49727083799231348492915)
          ·
            refine ⟨74590625698847022739373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49727083799231348492915 74590625698847022739373)
            ·
              refine ⟨27971484637067633527265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74590625698847022739373 27971484637067633527265)
              ·
                refine ⟨20978613477800725145449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27971484637067633527265 20978613477800725145449)
                ·
                  refine ⟨15733960108350543859087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20978613477800725145449 15733960108350543859087)
                  ·
                    rfl

theorem cell20_34472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 2].length) (baseStart_34472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34472 prefixEnd_34472 := by exact prefixLift 34472
  have htrace : WordTrace (prefixWord ++ tailWord_34472) baseStart_34472 baseEnd_34472 := by
    simpa [prefixWord, tailWord_34472, baseEnd_34472] using wordTrace_append hprefix tailTrace_34472
  have hstable : (prefixWord ++ tailWord_34472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34472).length < 2 ^ (prefixWord ++ tailWord_34472).sum := by decide
  have hdescent : baseEnd_34472 < baseStart_34472 := by decide
  rcases family_descends (prefixWord ++ tailWord_34472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34525 : List Nat := [1, 4, 3, 3, 1, 8]
def baseStart_34525 : Nat := 118140960795 + 34525 * 2 ^ 59
def prefixEnd_34525 : Nat := 4983230072969 + 3 ^ 40 * 34525 * 2
def baseEnd_34525 : Nat := 583635213056219077489

theorem tailTrace_34525 : CollatzResearch.WordTrace tailWord_34525 prefixEnd_34525 583635213056219077489 := by
  unfold tailWord_34525
  simp only [CollatzResearch.WordTrace]
  refine ⟨1259230199929296245673029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 839486799952864163782019 1259230199929296245673029)
  ·
    refine ⟨236105662486743046063693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1259230199929296245673029 236105662486743046063693)
    ·
      refine ⟨88539623432528642273885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236105662486743046063693 88539623432528642273885)
      ·
        refine ⟨33202358787198240852707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88539623432528642273885 33202358787198240852707)
        ·
          refine ⟨49803538180797361279061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33202358787198240852707 49803538180797361279061)
          ·
            refine ⟨583635213056219077489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 49803538180797361279061 583635213056219077489)
            ·
              rfl

theorem cell20_34525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 8].length) (baseStart_34525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34525 prefixEnd_34525 := by exact prefixLift 34525
  have htrace : WordTrace (prefixWord ++ tailWord_34525) baseStart_34525 baseEnd_34525 := by
    simpa [prefixWord, tailWord_34525, baseEnd_34525] using wordTrace_append hprefix tailTrace_34525
  have hstable : (prefixWord ++ tailWord_34525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34525).length < 2 ^ (prefixWord ++ tailWord_34525).sum := by decide
  have hdescent : baseEnd_34525 < baseStart_34525 := by decide
  rcases family_descends (prefixWord ++ tailWord_34525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34529 : List Nat := [1, 2, 3, 1, 13]
def baseStart_34529 : Nat := 118140960795 + 34529 * 2 ^ 59
def prefixEnd_34529 : Nat := 4983230072969 + 3 ^ 40 * 34529 * 2
def baseEnd_34529 : Nat := 194567610635946653813

theorem tailTrace_34529 : CollatzResearch.WordTrace tailWord_34529 prefixEnd_34529 194567610635946653813 := by
  unfold tailWord_34529
  simp only [CollatzResearch.WordTrace]
  refine ⟨1259376091914804928818641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 839584061276536619212427 1259376091914804928818641)
  ·
    refine ⟨944532068936103696613981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1259376091914804928818641 944532068936103696613981)
    ·
      refine ⟨354199525851038886230243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 944532068936103696613981 354199525851038886230243)
      ·
        refine ⟨531299288776558329345365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354199525851038886230243 531299288776558329345365)
        ·
          refine ⟨194567610635946653813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 531299288776558329345365 194567610635946653813)
          ·
            rfl

theorem cell20_34529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 13].length) (baseStart_34529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34529 prefixEnd_34529 := by exact prefixLift 34529
  have htrace : WordTrace (prefixWord ++ tailWord_34529) baseStart_34529 baseEnd_34529 := by
    simpa [prefixWord, tailWord_34529, baseEnd_34529] using wordTrace_append hprefix tailTrace_34529
  have hstable : (prefixWord ++ tailWord_34529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34529).length < 2 ^ (prefixWord ++ tailWord_34529).sum := by decide
  have hdescent : baseEnd_34529 < baseStart_34529 := by decide
  rcases family_descends (prefixWord ++ tailWord_34529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34531 : List Nat := [1, 1, 1, 7, 3, 1, 2, 2, 2]
def baseStart_34531 : Nat := 118140960795 + 34531 * 2 ^ 59
def prefixEnd_34531 : Nat := 4983230072969 + 3 ^ 40 * 34531 * 2
def baseEnd_34531 : Nat := 15760889316008560892179

theorem tailTrace_34531 : CollatzResearch.WordTrace tailWord_34531 prefixEnd_34531 15760889316008560892179 := by
  unfold tailWord_34531
  simp only [CollatzResearch.WordTrace]
  refine ⟨1259449037907559270391447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 839632691938372846927631 1259449037907559270391447)
  ·
    refine ⟨1889173556861338905587171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1259449037907559270391447 1889173556861338905587171)
    ·
      refine ⟨2833760335292008358380757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1889173556861338905587171 2833760335292008358380757)
      ·
        refine ⟨66416257858406445899549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 2833760335292008358380757 66416257858406445899549)
        ·
          refine ⟨24906096696902417212331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66416257858406445899549 24906096696902417212331)
          ·
            refine ⟨37359145045353625818497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24906096696902417212331 37359145045353625818497)
            ·
              refine ⟨28019358784015219363873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37359145045353625818497 28019358784015219363873)
              ·
                refine ⟨21014519088011414522905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28019358784015219363873 21014519088011414522905)
                ·
                  refine ⟨15760889316008560892179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21014519088011414522905 15760889316008560892179)
                  ·
                    rfl

theorem cell20_34531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 2].length) (baseStart_34531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34531 prefixEnd_34531 := by exact prefixLift 34531
  have htrace : WordTrace (prefixWord ++ tailWord_34531) baseStart_34531 baseEnd_34531 := by
    simpa [prefixWord, tailWord_34531, baseEnd_34531] using wordTrace_append hprefix tailTrace_34531
  have hstable : (prefixWord ++ tailWord_34531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34531).length < 2 ^ (prefixWord ++ tailWord_34531).sum := by decide
  have hdescent : baseEnd_34531 < baseStart_34531 := by decide
  rcases family_descends (prefixWord ++ tailWord_34531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34532 : List Nat := [2, 3, 1, 1, 1, 3, 4, 2, 3]
def baseStart_34532 : Nat := 118140960795 + 34532 * 2 ^ 59
def prefixEnd_34532 : Nat := 4983230072969 + 3 ^ 40 * 34532 * 2
def baseEnd_34532 : Nat := 15761345743257001858841

theorem tailTrace_34532 : CollatzResearch.WordTrace tailWord_34532 prefixEnd_34532 15761345743257001858841 := by
  unfold tailWord_34532
  simp only [CollatzResearch.WordTrace]
  refine ⟨629742755451968220588925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 839657007269290960785233 629742755451968220588925)
  ·
    refine ⟨236153533294488082720847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 629742755451968220588925 236153533294488082720847)
    ·
      refine ⟨354230299941732124081271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236153533294488082720847 354230299941732124081271)
      ·
        refine ⟨531345449912598186121907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354230299941732124081271 531345449912598186121907)
        ·
          refine ⟨797018174868897279182861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 531345449912598186121907 797018174868897279182861)
          ·
            refine ⟨298881815575836479693573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 797018174868897279182861 298881815575836479693573)
            ·
              refine ⟨56040340420469339942545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 298881815575836479693573 56040340420469339942545)
              ·
                refine ⟨42030255315352004956909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56040340420469339942545 42030255315352004956909)
                ·
                  refine ⟨15761345743257001858841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42030255315352004956909 15761345743257001858841)
                  ·
                    rfl

theorem cell20_34532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_34532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34532 prefixEnd_34532 := by exact prefixLift 34532
  have htrace : WordTrace (prefixWord ++ tailWord_34532) baseStart_34532 baseEnd_34532 := by
    simpa [prefixWord, tailWord_34532, baseEnd_34532] using wordTrace_append hprefix tailTrace_34532
  have hstable : (prefixWord ++ tailWord_34532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34532).length < 2 ^ (prefixWord ++ tailWord_34532).sum := by decide
  have hdescent : baseEnd_34532 < baseStart_34532 := by decide
  rcases family_descends (prefixWord ++ tailWord_34532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34560 : List Nat := [2, 1, 1, 2, 1, 1, 2, 6, 4]
def baseStart_34560 : Nat := 118140960795 + 34560 * 2 ^ 59
def prefixEnd_34560 : Nat := 4983230072969 + 3 ^ 40 * 34560 * 2
def baseEnd_34560 : Nat := 15774125706213348925393

theorem tailTrace_34560 : CollatzResearch.WordTrace tailWord_34560 prefixEnd_34560 15774125706213348925393 := by
  unfold tailWord_34560
  simp only [CollatzResearch.WordTrace]
  refine ⟨630253377401248611598567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 840337836534998148798089 630253377401248611598567)
  ·
    refine ⟨945380066101872917397851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 630253377401248611598567 945380066101872917397851)
    ·
      refine ⟨1418070099152809376096777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 945380066101872917397851 1418070099152809376096777)
      ·
        refine ⟨1063552574364607032072583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1418070099152809376096777 1063552574364607032072583)
        ·
          refine ⟨1595328861546910548108875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1063552574364607032072583 1595328861546910548108875)
          ·
            refine ⟨2392993292320365822163313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1595328861546910548108875 2392993292320365822163313)
            ·
              refine ⟨1794744969240274366622485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2392993292320365822163313 1794744969240274366622485)
              ·
                refine ⟨84128670433137860935429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1794744969240274366622485 84128670433137860935429)
                ·
                  refine ⟨15774125706213348925393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84128670433137860935429 15774125706213348925393)
                  ·
                    rfl

theorem cell20_34560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_34560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34560 prefixEnd_34560 := by exact prefixLift 34560
  have htrace : WordTrace (prefixWord ++ tailWord_34560) baseStart_34560 baseEnd_34560 := by
    simpa [prefixWord, tailWord_34560, baseEnd_34560] using wordTrace_append hprefix tailTrace_34560
  have hstable : (prefixWord ++ tailWord_34560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34560).length < 2 ^ (prefixWord ++ tailWord_34560).sum := by decide
  have hdescent : baseEnd_34560 < baseStart_34560 := by decide
  rcases family_descends (prefixWord ++ tailWord_34560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34590 : List Nat := [4, 3, 2, 2, 1, 1, 2, 1, 4]
def baseStart_34590 : Nat := 118140960795 + 34590 * 2 ^ 59
def prefixEnd_34590 : Nat := 4983230072969 + 3 ^ 40 * 34590 * 2
def baseEnd_34590 : Nat := 15787818523666577925271

theorem tailTrace_34590 : CollatzResearch.WordTrace tailWord_34590 prefixEnd_34590 15787818523666577925271 := by
  unfold tailWord_34590
  simp only [CollatzResearch.WordTrace]
  refine ⟨157700118086726543348653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 841067296462541564526149 157700118086726543348653)
  ·
    refine ⟨59137544282522453755745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157700118086726543348653 59137544282522453755745)
    ·
      refine ⟨44353158211891840316809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59137544282522453755745 44353158211891840316809)
      ·
        refine ⟨33264868658918880237607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44353158211891840316809 33264868658918880237607)
        ·
          refine ⟨49897302988378320356411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33264868658918880237607 49897302988378320356411)
          ·
            refine ⟨74845954482567480534617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49897302988378320356411 74845954482567480534617)
            ·
              refine ⟨56134465861925610400963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74845954482567480534617 56134465861925610400963)
              ·
                refine ⟨84201698792888415601445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56134465861925610400963 84201698792888415601445)
                ·
                  refine ⟨15787818523666577925271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84201698792888415601445 15787818523666577925271)
                  ·
                    rfl

theorem cell20_34590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_34590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34590 prefixEnd_34590 := by exact prefixLift 34590
  have htrace : WordTrace (prefixWord ++ tailWord_34590) baseStart_34590 baseEnd_34590 := by
    simpa [prefixWord, tailWord_34590, baseEnd_34590] using wordTrace_append hprefix tailTrace_34590
  have hstable : (prefixWord ++ tailWord_34590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34590).length < 2 ^ (prefixWord ++ tailWord_34590).sum := by decide
  have hdescent : baseEnd_34590 < baseStart_34590 := by decide
  rcases family_descends (prefixWord ++ tailWord_34590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34591 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 5]
def baseStart_34591 : Nat := 118140960795 + 34591 * 2 ^ 59
def prefixEnd_34591 : Nat := 4983230072969 + 3 ^ 40 * 34591 * 2
def baseEnd_34591 : Nat := 15788274950915018891933

theorem tailTrace_34591 : CollatzResearch.WordTrace tailWord_34591 prefixEnd_34591 15788274950915018891933 := by
  unfold tailWord_34591
  simp only [CollatzResearch.WordTrace]
  refine ⟨1261637417690189517575627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 841091611793459678383751 1261637417690189517575627)
  ·
    refine ⟨1892456126535284276363441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1261637417690189517575627 1892456126535284276363441)
    ·
      refine ⟨1419342094901463207272581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1892456126535284276363441 1419342094901463207272581)
      ·
        refine ⟨266126642794024351363609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1419342094901463207272581 266126642794024351363609)
        ·
          refine ⟨199594982095518263522707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266126642794024351363609 199594982095518263522707)
          ·
            refine ⟨299392473143277395284061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199594982095518263522707 299392473143277395284061)
            ·
              refine ⟨112272177428729023231523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 299392473143277395284061 112272177428729023231523)
              ·
                refine ⟨168408266143093534847285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112272177428729023231523 168408266143093534847285)
                ·
                  refine ⟨15788274950915018891933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 168408266143093534847285 15788274950915018891933)
                  ·
                    rfl

theorem cell20_34591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 5].length) (baseStart_34591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34591 prefixEnd_34591 := by exact prefixLift 34591
  have htrace : WordTrace (prefixWord ++ tailWord_34591) baseStart_34591 baseEnd_34591 := by
    simpa [prefixWord, tailWord_34591, baseEnd_34591] using wordTrace_append hprefix tailTrace_34591
  have hstable : (prefixWord ++ tailWord_34591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34591).length < 2 ^ (prefixWord ++ tailWord_34591).sum := by decide
  have hdescent : baseEnd_34591 < baseStart_34591 := by decide
  rcases family_descends (prefixWord ++ tailWord_34591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34594 : List Nat := [3, 3, 1, 1, 2, 1, 1, 6, 2]
def baseStart_34594 : Nat := 118140960795 + 34594 * 2 ^ 59
def prefixEnd_34594 : Nat := 4983230072969 + 3 ^ 40 * 34594 * 2
def baseEnd_34594 : Nat := 15789644232660341791921

theorem tailTrace_34594 : CollatzResearch.WordTrace tailWord_34594 prefixEnd_34594 15789644232660341791921 := by
  unfold tailWord_34594
  simp only [CollatzResearch.WordTrace]
  refine ⟨315436709169830257483709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 841164557786214019956557 315436709169830257483709)
  ·
    refine ⟨118288765938686346556391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 315436709169830257483709 118288765938686346556391)
    ·
      refine ⟨177433148908029519834587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118288765938686346556391 177433148908029519834587)
      ·
        refine ⟨266149723362044279751881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177433148908029519834587 266149723362044279751881)
        ·
          refine ⟨199612292521533209813911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266149723362044279751881 199612292521533209813911)
          ·
            refine ⟨299418438782299814720867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199612292521533209813911 299418438782299814720867)
            ·
              refine ⟨449127658173449722081301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299418438782299814720867 449127658173449722081301)
              ·
                refine ⟨21052858976880455722561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 449127658173449722081301 21052858976880455722561)
                ·
                  refine ⟨15789644232660341791921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21052858976880455722561 15789644232660341791921)
                  ·
                    rfl

theorem cell20_34594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_34594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34594 prefixEnd_34594 := by exact prefixLift 34594
  have htrace : WordTrace (prefixWord ++ tailWord_34594) baseStart_34594 baseEnd_34594 := by
    simpa [prefixWord, tailWord_34594, baseEnd_34594] using wordTrace_append hprefix tailTrace_34594
  have hstable : (prefixWord ++ tailWord_34594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34594).length < 2 ^ (prefixWord ++ tailWord_34594).sum := by decide
  have hdescent : baseEnd_34594 < baseStart_34594 := by decide
  rcases family_descends (prefixWord ++ tailWord_34594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34632 : List Nat := [2, 1, 3, 1, 1, 4, 3, 3, 2]
def baseStart_34632 : Nat := 118140960795 + 34632 * 2 ^ 59
def prefixEnd_34632 : Nat := 4983230072969 + 3 ^ 40 * 34632 * 2
def baseEnd_34632 : Nat := 15806988468101098525099

theorem tailTrace_34632 : CollatzResearch.WordTrace tailWord_34632 prefixEnd_34632 15806988468101098525099 := by
  unfold tailWord_34632
  simp only [CollatzResearch.WordTrace]
  refine ⟨631566405270826759909075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 842088540361102346545433 631566405270826759909075)
  ·
    refine ⟨947349607906240139863613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 631566405270826759909075 947349607906240139863613)
    ·
      refine ⟨355256102964840052448855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 947349607906240139863613 355256102964840052448855)
      ·
        refine ⟨532884154447260078673283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355256102964840052448855 532884154447260078673283)
        ·
          refine ⟨799326231670890118009925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532884154447260078673283 799326231670890118009925)
          ·
            refine ⟨149873668438291897126861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 799326231670890118009925 149873668438291897126861)
            ·
              refine ⟨56202625664359461422573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149873668438291897126861 56202625664359461422573)
              ·
                refine ⟨21075984624134798033465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56202625664359461422573 21075984624134798033465)
                ·
                  refine ⟨15806988468101098525099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21075984624134798033465 15806988468101098525099)
                  ·
                    rfl

theorem cell20_34632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 2].length) (baseStart_34632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34632 prefixEnd_34632 := by exact prefixLift 34632
  have htrace : WordTrace (prefixWord ++ tailWord_34632) baseStart_34632 baseEnd_34632 := by
    simpa [prefixWord, tailWord_34632, baseEnd_34632] using wordTrace_append hprefix tailTrace_34632
  have hstable : (prefixWord ++ tailWord_34632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34632).length < 2 ^ (prefixWord ++ tailWord_34632).sum := by decide
  have hdescent : baseEnd_34632 < baseStart_34632 := by decide
  rcases family_descends (prefixWord ++ tailWord_34632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34674 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 6]
def baseStart_34674 : Nat := 118140960795 + 34674 * 2 ^ 59
def prefixEnd_34674 : Nat := 4983230072969 + 3 ^ 40 * 34674 * 2
def baseEnd_34674 : Nat := 15826158412535619124927

theorem tailTrace_34674 : CollatzResearch.WordTrace tailWord_34674 prefixEnd_34674 15826158412535619124927 := by
  unfold tailWord_34674
  simp only [CollatzResearch.WordTrace]
  refine ⟨316166169097373673211769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 843109784259663128564717 316166169097373673211769)
  ·
    refine ⟨237124626823030254908827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 316166169097373673211769 237124626823030254908827)
    ·
      refine ⟨355686940234545382363241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237124626823030254908827 355686940234545382363241)
      ·
        refine ⟨266765205175909036772431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 355686940234545382363241 266765205175909036772431)
        ·
          refine ⟨400147807763863555158647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266765205175909036772431 400147807763863555158647)
          ·
            refine ⟨600221711645795332737971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400147807763863555158647 600221711645795332737971)
            ·
              refine ⟨900332567468692999106957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 600221711645795332737971 900332567468692999106957)
              ·
                refine ⟨337624712800759874665109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 900332567468692999106957 337624712800759874665109)
                ·
                  refine ⟨15826158412535619124927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 337624712800759874665109 15826158412535619124927)
                  ·
                    rfl

theorem cell20_34674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_34674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34674 prefixEnd_34674 := by exact prefixLift 34674
  have htrace : WordTrace (prefixWord ++ tailWord_34674) baseStart_34674 baseEnd_34674 := by
    simpa [prefixWord, tailWord_34674, baseEnd_34674] using wordTrace_append hprefix tailTrace_34674
  have hstable : (prefixWord ++ tailWord_34674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34674).length < 2 ^ (prefixWord ++ tailWord_34674).sum := by decide
  have hdescent : baseEnd_34674 < baseStart_34674 := by decide
  rcases family_descends (prefixWord ++ tailWord_34674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34681 : List Nat := [1, 2, 1, 3, 2, 2, 1, 8]
def baseStart_34681 : Nat := 118140960795 + 34681 * 2 ^ 59
def prefixEnd_34681 : Nat := 4983230072969 + 3 ^ 40 * 34681 * 2
def baseEnd_34681 : Nat := 5276451134424901963855

theorem tailTrace_34681 : CollatzResearch.WordTrace tailWord_34681 prefixEnd_34681 5276451134424901963855 := by
  unfold tailWord_34681
  simp only [CollatzResearch.WordTrace]
  refine ⟨1264919987364134888351897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 843279991576089925567931 1264919987364134888351897)
  ·
    refine ⟨948689990523101166263923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1264919987364134888351897 948689990523101166263923)
    ·
      refine ⟨1423034985784651749395885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 948689990523101166263923 1423034985784651749395885)
      ·
        refine ⟨533638119669244406023457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1423034985784651749395885 533638119669244406023457)
        ·
          refine ⟨400228589751933304517593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 533638119669244406023457 400228589751933304517593)
          ·
            refine ⟨300171442313949978388195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 400228589751933304517593 300171442313949978388195)
            ·
              refine ⟨450257163470924967582293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300171442313949978388195 450257163470924967582293)
              ·
                refine ⟨5276451134424901963855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 450257163470924967582293 5276451134424901963855)
                ·
                  rfl

theorem cell20_34681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 8].length) (baseStart_34681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34681 prefixEnd_34681 := by exact prefixLift 34681
  have htrace : WordTrace (prefixWord ++ tailWord_34681) baseStart_34681 baseEnd_34681 := by
    simpa [prefixWord, tailWord_34681, baseEnd_34681] using wordTrace_append hprefix tailTrace_34681
  have hstable : (prefixWord ++ tailWord_34681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34681).length < 2 ^ (prefixWord ++ tailWord_34681).sum := by decide
  have hdescent : baseEnd_34681 < baseStart_34681 := by decide
  rcases family_descends (prefixWord ++ tailWord_34681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34698 : List Nat := [3, 1, 2, 4, 2, 8]
def baseStart_34698 : Nat := 118140960795 + 34698 * 2 ^ 59
def prefixEnd_34698 : Nat := 4983230072969 + 3 ^ 40 * 34698 * 2
def baseEnd_34698 : Nat := 586559728388822308327

theorem tailTrace_34698 : CollatzResearch.WordTrace tailWord_34698 prefixEnd_34698 586559728388822308327 := by
  unfold tailWord_34698
  simp only [CollatzResearch.WordTrace]
  refine ⟨316385007075636697930187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 843693352201697861147165 316385007075636697930187)
  ·
    refine ⟨474577510613455046895281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 316385007075636697930187 474577510613455046895281)
    ·
      refine ⟨355933132960091285171461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 474577510613455046895281 355933132960091285171461)
      ·
        refine ⟨66737462430017115969649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 355933132960091285171461 66737462430017115969649)
        ·
          refine ⟨50053096822512836977237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66737462430017115969649 50053096822512836977237)
          ·
            refine ⟨586559728388822308327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 50053096822512836977237 586559728388822308327)
            ·
              rfl

theorem cell20_34698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 8].length) (baseStart_34698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34698 prefixEnd_34698 := by exact prefixLift 34698
  have htrace : WordTrace (prefixWord ++ tailWord_34698) baseStart_34698 baseEnd_34698 := by
    simpa [prefixWord, tailWord_34698, baseEnd_34698] using wordTrace_append hprefix tailTrace_34698
  have hstable : (prefixWord ++ tailWord_34698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34698).length < 2 ^ (prefixWord ++ tailWord_34698).sum := by decide
  have hdescent : baseEnd_34698 < baseStart_34698 := by decide
  rcases family_descends (prefixWord ++ tailWord_34698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34705 : List Nat := [1, 2, 2, 1, 1, 1, 5, 4, 3]
def baseStart_34705 : Nat := 118140960795 + 34705 * 2 ^ 59
def prefixEnd_34705 : Nat := 4983230072969 + 3 ^ 40 * 34705 * 2
def baseEnd_34705 : Nat := 15840307657237289091467

theorem tailTrace_34705 : CollatzResearch.WordTrace tailWord_34705 prefixEnd_34705 15840307657237289091467 := by
  unfold tailWord_34705
  simp only [CollatzResearch.WordTrace]
  refine ⟨1265795339277186987225569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 843863559518124658150379 1265795339277186987225569)
  ·
    refine ⟨949346504457890240419177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1265795339277186987225569 949346504457890240419177)
    ·
      refine ⟨712009878343417680314383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 949346504457890240419177 712009878343417680314383)
      ·
        refine ⟨1068014817515126520471575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 712009878343417680314383 1068014817515126520471575)
        ·
          refine ⟨1602022226272689780707363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1068014817515126520471575 1602022226272689780707363)
          ·
            refine ⟨2403033339409034671061045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1602022226272689780707363 2403033339409034671061045)
            ·
              refine ⟨225284375569597000411973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2403033339409034671061045 225284375569597000411973)
              ·
                refine ⟨42240820419299437577245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 225284375569597000411973 42240820419299437577245)
                ·
                  refine ⟨15840307657237289091467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42240820419299437577245 15840307657237289091467)
                  ·
                    rfl

theorem cell20_34705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 3].length) (baseStart_34705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34705 prefixEnd_34705 := by exact prefixLift 34705
  have htrace : WordTrace (prefixWord ++ tailWord_34705) baseStart_34705 baseEnd_34705 := by
    simpa [prefixWord, tailWord_34705, baseEnd_34705] using wordTrace_append hprefix tailTrace_34705
  have hstable : (prefixWord ++ tailWord_34705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34705).length < 2 ^ (prefixWord ++ tailWord_34705).sum := by decide
  have hdescent : baseEnd_34705 < baseStart_34705 := by decide
  rcases family_descends (prefixWord ++ tailWord_34705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34760 : List Nat := [2, 1, 3, 1, 4, 1, 3, 2, 3]
def baseStart_34760 : Nat := 118140960795 + 34760 * 2 ^ 59
def prefixEnd_34760 : Nat := 4983230072969 + 3 ^ 40 * 34760 * 2
def baseEnd_34760 : Nat := 15865411155901542257909

theorem tailTrace_34760 : CollatzResearch.WordTrace tailWord_34760 prefixEnd_34760 15865411155901542257909 := by
  unfold tailWord_34760
  simp only [CollatzResearch.WordTrace]
  refine ⟨633900677038965690238867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 845200902718620920318489 633900677038965690238867)
  ·
    refine ⟨950851015558448535358301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 633900677038965690238867 950851015558448535358301)
    ·
      refine ⟨356569130834418200759363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 950851015558448535358301 356569130834418200759363)
      ·
        refine ⟨534853696251627301139045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356569130834418200759363 534853696251627301139045)
        ·
          refine ⟨100285068047180118963571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 534853696251627301139045 100285068047180118963571)
          ·
            refine ⟨150427602070770178445357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100285068047180118963571 150427602070770178445357)
            ·
              refine ⟨56410350776538816917009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150427602070770178445357 56410350776538816917009)
              ·
                refine ⟨42307763082404112687757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56410350776538816917009 42307763082404112687757)
                ·
                  refine ⟨15865411155901542257909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42307763082404112687757 15865411155901542257909)
                  ·
                    rfl

theorem cell20_34760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 3].length) (baseStart_34760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34760 prefixEnd_34760 := by exact prefixLift 34760
  have htrace : WordTrace (prefixWord ++ tailWord_34760) baseStart_34760 baseEnd_34760 := by
    simpa [prefixWord, tailWord_34760, baseEnd_34760] using wordTrace_append hprefix tailTrace_34760
  have hstable : (prefixWord ++ tailWord_34760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34760).length < 2 ^ (prefixWord ++ tailWord_34760).sum := by decide
  have hdescent : baseEnd_34760 < baseStart_34760 := by decide
  rcases family_descends (prefixWord ++ tailWord_34760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34767 : List Nat := [1, 1, 2, 1, 1, 5, 1, 6, 2]
def baseStart_34767 : Nat := 118140960795 + 34767 * 2 ^ 59
def prefixEnd_34767 : Nat := 4983230072969 + 3 ^ 40 * 34767 * 2
def baseEnd_34767 : Nat := 15868606146640629024547

theorem tailTrace_34767 : CollatzResearch.WordTrace tailWord_34767 prefixEnd_34767 15868606146640629024547 := by
  unfold tailWord_34767
  simp only [CollatzResearch.WordTrace]
  refine ⟨1268056665052571575982555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 845371110035047717321703 1268056665052571575982555)
  ·
    refine ⟨1902084997578857363973833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1268056665052571575982555 1902084997578857363973833)
    ·
      refine ⟨1426563748184143022980375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1902084997578857363973833 1426563748184143022980375)
      ·
        refine ⟨2139845622276214534470563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1426563748184143022980375 2139845622276214534470563)
        ·
          refine ⟨3209768433414321801705845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2139845622276214534470563 3209768433414321801705845)
          ·
            refine ⟨300915790632592668909923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3209768433414321801705845 300915790632592668909923)
            ·
              refine ⟨451373685948889003364885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300915790632592668909923 451373685948889003364885)
              ·
                refine ⟨21158141528854172032729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 451373685948889003364885 21158141528854172032729)
                ·
                  refine ⟨15868606146640629024547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21158141528854172032729 15868606146640629024547)
                  ·
                    rfl

theorem cell20_34767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 2].length) (baseStart_34767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34767 prefixEnd_34767 := by exact prefixLift 34767
  have htrace : WordTrace (prefixWord ++ tailWord_34767) baseStart_34767 baseEnd_34767 := by
    simpa [prefixWord, tailWord_34767, baseEnd_34767] using wordTrace_append hprefix tailTrace_34767
  have hstable : (prefixWord ++ tailWord_34767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34767).length < 2 ^ (prefixWord ++ tailWord_34767).sum := by decide
  have hdescent : baseEnd_34767 < baseStart_34767 := by decide
  rcases family_descends (prefixWord ++ tailWord_34767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34777 : List Nat := [1, 2, 1, 2, 6, 1, 3, 1, 3]
def baseStart_34777 : Nat := 118140960795 + 34777 * 2 ^ 59
def prefixEnd_34777 : Nat := 4983230072969 + 3 ^ 40 * 34777 * 2
def baseEnd_34777 : Nat := 15873170419125038691173

theorem tailTrace_34777 : CollatzResearch.WordTrace tailWord_34777 prefixEnd_34777 15873170419125038691173 := by
  unfold tailWord_34777
  simp only [CollatzResearch.WordTrace]
  refine ⟨1268421395016343283846585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 845614263344228855897723 1268421395016343283846585)
  ·
    refine ⟨951316046262257462884939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1268421395016343283846585 951316046262257462884939)
    ·
      refine ⟨1426974069393386194327409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 951316046262257462884939 1426974069393386194327409)
      ·
        refine ⟨1070230552045039645745557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1426974069393386194327409 1070230552045039645745557)
        ·
          refine ⟨50167057127111233394323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1070230552045039645745557 50167057127111233394323)
          ·
            refine ⟨75250585690666850091485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50167057127111233394323 75250585690666850091485)
            ·
              refine ⟨28218969634000068784307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75250585690666850091485 28218969634000068784307)
              ·
                refine ⟨42328454451000103176461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28218969634000068784307 42328454451000103176461)
                ·
                  refine ⟨15873170419125038691173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42328454451000103176461 15873170419125038691173)
                  ·
                    rfl

theorem cell20_34777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 3].length) (baseStart_34777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34777 prefixEnd_34777 := by exact prefixLift 34777
  have htrace : WordTrace (prefixWord ++ tailWord_34777) baseStart_34777 baseEnd_34777 := by
    simpa [prefixWord, tailWord_34777, baseEnd_34777] using wordTrace_append hprefix tailTrace_34777
  have hstable : (prefixWord ++ tailWord_34777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34777).length < 2 ^ (prefixWord ++ tailWord_34777).sum := by decide
  have hdescent : baseEnd_34777 < baseStart_34777 := by decide
  rcases family_descends (prefixWord ++ tailWord_34777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34788 : List Nat := [2, 3, 1, 1, 1, 1, 3, 4, 4]
def baseStart_34788 : Nat := 118140960795 + 34788 * 2 ^ 59
def prefixEnd_34788 : Nat := 4983230072969 + 3 ^ 40 * 34788 * 2
def baseEnd_34788 : Nat := 15878191118857889324461

theorem tailTrace_34788 : CollatzResearch.WordTrace tailWord_34788 prefixEnd_34788 15878191118857889324461 := by
  unfold tailWord_34788
  simp only [CollatzResearch.WordTrace]
  refine ⟨634411298988246081248509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 845881731984328108331345 634411298988246081248509)
  ·
    refine ⟨237904237120592280468191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 634411298988246081248509 237904237120592280468191)
    ·
      refine ⟨356856355680888420702287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237904237120592280468191 356856355680888420702287)
      ·
        refine ⟨535284533521332631053431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356856355680888420702287 535284533521332631053431)
        ·
          refine ⟨802926800281998946580147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535284533521332631053431 802926800281998946580147)
          ·
            refine ⟨1204390200422998419870221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 802926800281998946580147 1204390200422998419870221)
            ·
              refine ⟨451646325158624407451333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1204390200422998419870221 451646325158624407451333)
              ·
                refine ⟨84683685967242076397125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 451646325158624407451333 84683685967242076397125)
                ·
                  refine ⟨15878191118857889324461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84683685967242076397125 15878191118857889324461)
                  ·
                    rfl

theorem cell20_34788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_34788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34788 prefixEnd_34788 := by exact prefixLift 34788
  have htrace : WordTrace (prefixWord ++ tailWord_34788) baseStart_34788 baseEnd_34788 := by
    simpa [prefixWord, tailWord_34788, baseEnd_34788] using wordTrace_append hprefix tailTrace_34788
  have hstable : (prefixWord ++ tailWord_34788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34788).length < 2 ^ (prefixWord ++ tailWord_34788).sum := by decide
  have hdescent : baseEnd_34788 < baseStart_34788 := by decide
  rcases family_descends (prefixWord ++ tailWord_34788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34797 : List Nat := [1, 5, 1, 4, 2, 1, 1, 3, 2]
def baseStart_34797 : Nat := 118140960795 + 34797 * 2 ^ 59
def prefixEnd_34797 : Nat := 4983230072969 + 3 ^ 40 * 34797 * 2
def baseEnd_34797 : Nat := 15882298964093858024425

theorem tailTrace_34797 : CollatzResearch.WordTrace tailWord_34797 prefixEnd_34797 15882298964093858024425 := by
  unfold tailWord_34797
  simp only [CollatzResearch.WordTrace]
  refine ⟨1269150854943886699574645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 846100569962591133049763 1269150854943886699574645)
  ·
    refine ⟨118982892650989378085123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1269150854943886699574645 118982892650989378085123)
    ·
      refine ⟨178474338976484067127685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118982892650989378085123 178474338976484067127685)
      ·
        refine ⟨33463938558090762586441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 178474338976484067127685 33463938558090762586441)
        ·
          refine ⟨25097953918568071939831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33463938558090762586441 25097953918568071939831)
          ·
            refine ⟨37646930877852107909747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25097953918568071939831 37646930877852107909747)
            ·
              refine ⟨56470396316778161864621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37646930877852107909747 56470396316778161864621)
              ·
                refine ⟨21176398618791810699233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56470396316778161864621 21176398618791810699233)
                ·
                  refine ⟨15882298964093858024425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21176398618791810699233 15882298964093858024425)
                  ·
                    rfl

theorem cell20_34797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_34797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34797 prefixEnd_34797 := by exact prefixLift 34797
  have htrace : WordTrace (prefixWord ++ tailWord_34797) baseStart_34797 baseEnd_34797 := by
    simpa [prefixWord, tailWord_34797, baseEnd_34797] using wordTrace_append hprefix tailTrace_34797
  have hstable : (prefixWord ++ tailWord_34797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34797).length < 2 ^ (prefixWord ++ tailWord_34797).sum := by decide
  have hdescent : baseEnd_34797 < baseStart_34797 := by decide
  rcases family_descends (prefixWord ++ tailWord_34797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34801 : List Nat := [1, 2, 2, 2, 5, 2, 1, 3, 2]
def baseStart_34801 : Nat := 118140960795 + 34801 * 2 ^ 59
def prefixEnd_34801 : Nat := 4983230072969 + 3 ^ 40 * 34801 * 2
def baseEnd_34801 : Nat := 15884124673087621891075

theorem tailTrace_34801 : CollatzResearch.WordTrace tailWord_34801 prefixEnd_34801 15884124673087621891075 := by
  unfold tailWord_34801
  simp only [CollatzResearch.WordTrace]
  refine ⟨1269296746929395382720257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 846197831286263588480171 1269296746929395382720257)
  ·
    refine ⟨951972560197046537040193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1269296746929395382720257 951972560197046537040193)
    ·
      refine ⟨713979420147784902780145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 951972560197046537040193 713979420147784902780145)
      ·
        refine ⟨535484565110838677085109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 713979420147784902780145 535484565110838677085109)
        ·
          refine ⟨50201677979141125976729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 535484565110838677085109 50201677979141125976729)
          ·
            refine ⟨37651258484355844482547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50201677979141125976729 37651258484355844482547)
            ·
              refine ⟨56476887726533766723821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37651258484355844482547 56476887726533766723821)
              ·
                refine ⟨21178832897450162521433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56476887726533766723821 21178832897450162521433)
                ·
                  refine ⟨15884124673087621891075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21178832897450162521433 15884124673087621891075)
                  ·
                    rfl

theorem cell20_34801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 2].length) (baseStart_34801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34801 prefixEnd_34801 := by exact prefixLift 34801
  have htrace : WordTrace (prefixWord ++ tailWord_34801) baseStart_34801 baseEnd_34801 := by
    simpa [prefixWord, tailWord_34801, baseEnd_34801] using wordTrace_append hprefix tailTrace_34801
  have hstable : (prefixWord ++ tailWord_34801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34801).length < 2 ^ (prefixWord ++ tailWord_34801).sum := by decide
  have hdescent : baseEnd_34801 < baseStart_34801 := by decide
  rcases family_descends (prefixWord ++ tailWord_34801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34940 : List Nat := [2, 2, 2, 1, 1, 4, 1, 3, 4]
def baseStart_34940 : Nat := 118140960795 + 34940 * 2 ^ 59
def prefixEnd_34940 : Nat := 4983230072969 + 3 ^ 40 * 34940 * 2
def baseEnd_34940 : Nat := 15947568060620916257173

theorem tailTrace_34940 : CollatzResearch.WordTrace tailWord_34940 prefixEnd_34940 15947568060620916257173 := by
  unfold tailWord_34940
  simp only [CollatzResearch.WordTrace]
  refine ⟨637183246712911061015137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 849577662283881414686849 637183246712911061015137)
  ·
    refine ⟨477887435034683295761353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 637183246712911061015137 477887435034683295761353)
    ·
      refine ⟨358415576276012471821015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 477887435034683295761353 358415576276012471821015)
      ·
        refine ⟨537623364414018707731523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358415576276012471821015 537623364414018707731523)
        ·
          refine ⟨806435046621028061597285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537623364414018707731523 806435046621028061597285)
          ·
            refine ⟨151206571241442761549491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 806435046621028061597285 151206571241442761549491)
            ·
              refine ⟨226809856862164142324237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151206571241442761549491 226809856862164142324237)
              ·
                refine ⟨85053696323311553371589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 226809856862164142324237 85053696323311553371589)
                ·
                  refine ⟨15947568060620916257173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85053696323311553371589 15947568060620916257173)
                  ·
                    rfl

theorem cell20_34940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_34940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34940 prefixEnd_34940 := by exact prefixLift 34940
  have htrace : WordTrace (prefixWord ++ tailWord_34940) baseStart_34940 baseEnd_34940 := by
    simpa [prefixWord, tailWord_34940, baseEnd_34940] using wordTrace_append hprefix tailTrace_34940
  have hstable : (prefixWord ++ tailWord_34940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34940).length < 2 ^ (prefixWord ++ tailWord_34940).sum := by decide
  have hdescent : baseEnd_34940 < baseStart_34940 := by decide
  rcases family_descends (prefixWord ++ tailWord_34940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34970 : List Nat := [3, 1, 1, 5, 3, 1, 1, 3, 2]
def baseStart_34970 : Nat := 118140960795 + 34970 * 2 ^ 59
def prefixEnd_34970 : Nat := 4983230072969 + 3 ^ 40 * 34970 * 2
def baseEnd_34970 : Nat := 15961260878074145257051

theorem tailTrace_34970 : CollatzResearch.WordTrace tailWord_34970 prefixEnd_34970 15961260878074145257051 := by
  unfold tailWord_34970
  simp only [CollatzResearch.WordTrace]
  refine ⟨318865170829284311405591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 850307122211424830414909 318865170829284311405591)
  ·
    refine ⟨478297756243926467108387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 318865170829284311405591 478297756243926467108387)
    ·
      refine ⟨717446634365889700662581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 478297756243926467108387 717446634365889700662581)
      ·
        refine ⟨67260621971802159437117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 717446634365889700662581 67260621971802159437117)
        ·
          refine ⟨25222733239425809788919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67260621971802159437117 25222733239425809788919)
          ·
            refine ⟨37834099859138714683379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25222733239425809788919 37834099859138714683379)
            ·
              refine ⟨56751149788708072025069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37834099859138714683379 56751149788708072025069)
              ·
                refine ⟨21281681170765527009401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56751149788708072025069 21281681170765527009401)
                ·
                  refine ⟨15961260878074145257051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21281681170765527009401 15961260878074145257051)
                  ·
                    rfl

theorem cell20_34970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 2].length) (baseStart_34970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_34970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_34970 prefixEnd_34970 := by exact prefixLift 34970
  have htrace : WordTrace (prefixWord ++ tailWord_34970) baseStart_34970 baseEnd_34970 := by
    simpa [prefixWord, tailWord_34970, baseEnd_34970] using wordTrace_append hprefix tailTrace_34970
  have hstable : (prefixWord ++ tailWord_34970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34970).length < 2 ^ (prefixWord ++ tailWord_34970).sum := by decide
  have hdescent : baseEnd_34970 < baseStart_34970 := by decide
  rcases family_descends (prefixWord ++ tailWord_34970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35042 : List Nat := [3, 3, 4, 1, 1, 2, 2, 2, 2]
def baseStart_35042 : Nat := 118140960795 + 35042 * 2 ^ 59
def prefixEnd_35042 : Nat := 4983230072969 + 3 ^ 40 * 35042 * 2
def baseEnd_35042 : Nat := 15994123639961894856757

theorem tailTrace_35042 : CollatzResearch.WordTrace tailWord_35042 prefixEnd_35042 15994123639961894856757 := by
  unfold tailWord_35042
  simp only [CollatzResearch.WordTrace]
  refine ⟨319521684764073385560845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 852057826037529028162253 319521684764073385560845)
  ·
    refine ⟨119820631786527519585317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 319521684764073385560845 119820631786527519585317)
    ·
      refine ⟨22466368459973909922247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119820631786527519585317 22466368459973909922247)
      ·
        refine ⟨33699552689960864883371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22466368459973909922247 33699552689960864883371)
        ·
          refine ⟨50549329034941297325057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33699552689960864883371 50549329034941297325057)
          ·
            refine ⟨37911996776205972993793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50549329034941297325057 37911996776205972993793)
            ·
              refine ⟨28433997582154479745345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37911996776205972993793 28433997582154479745345)
              ·
                refine ⟨21325498186615859809009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28433997582154479745345 21325498186615859809009)
                ·
                  refine ⟨15994123639961894856757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21325498186615859809009 15994123639961894856757)
                  ·
                    rfl

theorem cell20_35042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_35042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35042 prefixEnd_35042 := by exact prefixLift 35042
  have htrace : WordTrace (prefixWord ++ tailWord_35042) baseStart_35042 baseEnd_35042 := by
    simpa [prefixWord, tailWord_35042, baseEnd_35042] using wordTrace_append hprefix tailTrace_35042
  have hstable : (prefixWord ++ tailWord_35042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35042).length < 2 ^ (prefixWord ++ tailWord_35042).sum := by decide
  have hdescent : baseEnd_35042 < baseStart_35042 := by decide
  rcases family_descends (prefixWord ++ tailWord_35042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35043 : List Nat := [1, 1, 1, 8, 1, 1, 2, 2, 3]
def baseStart_35043 : Nat := 118140960795 + 35043 * 2 ^ 59
def prefixEnd_35043 : Nat := 4983230072969 + 3 ^ 40 * 35043 * 2
def baseEnd_35043 : Nat := 15994580067210335823419

theorem tailTrace_35043 : CollatzResearch.WordTrace tailWord_35043 prefixEnd_35043 15994580067210335823419 := by
  unfold tailWord_35043
  simp only [CollatzResearch.WordTrace]
  refine ⟨1278123212052670713029783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 852082141368447142019855 1278123212052670713029783)
  ·
    refine ⟨1917184818079006069544675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1278123212052670713029783 1917184818079006069544675)
    ·
      refine ⟨2875777227118509104317013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1917184818079006069544675 2875777227118509104317013)
      ·
        refine ⟨33700514380295028566215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 2875777227118509104317013 33700514380295028566215)
        ·
          refine ⟨50550771570442542849323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33700514380295028566215 50550771570442542849323)
          ·
            refine ⟨75826157355663814273985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50550771570442542849323 75826157355663814273985)
            ·
              refine ⟨56869618016747860705489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75826157355663814273985 56869618016747860705489)
              ·
                refine ⟨42652213512560895529117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56869618016747860705489 42652213512560895529117)
                ·
                  refine ⟨15994580067210335823419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42652213512560895529117 15994580067210335823419)
                  ·
                    rfl

theorem cell20_35043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 3].length) (baseStart_35043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35043 prefixEnd_35043 := by exact prefixLift 35043
  have htrace : WordTrace (prefixWord ++ tailWord_35043) baseStart_35043 baseEnd_35043 := by
    simpa [prefixWord, tailWord_35043, baseEnd_35043] using wordTrace_append hprefix tailTrace_35043
  have hstable : (prefixWord ++ tailWord_35043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35043).length < 2 ^ (prefixWord ++ tailWord_35043).sum := by decide
  have hdescent : baseEnd_35043 < baseStart_35043 := by decide
  rcases family_descends (prefixWord ++ tailWord_35043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35054 : List Nat := [4, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_35054 : Nat := 118140960795 + 35054 * 2 ^ 59
def prefixEnd_35054 : Nat := 4983230072969 + 3 ^ 40 * 35054 * 2
def baseEnd_35054 : Nat := 15999600766943186456707

theorem tailTrace_35054 : CollatzResearch.WordTrace tailWord_35054 prefixEnd_35054 15999600766943186456707 := by
  unfold tailWord_35054
  simp only [CollatzResearch.WordTrace]
  refine ⟨159815551876602448960027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 852349610008546394453477 159815551876602448960027)
  ·
    refine ⟨239723327814903673440041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159815551876602448960027 239723327814903673440041)
    ·
      refine ⟨179792495861177755080031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239723327814903673440041 179792495861177755080031)
      ·
        refine ⟨269688743791766632620047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179792495861177755080031 269688743791766632620047)
        ·
          refine ⟨404533115687649948930071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269688743791766632620047 404533115687649948930071)
          ·
            refine ⟨606799673531474923395107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404533115687649948930071 606799673531474923395107)
            ·
              refine ⟨910199510297212385092661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606799673531474923395107 910199510297212385092661)
              ·
                refine ⟨85331204090363661102437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 910199510297212385092661 85331204090363661102437)
                ·
                  refine ⟨15999600766943186456707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85331204090363661102437 15999600766943186456707)
                  ·
                    rfl

theorem cell20_35054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_35054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35054 prefixEnd_35054 := by exact prefixLift 35054
  have htrace : WordTrace (prefixWord ++ tailWord_35054) baseStart_35054 baseEnd_35054 := by
    simpa [prefixWord, tailWord_35054, baseEnd_35054] using wordTrace_append hprefix tailTrace_35054
  have hstable : (prefixWord ++ tailWord_35054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35054).length < 2 ^ (prefixWord ++ tailWord_35054).sum := by decide
  have hdescent : baseEnd_35054 < baseStart_35054 := by decide
  rcases family_descends (prefixWord ++ tailWord_35054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35109 : List Nat := [1, 3, 1, 2, 5, 1, 2, 1, 4]
def baseStart_35109 : Nat := 118140960795 + 35109 * 2 ^ 59
def prefixEnd_35109 : Nat := 4983230072969 + 3 ^ 40 * 35109 * 2
def baseEnd_35109 : Nat := 16024704265607439623149

theorem tailTrace_35109 : CollatzResearch.WordTrace tailWord_35109 prefixEnd_35109 16024704265607439623149 := by
  unfold tailWord_35109
  simp only [CollatzResearch.WordTrace]
  refine ⟨1280530429813563984932381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 853686953209042656621587 1280530429813563984932381)
  ·
    refine ⟨480198911180086494349643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1280530429813563984932381 480198911180086494349643)
    ·
      refine ⟨720298366770129741524465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 480198911180086494349643 720298366770129741524465)
      ·
        refine ⟨540223775077597306143349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 720298366770129741524465 540223775077597306143349)
        ·
          refine ⟨50645978913524747450939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 540223775077597306143349 50645978913524747450939)
          ·
            refine ⟨75968968370287121176409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50645978913524747450939 75968968370287121176409)
            ·
              refine ⟨56976726277715340882307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75968968370287121176409 56976726277715340882307)
              ·
                refine ⟨85465089416573011323461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56976726277715340882307 85465089416573011323461)
                ·
                  refine ⟨16024704265607439623149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85465089416573011323461 16024704265607439623149)
                  ·
                    rfl

theorem cell20_35109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_35109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35109 prefixEnd_35109 := by exact prefixLift 35109
  have htrace : WordTrace (prefixWord ++ tailWord_35109) baseStart_35109 baseEnd_35109 := by
    simpa [prefixWord, tailWord_35109, baseEnd_35109] using wordTrace_append hprefix tailTrace_35109
  have hstable : (prefixWord ++ tailWord_35109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35109).length < 2 ^ (prefixWord ++ tailWord_35109).sum := by decide
  have hdescent : baseEnd_35109 < baseStart_35109 := by decide
  rcases family_descends (prefixWord ++ tailWord_35109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35130 : List Nat := [3, 1, 1, 1, 4, 2, 2, 2, 4]
def baseStart_35130 : Nat := 118140960795 + 35130 * 2 ^ 59
def prefixEnd_35130 : Nat := 4983230072969 + 3 ^ 40 * 35130 * 2
def baseEnd_35130 : Nat := 16034289237824699923063

theorem tailTrace_35130 : CollatzResearch.WordTrace tailWord_35130 prefixEnd_35130 16034289237824699923063 := by
  unfold tailWord_35130
  simp only [CollatzResearch.WordTrace]
  refine ⟨320324090684371142861711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 854197575158323047631229 320324090684371142861711)
  ·
    refine ⟨480486136026556714292567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 320324090684371142861711 480486136026556714292567)
    ·
      refine ⟨720729204039835071438851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 480486136026556714292567 720729204039835071438851)
      ·
        refine ⟨1081093806059752607158277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 720729204039835071438851 1081093806059752607158277)
        ·
          refine ⟨202705088636203613842177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1081093806059752607158277 202705088636203613842177)
          ·
            refine ⟨152028816477152710381633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202705088636203613842177 152028816477152710381633)
            ·
              refine ⟨114021612357864532786225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152028816477152710381633 114021612357864532786225)
              ·
                refine ⟨85516209268398399589669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114021612357864532786225 85516209268398399589669)
                ·
                  refine ⟨16034289237824699923063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85516209268398399589669 16034289237824699923063)
                  ·
                    rfl

theorem cell20_35130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_35130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35130 prefixEnd_35130 := by exact prefixLift 35130
  have htrace : WordTrace (prefixWord ++ tailWord_35130) baseStart_35130 baseEnd_35130 := by
    simpa [prefixWord, tailWord_35130, baseEnd_35130] using wordTrace_append hprefix tailTrace_35130
  have hstable : (prefixWord ++ tailWord_35130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35130).length < 2 ^ (prefixWord ++ tailWord_35130).sum := by decide
  have hdescent : baseEnd_35130 < baseStart_35130 := by decide
  rcases family_descends (prefixWord ++ tailWord_35130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35144 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 5]
def baseStart_35144 : Nat := 118140960795 + 35144 * 2 ^ 59
def prefixEnd_35144 : Nat := 4983230072969 + 3 ^ 40 * 35144 * 2
def baseEnd_35144 : Nat := 16040679219302873456339

theorem tailTrace_35144 : CollatzResearch.WordTrace tailWord_35144 prefixEnd_35144 16040679219302873456339 := by
  unfold tailWord_35144
  simp only [CollatzResearch.WordTrace]
  refine ⟨640903492343382481228243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 854537989791176641637657 640903492343382481228243)
  ·
    refine ⟨961355238515073721842365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 640903492343382481228243 961355238515073721842365)
    ·
      refine ⟨360508214443152645690887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 961355238515073721842365 360508214443152645690887)
      ·
        refine ⟨540762321664728968536331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360508214443152645690887 540762321664728968536331)
        ·
          refine ⟨811143482497093452804497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540762321664728968536331 811143482497093452804497)
          ·
            refine ⟨608357611872820089603373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 811143482497093452804497 608357611872820089603373)
            ·
              refine ⟨228134104452307533601265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 608357611872820089603373 228134104452307533601265)
              ·
                refine ⟨171100578339230650200949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228134104452307533601265 171100578339230650200949)
                ·
                  refine ⟨16040679219302873456339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 171100578339230650200949 16040679219302873456339)
                  ·
                    rfl

theorem cell20_35144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_35144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35144 prefixEnd_35144 := by exact prefixLift 35144
  have htrace : WordTrace (prefixWord ++ tailWord_35144) baseStart_35144 baseEnd_35144 := by
    simpa [prefixWord, tailWord_35144, baseEnd_35144] using wordTrace_append hprefix tailTrace_35144
  have hstable : (prefixWord ++ tailWord_35144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35144).length < 2 ^ (prefixWord ++ tailWord_35144).sum := by decide
  have hdescent : baseEnd_35144 < baseStart_35144 := by decide
  rcases family_descends (prefixWord ++ tailWord_35144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35175 : List Nat := [1, 1, 5, 1, 3, 1, 1, 7]
def baseStart_35175 : Nat := 118140960795 + 35175 * 2 ^ 59
def prefixEnd_35175 : Nat := 4983230072969 + 3 ^ 40 * 35175 * 2
def baseEnd_35175 : Nat := 5351609488001514474293

theorem tailTrace_35175 : CollatzResearch.WordTrace tailWord_35175 prefixEnd_35175 5351609488001514474293 := by
  unfold tailWord_35175
  simp only [CollatzResearch.WordTrace]
  refine ⟨1282937647574457256834979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 855291765049638171223319 1282937647574457256834979)
  ·
    refine ⟨1924406471361685885252469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1282937647574457256834979 1924406471361685885252469)
    ·
      refine ⟨180413106690158051742419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1924406471361685885252469 180413106690158051742419)
      ·
        refine ⟨270619660035237077613629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180413106690158051742419 270619660035237077613629)
        ·
          refine ⟨101482372513213904105111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 270619660035237077613629 101482372513213904105111)
          ·
            refine ⟨152223558769820856157667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101482372513213904105111 152223558769820856157667)
            ·
              refine ⟨228335338154731284236501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152223558769820856157667 228335338154731284236501)
              ·
                refine ⟨5351609488001514474293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 228335338154731284236501 5351609488001514474293)
                ·
                  rfl

theorem cell20_35175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 7].length) (baseStart_35175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35175 prefixEnd_35175 := by exact prefixLift 35175
  have htrace : WordTrace (prefixWord ++ tailWord_35175) baseStart_35175 baseEnd_35175 := by
    simpa [prefixWord, tailWord_35175, baseEnd_35175] using wordTrace_append hprefix tailTrace_35175
  have hstable : (prefixWord ++ tailWord_35175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35175).length < 2 ^ (prefixWord ++ tailWord_35175).sum := by decide
  have hdescent : baseEnd_35175 < baseStart_35175 := by decide
  rcases family_descends (prefixWord ++ tailWord_35175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35178 : List Nat := [3, 1, 3, 3, 1, 2, 1, 3, 3]
def baseStart_35178 : Nat := 118140960795 + 35178 * 2 ^ 59
def prefixEnd_35178 : Nat := 4983230072969 + 3 ^ 40 * 35178 * 2
def baseEnd_35178 : Nat := 16056197745749866322867

theorem tailTrace_35178 : CollatzResearch.WordTrace tailWord_35178 prefixEnd_35178 16056197745749866322867 := by
  unfold tailWord_35178
  simp only [CollatzResearch.WordTrace]
  refine ⟨320761766640897192298547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 855364711042392512796125 320761766640897192298547)
  ·
    refine ⟨481142649961345788447821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 320761766640897192298547 481142649961345788447821)
    ·
      refine ⟨180428493735504670667933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 481142649961345788447821 180428493735504670667933)
      ·
        refine ⟨67660685150814251500475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180428493735504670667933 67660685150814251500475)
        ·
          refine ⟨101491027726221377250713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67660685150814251500475 101491027726221377250713)
          ·
            refine ⟨76118270794666032938035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101491027726221377250713 76118270794666032938035)
            ·
              refine ⟨114177406191999049407053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76118270794666032938035 114177406191999049407053)
              ·
                refine ⟨42816527321999643527645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114177406191999049407053 42816527321999643527645)
                ·
                  refine ⟨16056197745749866322867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42816527321999643527645 16056197745749866322867)
                  ·
                    rfl

theorem cell20_35178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_35178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35178 prefixEnd_35178 := by exact prefixLift 35178
  have htrace : WordTrace (prefixWord ++ tailWord_35178) baseStart_35178 baseEnd_35178 := by
    simpa [prefixWord, tailWord_35178, baseEnd_35178] using wordTrace_append hprefix tailTrace_35178
  have hstable : (prefixWord ++ tailWord_35178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35178).length < 2 ^ (prefixWord ++ tailWord_35178).sum := by decide
  have hdescent : baseEnd_35178 < baseStart_35178 := by decide
  rcases family_descends (prefixWord ++ tailWord_35178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35222 : List Nat := [5, 3, 1, 2, 2, 1, 1, 5]
def baseStart_35222 : Nat := 118140960795 + 35222 * 2 ^ 59
def prefixEnd_35222 : Nat := 4983230072969 + 3 ^ 40 * 35222 * 2
def baseEnd_35222 : Nat := 5358760181560422952007

theorem tailTrace_35222 : CollatzResearch.WordTrace tailWord_35222 prefixEnd_35222 5358760181560422952007 := by
  unfold tailWord_35222
  simp only [CollatzResearch.WordTrace]
  refine ⟨80290742400261517737245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 856434585602789522530613 80290742400261517737245)
  ·
    refine ⟨30109028400098069151467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80290742400261517737245 30109028400098069151467)
    ·
      refine ⟨45163542600147103727201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30109028400098069151467 45163542600147103727201)
      ·
        refine ⟨33872656950110327795401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45163542600147103727201 33872656950110327795401)
        ·
          refine ⟨25404492712582745846551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33872656950110327795401 25404492712582745846551)
          ·
            refine ⟨38106739068874118769827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25404492712582745846551 38106739068874118769827)
            ·
              refine ⟨57160108603311178154741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38106739068874118769827 57160108603311178154741)
              ·
                refine ⟨5358760181560422952007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57160108603311178154741 5358760181560422952007)
                ·
                  rfl

theorem cell20_35222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_35222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35222 prefixEnd_35222 := by exact prefixLift 35222
  have htrace : WordTrace (prefixWord ++ tailWord_35222) baseStart_35222 baseEnd_35222 := by
    simpa [prefixWord, tailWord_35222, baseEnd_35222] using wordTrace_append hprefix tailTrace_35222
  have hstable : (prefixWord ++ tailWord_35222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35222).length < 2 ^ (prefixWord ++ tailWord_35222).sum := by decide
  have hdescent : baseEnd_35222 < baseStart_35222 := by decide
  rcases family_descends (prefixWord ++ tailWord_35222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35261 : List Nat := [1, 4, 1, 2, 2, 2, 1, 5, 2]
def baseStart_35261 : Nat := 118140960795 + 35261 * 2 ^ 59
def prefixEnd_35261 : Nat := 4983230072969 + 3 ^ 40 * 35261 * 2
def baseEnd_35261 : Nat := 16094081207370466555861

theorem tailTrace_35261 : CollatzResearch.WordTrace tailWord_35261 prefixEnd_35261 16094081207370466555861 := by
  unfold tailWord_35261
  simp only [CollatzResearch.WordTrace]
  refine ⟨1286074325262893944465637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 857382883508595962977091 1286074325262893944465637)
  ·
    refine ⟨241138935986792614587307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1286074325262893944465637 241138935986792614587307)
    ·
      refine ⟨361708403980188921880961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241138935986792614587307 361708403980188921880961)
      ·
        refine ⟨271281302985141691410721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 361708403980188921880961 271281302985141691410721)
        ·
          refine ⟨203460977238856268558041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271281302985141691410721 203460977238856268558041)
          ·
            refine ⟨152595732929142201418531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203460977238856268558041 152595732929142201418531)
            ·
              refine ⟨228893599393713302127797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152595732929142201418531 228893599393713302127797)
              ·
                refine ⟨21458774943160622074481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 228893599393713302127797 21458774943160622074481)
                ·
                  refine ⟨16094081207370466555861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21458774943160622074481 16094081207370466555861)
                  ·
                    rfl

theorem cell20_35261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_35261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35261 prefixEnd_35261 := by exact prefixLift 35261
  have htrace : WordTrace (prefixWord ++ tailWord_35261) baseStart_35261 baseEnd_35261 := by
    simpa [prefixWord, tailWord_35261, baseEnd_35261] using wordTrace_append hprefix tailTrace_35261
  have hstable : (prefixWord ++ tailWord_35261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35261).length < 2 ^ (prefixWord ++ tailWord_35261).sum := by decide
  have hdescent : baseEnd_35261 < baseStart_35261 := by decide
  rcases family_descends (prefixWord ++ tailWord_35261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35268 : List Nat := [2, 3, 3, 2, 2, 1, 7]
def baseStart_35268 : Nat := 118140960795 + 35268 * 2 ^ 59
def prefixEnd_35268 : Nat := 4983230072969 + 3 ^ 40 * 35268 * 2
def baseEnd_35268 : Nat := 1788586244234394813611

theorem tailTrace_35268 : CollatzResearch.WordTrace tailWord_35268 prefixEnd_35268 1788586244234394813611 := by
  unfold tailWord_35268
  simp only [CollatzResearch.WordTrace]
  refine ⟨643164818118767069985229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 857553090825022759980305 643164818118767069985229)
  ·
    refine ⟨241186806794537651244461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 643164818118767069985229 241186806794537651244461)
    ·
      refine ⟨90445052547951619216673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241186806794537651244461 90445052547951619216673)
      ·
        refine ⟨67833789410963714412505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90445052547951619216673 67833789410963714412505)
        ·
          refine ⟨50875342058222785809379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67833789410963714412505 50875342058222785809379)
          ·
            refine ⟨76313013087334178714069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50875342058222785809379 76313013087334178714069)
            ·
              refine ⟨1788586244234394813611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 76313013087334178714069 1788586244234394813611)
              ·
                rfl

theorem cell20_35268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 7].length) (baseStart_35268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35268 prefixEnd_35268 := by exact prefixLift 35268
  have htrace : WordTrace (prefixWord ++ tailWord_35268) baseStart_35268 baseEnd_35268 := by
    simpa [prefixWord, tailWord_35268, baseEnd_35268] using wordTrace_append hprefix tailTrace_35268
  have hstable : (prefixWord ++ tailWord_35268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35268).length < 2 ^ (prefixWord ++ tailWord_35268).sum := by decide
  have hdescent : baseEnd_35268 < baseStart_35268 := by decide
  rcases family_descends (prefixWord ++ tailWord_35268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35306 : List Nat := [3, 1, 3, 1, 3, 1, 4, 4]
def baseStart_35306 : Nat := 118140960795 + 35306 * 2 ^ 59
def prefixEnd_35306 : Nat := 4983230072969 + 3 ^ 40 * 35306 * 2
def baseEnd_35306 : Nat := 5371540144516770018559

theorem tailTrace_35306 : CollatzResearch.WordTrace tailWord_35306 prefixEnd_35306 5371540144516770018559 := by
  unfold tailWord_35306
  simp only [CollatzResearch.WordTrace]
  refine ⟨321928902524966657463443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 858477073399911086569181 321928902524966657463443)
  ·
    refine ⟨482893353787449986195165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 321928902524966657463443 482893353787449986195165)
    ·
      refine ⟨181085007670293744823187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 482893353787449986195165 181085007670293744823187)
      ·
        refine ⟨271627511505440617234781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181085007670293744823187 271627511505440617234781)
        ·
          refine ⟨101860316814540231463043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 271627511505440617234781 101860316814540231463043)
          ·
            refine ⟨152790475221810347194565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101860316814540231463043 152790475221810347194565)
            ·
              refine ⟨28648214104089440098981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152790475221810347194565 28648214104089440098981)
              ·
                refine ⟨5371540144516770018559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28648214104089440098981 5371540144516770018559)
                ·
                  rfl

theorem cell20_35306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_35306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35306 prefixEnd_35306 := by exact prefixLift 35306
  have htrace : WordTrace (prefixWord ++ tailWord_35306) baseStart_35306 baseEnd_35306 := by
    simpa [prefixWord, tailWord_35306, baseEnd_35306] using wordTrace_append hprefix tailTrace_35306
  have hstable : (prefixWord ++ tailWord_35306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35306).length < 2 ^ (prefixWord ++ tailWord_35306).sum := by decide
  have hdescent : baseEnd_35306 < baseStart_35306 := by decide
  rcases family_descends (prefixWord ++ tailWord_35306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35386 : List Nat := [3, 1, 1, 1, 3, 11]
def baseStart_35386 : Nat := 118140960795 + 35386 * 2 ^ 59
def prefixEnd_35386 : Nat := 4983230072969 + 3 ^ 40 * 35386 * 2
def baseEnd_35386 : Nat := 598190170867614347729

theorem tailTrace_35386 : CollatzResearch.WordTrace tailWord_35386 prefixEnd_35386 598190170867614347729 := by
  unfold tailWord_35386
  simp only [CollatzResearch.WordTrace]
  refine ⟨322658362452510073191503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 860422299873360195177341 322658362452510073191503)
  ·
    refine ⟨483987543678765109787255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 322658362452510073191503 483987543678765109787255)
    ·
      refine ⟨725981315518147664680883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 483987543678765109787255 725981315518147664680883)
      ·
        refine ⟨1088971973277221497021325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 725981315518147664680883 1088971973277221497021325)
        ·
          refine ⟨408364489978958061382997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1088971973277221497021325 408364489978958061382997)
          ·
            refine ⟨598190170867614347729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 408364489978958061382997 598190170867614347729)
            ·
              rfl

theorem cell20_35386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 11].length) (baseStart_35386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35386 prefixEnd_35386 := by exact prefixLift 35386
  have htrace : WordTrace (prefixWord ++ tailWord_35386) baseStart_35386 baseEnd_35386 := by
    simpa [prefixWord, tailWord_35386, baseEnd_35386] using wordTrace_append hprefix tailTrace_35386
  have hstable : (prefixWord ++ tailWord_35386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35386).length < 2 ^ (prefixWord ++ tailWord_35386).sum := by decide
  have hdescent : baseEnd_35386 < baseStart_35386 := by decide
  rcases family_descends (prefixWord ++ tailWord_35386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35389 : List Nat := [1, 4, 1, 3, 2, 1, 1, 4, 3]
def baseStart_35389 : Nat := 118140960795 + 35389 * 2 ^ 59
def prefixEnd_35389 : Nat := 4983230072969 + 3 ^ 40 * 35389 * 2
def baseEnd_35389 : Nat := 16152503895170910288671

theorem tailTrace_35389 : CollatzResearch.WordTrace tailWord_35389 prefixEnd_35389 16152503895170910288671 := by
  unfold tailWord_35389
  simp only [CollatzResearch.WordTrace]
  refine ⟨1290742868799171805125221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 860495245866114536750147 1290742868799171805125221)
  ·
    refine ⟨242014287899844713460979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1290742868799171805125221 242014287899844713460979)
    ·
      refine ⟨363021431849767070191469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242014287899844713460979 363021431849767070191469)
      ·
        refine ⟨136133036943662651321801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 363021431849767070191469 136133036943662651321801)
        ·
          refine ⟨102099777707746988491351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136133036943662651321801 102099777707746988491351)
          ·
            refine ⟨153149666561620482737027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102099777707746988491351 153149666561620482737027)
            ·
              refine ⟨229724499842430724105541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153149666561620482737027 229724499842430724105541)
              ·
                refine ⟨43073343720455760769789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 229724499842430724105541 43073343720455760769789)
                ·
                  refine ⟨16152503895170910288671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43073343720455760769789 16152503895170910288671)
                  ·
                    rfl

theorem cell20_35389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_35389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35389 prefixEnd_35389 := by exact prefixLift 35389
  have htrace : WordTrace (prefixWord ++ tailWord_35389) baseStart_35389 baseEnd_35389 := by
    simpa [prefixWord, tailWord_35389, baseEnd_35389] using wordTrace_append hprefix tailTrace_35389
  have hstable : (prefixWord ++ tailWord_35389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35389).length < 2 ^ (prefixWord ++ tailWord_35389).sum := by decide
  have hdescent : baseEnd_35389 < baseStart_35389 := by decide
  rcases family_descends (prefixWord ++ tailWord_35389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35424 : List Nat := [2, 1, 1, 3, 2, 1, 2, 8]
def baseStart_35424 : Nat := 118140960795 + 35424 * 2 ^ 59
def prefixEnd_35424 : Nat := 4983230072969 + 3 ^ 40 * 35424 * 2
def baseEnd_35424 : Nat := 5389492949622114707287

theorem tailTrace_35424 : CollatzResearch.WordTrace tailWord_35424 prefixEnd_35424 5389492949622114707287 := by
  unfold tailWord_35424
  simp only [CollatzResearch.WordTrace]
  refine ⟨646009711836186391324663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 861346282448248521766217 646009711836186391324663)
  ·
    refine ⟨969014567754279586986995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 646009711836186391324663 969014567754279586986995)
    ·
      refine ⟨1453521851631419380480493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 969014567754279586986995 1453521851631419380480493)
      ·
        refine ⟨545070694361782267680185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1453521851631419380480493 545070694361782267680185)
        ·
          refine ⟨408803020771336700760139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 545070694361782267680185 408803020771336700760139)
          ·
            refine ⟨613204531157005051140209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408803020771336700760139 613204531157005051140209)
            ·
              refine ⟨459903398367753788355157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 613204531157005051140209 459903398367753788355157)
              ·
                refine ⟨5389492949622114707287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 459903398367753788355157 5389492949622114707287)
                ·
                  rfl

theorem cell20_35424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_35424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35424 prefixEnd_35424 := by exact prefixLift 35424
  have htrace : WordTrace (prefixWord ++ tailWord_35424) baseStart_35424 baseEnd_35424 := by
    simpa [prefixWord, tailWord_35424, baseEnd_35424] using wordTrace_append hprefix tailTrace_35424
  have hstable : (prefixWord ++ tailWord_35424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35424).length < 2 ^ (prefixWord ++ tailWord_35424).sum := by decide
  have hdescent : baseEnd_35424 < baseStart_35424 := by decide
  rcases family_descends (prefixWord ++ tailWord_35424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35517 : List Nat := [1, 4, 1, 2, 1, 4, 2, 5]
def baseStart_35517 : Nat := 118140960795 + 35517 * 2 ^ 59
def prefixEnd_35517 : Nat := 4983230072969 + 3 ^ 40 * 35517 * 2
def baseEnd_35517 : Nat := 5403642194323784673827

theorem tailTrace_35517 : CollatzResearch.WordTrace tailWord_35517 prefixEnd_35517 5403642194323784673827 := by
  unfold tailWord_35517
  simp only [CollatzResearch.WordTrace]
  refine ⟨1295411412335449665784805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 863607608223633110523203 1295411412335449665784805)
  ·
    refine ⟨242889639812896812334651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1295411412335449665784805 242889639812896812334651)
    ·
      refine ⟨364334459719345218501977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242889639812896812334651 364334459719345218501977)
      ·
        refine ⟨273250844789508913876483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364334459719345218501977 273250844789508913876483)
        ·
          refine ⟨409876267184263370814725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273250844789508913876483 409876267184263370814725)
          ·
            refine ⟨76851800097049382027761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 409876267184263370814725 76851800097049382027761)
            ·
              refine ⟨57638850072787036520821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76851800097049382027761 57638850072787036520821)
              ·
                refine ⟨5403642194323784673827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57638850072787036520821 5403642194323784673827)
                ·
                  rfl

theorem cell20_35517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 5].length) (baseStart_35517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35517 prefixEnd_35517 := by exact prefixLift 35517
  have htrace : WordTrace (prefixWord ++ tailWord_35517) baseStart_35517 baseEnd_35517 := by
    simpa [prefixWord, tailWord_35517, baseEnd_35517] using wordTrace_append hprefix tailTrace_35517
  have hstable : (prefixWord ++ tailWord_35517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35517).length < 2 ^ (prefixWord ++ tailWord_35517).sum := by decide
  have hdescent : baseEnd_35517 < baseStart_35517 := by decide
  rcases family_descends (prefixWord ++ tailWord_35517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35520 : List Nat := [2, 1, 1, 2, 4, 4, 2, 1, 3]
def baseStart_35520 : Nat := 118140960795 + 35520 * 2 ^ 59
def prefixEnd_35520 : Nat := 4983230072969 + 3 ^ 40 * 35520 * 2
def baseEnd_35520 : Nat := 16212295864716676921469

theorem tailTrace_35520 : CollatzResearch.WordTrace tailWord_35520 prefixEnd_35520 16212295864716676921469 := by
  unfold tailWord_35520
  simp only [CollatzResearch.WordTrace]
  refine ⟨647760415662290589072007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 863680554216387452096009 647760415662290589072007)
  ·
    refine ⟨971640623493435883608011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 647760415662290589072007 971640623493435883608011)
    ·
      refine ⟨1457460935240153825412017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 971640623493435883608011 1457460935240153825412017)
      ·
        refine ⟨1093095701430115369059013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1457460935240153825412017 1093095701430115369059013)
        ·
          refine ⟨204955444018146631698565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1093095701430115369059013 204955444018146631698565)
          ·
            refine ⟨38429145753402493443481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 204955444018146631698565 38429145753402493443481)
            ·
              refine ⟨28821859315051870082611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38429145753402493443481 28821859315051870082611)
              ·
                refine ⟨43232788972577805123917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28821859315051870082611 43232788972577805123917)
                ·
                  refine ⟨16212295864716676921469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43232788972577805123917 16212295864716676921469)
                  ·
                    rfl

theorem cell20_35520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 3].length) (baseStart_35520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35520 prefixEnd_35520 := by exact prefixLift 35520
  have htrace : WordTrace (prefixWord ++ tailWord_35520) baseStart_35520 baseEnd_35520 := by
    simpa [prefixWord, tailWord_35520, baseEnd_35520] using wordTrace_append hprefix tailTrace_35520
  have hstable : (prefixWord ++ tailWord_35520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35520).length < 2 ^ (prefixWord ++ tailWord_35520).sum := by decide
  have hdescent : baseEnd_35520 < baseStart_35520 := by decide
  rcases family_descends (prefixWord ++ tailWord_35520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35565 : List Nat := [1, 5, 1, 2, 1, 1, 3, 4, 2]
def baseStart_35565 : Nat := 118140960795 + 35565 * 2 ^ 59
def prefixEnd_35565 : Nat := 4983230072969 + 3 ^ 40 * 35565 * 2
def baseEnd_35565 : Nat := 16232835090896520421285

theorem tailTrace_35565 : CollatzResearch.WordTrace tailWord_35565 prefixEnd_35565 16232835090896520421285 := by
  unfold tailWord_35565
  simp only [CollatzResearch.WordTrace]
  refine ⟨1297162116161553863532149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 864774744107702575688099 1297162116161553863532149)
  ·
    refine ⟨121608948390145674706139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1297162116161553863532149 121608948390145674706139)
    ·
      refine ⟨182413422585218512059209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121608948390145674706139 182413422585218512059209)
      ·
        refine ⟨136810066938913884044407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182413422585218512059209 136810066938913884044407)
        ·
          refine ⟨205215100408370826066611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136810066938913884044407 205215100408370826066611)
          ·
            refine ⟨307822650612556239099917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205215100408370826066611 307822650612556239099917)
            ·
              refine ⟨115433493979708589662469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 307822650612556239099917 115433493979708589662469)
              ·
                refine ⟨21643780121195360561713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115433493979708589662469 21643780121195360561713)
                ·
                  refine ⟨16232835090896520421285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21643780121195360561713 16232835090896520421285)
                  ·
                    rfl

theorem cell20_35565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_35565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35565 prefixEnd_35565 := by exact prefixLift 35565
  have htrace : WordTrace (prefixWord ++ tailWord_35565) baseStart_35565 baseEnd_35565 := by
    simpa [prefixWord, tailWord_35565, baseEnd_35565] using wordTrace_append hprefix tailTrace_35565
  have hstable : (prefixWord ++ tailWord_35565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35565).length < 2 ^ (prefixWord ++ tailWord_35565).sum := by decide
  have hdescent : baseEnd_35565 < baseStart_35565 := by decide
  rcases family_descends (prefixWord ++ tailWord_35565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35569 : List Nat := [1, 2, 2, 2, 2, 2, 2, 3, 4]
def baseStart_35569 : Nat := 118140960795 + 35569 * 2 ^ 59
def prefixEnd_35569 : Nat := 4983230072969 + 3 ^ 40 * 35569 * 2
def baseEnd_35569 : Nat := 16234660799890284287935

theorem tailTrace_35569 : CollatzResearch.WordTrace tailWord_35569 prefixEnd_35569 16234660799890284287935 := by
  unfold tailWord_35569
  simp only [CollatzResearch.WordTrace]
  refine ⟨1297308008147062546677761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 864872005431375031118507 1297308008147062546677761)
  ·
    refine ⟨972981006110296910008321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1297308008147062546677761 972981006110296910008321)
    ·
      refine ⟨729735754582722682506241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 972981006110296910008321 729735754582722682506241)
      ·
        refine ⟨547301815937042011879681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 729735754582722682506241 547301815937042011879681)
        ·
          refine ⟨410476361952781508909761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 547301815937042011879681 410476361952781508909761)
          ·
            refine ⟨307857271464586131682321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 410476361952781508909761 307857271464586131682321)
            ·
              refine ⟨230892953598439598761741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 307857271464586131682321 230892953598439598761741)
              ·
                refine ⟨86584857599414849535653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 230892953598439598761741 86584857599414849535653)
                ·
                  refine ⟨16234660799890284287935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86584857599414849535653 16234660799890284287935)
                  ·
                    rfl

theorem cell20_35569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_35569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35569 prefixEnd_35569 := by exact prefixLift 35569
  have htrace : WordTrace (prefixWord ++ tailWord_35569) baseStart_35569 baseEnd_35569 := by
    simpa [prefixWord, tailWord_35569, baseEnd_35569] using wordTrace_append hprefix tailTrace_35569
  have hstable : (prefixWord ++ tailWord_35569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35569).length < 2 ^ (prefixWord ++ tailWord_35569).sum := by decide
  have hdescent : baseEnd_35569 < baseStart_35569 := by decide
  rcases family_descends (prefixWord ++ tailWord_35569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35583 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 7]
def baseStart_35583 : Nat := 118140960795 + 35583 * 2 ^ 59
def prefixEnd_35583 : Nat := 4983230072969 + 3 ^ 40 * 35583 * 2
def baseEnd_35583 : Nat := 16241050781368457821211

theorem tailTrace_35583 : CollatzResearch.WordTrace tailWord_35583 prefixEnd_35583 16241050781368457821211 := by
  unfold tailWord_35583
  simp only [CollatzResearch.WordTrace]
  refine ⟨1297818630096342937687403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 865212420064228625124935 1297818630096342937687403)
  ·
    refine ⟨1946727945144514406531105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1297818630096342937687403 1946727945144514406531105)
    ·
      refine ⟨1460045958858385804898329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1946727945144514406531105 1460045958858385804898329)
      ·
        refine ⟨1095034469143789353673747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1460045958858385804898329 1095034469143789353673747)
        ·
          refine ⟨1642551703715684030510621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1095034469143789353673747 1642551703715684030510621)
          ·
            refine ⟨615956888893381511441483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1642551703715684030510621 615956888893381511441483)
            ·
              refine ⟨923935333340072267162225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 615956888893381511441483 923935333340072267162225)
              ·
                refine ⟨692951500005054200371669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 923935333340072267162225 692951500005054200371669)
                ·
                  refine ⟨16241050781368457821211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 692951500005054200371669 16241050781368457821211)
                  ·
                    rfl

theorem cell20_35583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_35583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35583 prefixEnd_35583 := by exact prefixLift 35583
  have htrace : WordTrace (prefixWord ++ tailWord_35583) baseStart_35583 baseEnd_35583 := by
    simpa [prefixWord, tailWord_35583, baseEnd_35583] using wordTrace_append hprefix tailTrace_35583
  have hstable : (prefixWord ++ tailWord_35583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35583).length < 2 ^ (prefixWord ++ tailWord_35583).sum := by decide
  have hdescent : baseEnd_35583 < baseStart_35583 := by decide
  rcases family_descends (prefixWord ++ tailWord_35583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35586 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 6]
def baseStart_35586 : Nat := 118140960795 + 35586 * 2 ^ 59
def prefixEnd_35586 : Nat := 4983230072969 + 3 ^ 40 * 35586 * 2
def baseEnd_35586 : Nat := 16242420063113780721199

theorem tailTrace_35586 : CollatzResearch.WordTrace tailWord_35586 prefixEnd_35586 16242420063113780721199 := by
  unfold tailWord_35586
  simp only [CollatzResearch.WordTrace]
  refine ⟨324482012271368612511653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 865285366056982966697741 324482012271368612511653)
  ·
    refine ⟨60840377300881614845935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 324482012271368612511653 60840377300881614845935)
    ·
      refine ⟨91260565951322422268903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60840377300881614845935 91260565951322422268903)
      ·
        refine ⟨136890848926983633403355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91260565951322422268903 136890848926983633403355)
        ·
          refine ⟨205336273390475450105033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136890848926983633403355 205336273390475450105033)
          ·
            refine ⟨154002205042856587578775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205336273390475450105033 154002205042856587578775)
            ·
              refine ⟨231003307564284881368163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154002205042856587578775 231003307564284881368163)
              ·
                refine ⟨346504961346427322052245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231003307564284881368163 346504961346427322052245)
                ·
                  refine ⟨16242420063113780721199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 346504961346427322052245 16242420063113780721199)
                  ·
                    rfl

theorem cell20_35586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_35586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35586 prefixEnd_35586 := by exact prefixLift 35586
  have htrace : WordTrace (prefixWord ++ tailWord_35586) baseStart_35586 baseEnd_35586 := by
    simpa [prefixWord, tailWord_35586, baseEnd_35586] using wordTrace_append hprefix tailTrace_35586
  have hstable : (prefixWord ++ tailWord_35586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35586).length < 2 ^ (prefixWord ++ tailWord_35586).sum := by decide
  have hdescent : baseEnd_35586 < baseStart_35586 := by decide
  rcases family_descends (prefixWord ++ tailWord_35586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35613 : List Nat := [1, 4, 2, 4, 1, 2, 1, 2, 3]
def baseStart_35613 : Nat := 118140960795 + 35613 * 2 ^ 59
def prefixEnd_35613 : Nat := 4983230072969 + 3 ^ 40 * 35613 * 2
def baseEnd_35613 : Nat := 16254743598821686821089

theorem tailTrace_35613 : CollatzResearch.WordTrace tailWord_35613 prefixEnd_35613 16254743598821686821089 := by
  unfold tailWord_35613
  simp only [CollatzResearch.WordTrace]
  refine ⟨1298912819987658061279493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 865941879991772040852995 1298912819987658061279493)
  ·
    refine ⟨243546153747685886489905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1298912819987658061279493 243546153747685886489905)
    ·
      refine ⟨182659615310764414867429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243546153747685886489905 182659615310764414867429)
      ·
        refine ⟨34248677870768327787643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182659615310764414867429 34248677870768327787643)
        ·
          refine ⟨51373016806152491681465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34248677870768327787643 51373016806152491681465)
          ·
            refine ⟨38529762604614368761099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51373016806152491681465 38529762604614368761099)
            ·
              refine ⟨57794643906921553141649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38529762604614368761099 57794643906921553141649)
              ·
                refine ⟨43345982930191164856237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57794643906921553141649 43345982930191164856237)
                ·
                  refine ⟨16254743598821686821089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43345982930191164856237 16254743598821686821089)
                  ·
                    rfl

theorem cell20_35613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_35613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35613 prefixEnd_35613 := by exact prefixLift 35613
  have htrace : WordTrace (prefixWord ++ tailWord_35613) baseStart_35613 baseEnd_35613 := by
    simpa [prefixWord, tailWord_35613, baseEnd_35613] using wordTrace_append hprefix tailTrace_35613
  have hstable : (prefixWord ++ tailWord_35613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35613).length < 2 ^ (prefixWord ++ tailWord_35613).sum := by decide
  have hdescent : baseEnd_35613 < baseStart_35613 := by decide
  rcases family_descends (prefixWord ++ tailWord_35613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35624 : List Nat := [2, 1, 5, 1, 1, 1, 4, 1, 4]
def baseStart_35624 : Nat := 118140960795 + 35624 * 2 ^ 59
def prefixEnd_35624 : Nat := 4983230072969 + 3 ^ 40 * 35624 * 2
def baseEnd_35624 : Nat := 16259764298554537454377

theorem tailTrace_35624 : CollatzResearch.WordTrace tailWord_35624 prefixEnd_35624 16259764298554537454377 := by
  unfold tailWord_35624
  simp only [CollatzResearch.WordTrace]
  refine ⟨649657011473903469964963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 866209348631871293286617 649657011473903469964963)
  ·
    refine ⟨974485517210855204947445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 649657011473903469964963 974485517210855204947445)
    ·
      refine ⟨91358017238517675463823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 974485517210855204947445 91358017238517675463823)
      ·
        refine ⟨137037025857776513195735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91358017238517675463823 137037025857776513195735)
        ·
          refine ⟨205555538786664769793603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137037025857776513195735 205555538786664769793603)
          ·
            refine ⟨308333308179997154690405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205555538786664769793603 308333308179997154690405)
            ·
              refine ⟨57812495283749466504451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 308333308179997154690405 57812495283749466504451)
              ·
                refine ⟨86718742925624199756677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57812495283749466504451 86718742925624199756677)
                ·
                  refine ⟨16259764298554537454377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86718742925624199756677 16259764298554537454377)
                  ·
                    rfl

theorem cell20_35624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_35624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35624 prefixEnd_35624 := by exact prefixLift 35624
  have htrace : WordTrace (prefixWord ++ tailWord_35624) baseStart_35624 baseEnd_35624 := by
    simpa [prefixWord, tailWord_35624, baseEnd_35624] using wordTrace_append hprefix tailTrace_35624
  have hstable : (prefixWord ++ tailWord_35624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35624).length < 2 ^ (prefixWord ++ tailWord_35624).sum := by decide
  have hdescent : baseEnd_35624 < baseStart_35624 := by decide
  rcases family_descends (prefixWord ++ tailWord_35624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35654 : List Nat := [6, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_35654 : Nat := 118140960795 + 35654 * 2 ^ 59
def prefixEnd_35654 : Nat := 4983230072969 + 3 ^ 40 * 35654 * 2
def baseEnd_35654 : Nat := 16273457116007766454255

theorem tailTrace_35654 : CollatzResearch.WordTrace tailWord_35654 prefixEnd_35654 16273457116007766454255 := by
  unfold tailWord_35654
  simp only [CollatzResearch.WordTrace]
  refine ⟨40637756651222564485063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 866938808559414709014677 40637756651222564485063)
  ·
    refine ⟨60956634976833846727595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40637756651222564485063 60956634976833846727595)
    ·
      refine ⟨91434952465250770091393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60956634976833846727595 91434952465250770091393)
      ·
        refine ⟨68576214348938077568545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91434952465250770091393 68576214348938077568545)
        ·
          refine ⟨51432160761703558176409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68576214348938077568545 51432160761703558176409)
          ·
            refine ⟨38574120571277668632307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51432160761703558176409 38574120571277668632307)
            ·
              refine ⟨57861180856916502948461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38574120571277668632307 57861180856916502948461)
              ·
                refine ⟨21697942821343688605673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57861180856916502948461 21697942821343688605673)
                ·
                  refine ⟨16273457116007766454255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21697942821343688605673 16273457116007766454255)
                  ·
                    rfl

theorem cell20_35654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_35654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35654 prefixEnd_35654 := by exact prefixLift 35654
  have htrace : WordTrace (prefixWord ++ tailWord_35654) baseStart_35654 baseEnd_35654 := by
    simpa [prefixWord, tailWord_35654, baseEnd_35654] using wordTrace_append hprefix tailTrace_35654
  have hstable : (prefixWord ++ tailWord_35654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35654).length < 2 ^ (prefixWord ++ tailWord_35654).sum := by decide
  have hdescent : baseEnd_35654 < baseStart_35654 := by decide
  rcases family_descends (prefixWord ++ tailWord_35654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35679 : List Nat := [1, 1, 2, 3, 1, 3, 5, 2, 2]
def baseStart_35679 : Nat := 118140960795 + 35679 * 2 ^ 59
def prefixEnd_35679 : Nat := 4983230072969 + 3 ^ 40 * 35679 * 2
def baseEnd_35679 : Nat := 16284867797218790620819

theorem tailTrace_35679 : CollatzResearch.WordTrace tailWord_35679 prefixEnd_35679 16284867797218790620819 := by
  unfold tailWord_35679
  simp only [CollatzResearch.WordTrace]
  refine ⟨1301320037748551333182091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 867546691832367555454727 1301320037748551333182091)
  ·
    refine ⟨1951980056622826999773137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1301320037748551333182091 1951980056622826999773137)
    ·
      refine ⟨1463985042467120249829853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1951980056622826999773137 1463985042467120249829853)
      ·
        refine ⟨548994390925170093686195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1463985042467120249829853 548994390925170093686195)
        ·
          refine ⟨823491586387755140529293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 548994390925170093686195 823491586387755140529293)
          ·
            refine ⟨308809344895408177698485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 823491586387755140529293 308809344895408177698485)
            ·
              refine ⟨28950876083944516659233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 308809344895408177698485 28950876083944516659233)
              ·
                refine ⟨21713157062958387494425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28950876083944516659233 21713157062958387494425)
                ·
                  refine ⟨16284867797218790620819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21713157062958387494425 16284867797218790620819)
                  ·
                    rfl

theorem cell20_35679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 2].length) (baseStart_35679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35679 prefixEnd_35679 := by exact prefixLift 35679
  have htrace : WordTrace (prefixWord ++ tailWord_35679) baseStart_35679 baseEnd_35679 := by
    simpa [prefixWord, tailWord_35679, baseEnd_35679] using wordTrace_append hprefix tailTrace_35679
  have hstable : (prefixWord ++ tailWord_35679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35679).length < 2 ^ (prefixWord ++ tailWord_35679).sum := by decide
  have hdescent : baseEnd_35679 < baseStart_35679 := by decide
  rcases family_descends (prefixWord ++ tailWord_35679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35730 : List Nat := [3, 2, 3, 2, 3, 1, 2, 2, 2]
def baseStart_35730 : Nat := 118140960795 + 35730 * 2 ^ 59
def prefixEnd_35730 : Nat := 4983230072969 + 3 ^ 40 * 35730 * 2
def baseEnd_35730 : Nat := 16308145586889279920611

theorem tailTrace_35730 : CollatzResearch.WordTrace tailWord_35730 prefixEnd_35730 16308145586889279920611 := by
  unfold tailWord_35730
  simp only [CollatzResearch.WordTrace]
  refine ⟨325795040140946760822161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 868786773709191362192429 325795040140946760822161)
  ·
    refine ⟨244346280105710070616621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 325795040140946760822161 244346280105710070616621)
    ·
      refine ⟨91629855039641276481233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244346280105710070616621 91629855039641276481233)
      ·
        refine ⟨68722391279730957360925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91629855039641276481233 68722391279730957360925)
        ·
          refine ⟨25770896729899109010347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68722391279730957360925 25770896729899109010347)
          ·
            refine ⟨38656345094848663515521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25770896729899109010347 38656345094848663515521)
            ·
              refine ⟨28992258821136497636641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38656345094848663515521 28992258821136497636641)
              ·
                refine ⟨21744194115852373227481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28992258821136497636641 21744194115852373227481)
                ·
                  refine ⟨16308145586889279920611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21744194115852373227481 16308145586889279920611)
                  ·
                    rfl

theorem cell20_35730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_35730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35730 prefixEnd_35730 := by exact prefixLift 35730
  have htrace : WordTrace (prefixWord ++ tailWord_35730) baseStart_35730 baseEnd_35730 := by
    simpa [prefixWord, tailWord_35730, baseEnd_35730] using wordTrace_append hprefix tailTrace_35730
  have hstable : (prefixWord ++ tailWord_35730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35730).length < 2 ^ (prefixWord ++ tailWord_35730).sum := by decide
  have hdescent : baseEnd_35730 < baseStart_35730 := by decide
  rcases family_descends (prefixWord ++ tailWord_35730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35745 : List Nat := [1, 2, 3, 4, 1, 1, 3, 5]
def baseStart_35745 : Nat := 118140960795 + 35745 * 2 ^ 59
def prefixEnd_35745 : Nat := 4983230072969 + 3 ^ 40 * 35745 * 2
def baseEnd_35745 : Nat := 5438330665205298140183

theorem tailTrace_35745 : CollatzResearch.WordTrace tailWord_35745 prefixEnd_35745 5438330665205298140183 := by
  unfold tailWord_35745
  simp only [CollatzResearch.WordTrace]
  refine ⟨1303727255509444605084689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 869151503672963070056459 1303727255509444605084689)
  ·
    refine ⟨977795441632083453813517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1303727255509444605084689 977795441632083453813517)
    ·
      refine ⟨366673290612031295180069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 977795441632083453813517 366673290612031295180069)
      ·
        refine ⟨68751241989755867846263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 366673290612031295180069 68751241989755867846263)
        ·
          refine ⟨103126862984633801769395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68751241989755867846263 103126862984633801769395)
          ·
            refine ⟨154690294476950702654093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103126862984633801769395 154690294476950702654093)
            ·
              refine ⟨58008860428856513495285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154690294476950702654093 58008860428856513495285)
              ·
                refine ⟨5438330665205298140183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58008860428856513495285 5438330665205298140183)
                ·
                  rfl

theorem cell20_35745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 5].length) (baseStart_35745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35745 prefixEnd_35745 := by exact prefixLift 35745
  have htrace : WordTrace (prefixWord ++ tailWord_35745) baseStart_35745 baseEnd_35745 := by
    simpa [prefixWord, tailWord_35745, baseEnd_35745] using wordTrace_append hprefix tailTrace_35745
  have hstable : (prefixWord ++ tailWord_35745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35745).length < 2 ^ (prefixWord ++ tailWord_35745).sum := by decide
  have hdescent : baseEnd_35745 < baseStart_35745 := by decide
  rcases family_descends (prefixWord ++ tailWord_35745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35776 : List Nat := [2, 1, 1, 2, 3, 3, 1, 5, 2]
def baseStart_35776 : Nat := 118140960795 + 35776 * 2 ^ 59
def prefixEnd_35776 : Nat := 4983230072969 + 3 ^ 40 * 35776 * 2
def baseEnd_35776 : Nat := 16329141240317564387089

theorem tailTrace_35776 : CollatzResearch.WordTrace tailWord_35776 prefixEnd_35776 16329141240317564387089 := by
  unfold tailWord_35776
  simp only [CollatzResearch.WordTrace]
  refine ⟨652428959198568449731591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 869905278931424599642121 652428959198568449731591)
  ·
    refine ⟨978643438797852674597387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 652428959198568449731591 978643438797852674597387)
    ·
      refine ⟨1467965158196779011896081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 978643438797852674597387 1467965158196779011896081)
      ·
        refine ⟨1100973868647584258922061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1467965158196779011896081 1100973868647584258922061)
        ·
          refine ⟨412865200742844097095773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1100973868647584258922061 412865200742844097095773)
          ·
            refine ⟨154824450278566536410915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 412865200742844097095773 154824450278566536410915)
            ·
              refine ⟨232236675417849804616373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154824450278566536410915 232236675417849804616373)
              ·
                refine ⟨21772188320423419182785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 232236675417849804616373 21772188320423419182785)
                ·
                  refine ⟨16329141240317564387089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21772188320423419182785 16329141240317564387089)
                  ·
                    rfl

theorem cell20_35776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 2].length) (baseStart_35776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35776 prefixEnd_35776 := by exact prefixLift 35776
  have htrace : WordTrace (prefixWord ++ tailWord_35776) baseStart_35776 baseEnd_35776 := by
    simpa [prefixWord, tailWord_35776, baseEnd_35776] using wordTrace_append hprefix tailTrace_35776
  have hstable : (prefixWord ++ tailWord_35776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35776).length < 2 ^ (prefixWord ++ tailWord_35776).sum := by decide
  have hdescent : baseEnd_35776 < baseStart_35776 := by decide
  rcases family_descends (prefixWord ++ tailWord_35776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35782 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_35782 : Nat := 118140960795 + 35782 * 2 ^ 59
def prefixEnd_35782 : Nat := 4983230072969 + 3 ^ 40 * 35782 * 2
def baseEnd_35782 : Nat := 16331879803808210187065

theorem tailTrace_35782 : CollatzResearch.WordTrace tailWord_35782 prefixEnd_35782 16331879803808210187065 := by
  unfold tailWord_35782
  simp only [CollatzResearch.WordTrace]
  refine ⟨40783648636731247630675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 870051170916933282787733 40783648636731247630675)
  ·
    refine ⟨61175472955096871446013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40783648636731247630675 61175472955096871446013)
    ·
      refine ⟨22940802358161326792255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61175472955096871446013 22940802358161326792255)
      ·
        refine ⟨34411203537241990188383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22940802358161326792255 34411203537241990188383)
        ·
          refine ⟨51616805305862985282575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34411203537241990188383 51616805305862985282575)
          ·
            refine ⟨77425207958794477923863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51616805305862985282575 77425207958794477923863)
            ·
              refine ⟨116137811938191716885795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77425207958794477923863 116137811938191716885795)
              ·
                refine ⟨174206717907287575328693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116137811938191716885795 174206717907287575328693)
                ·
                  refine ⟨16331879803808210187065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 174206717907287575328693 16331879803808210187065)
                  ·
                    rfl

theorem cell20_35782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_35782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35782 prefixEnd_35782 := by exact prefixLift 35782
  have htrace : WordTrace (prefixWord ++ tailWord_35782) baseStart_35782 baseEnd_35782 := by
    simpa [prefixWord, tailWord_35782, baseEnd_35782] using wordTrace_append hprefix tailTrace_35782
  have hstable : (prefixWord ++ tailWord_35782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35782).length < 2 ^ (prefixWord ++ tailWord_35782).sum := by decide
  have hdescent : baseEnd_35782 < baseStart_35782 := by decide
  rcases family_descends (prefixWord ++ tailWord_35782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35789 : List Nat := [1, 6, 3, 1, 1, 1, 2, 1, 4]
def baseStart_35789 : Nat := 118140960795 + 35789 * 2 ^ 59
def prefixEnd_35789 : Nat := 4983230072969 + 3 ^ 40 * 35789 * 2
def baseEnd_35789 : Nat := 16335074794547296953703

theorem tailTrace_35789 : CollatzResearch.WordTrace tailWord_35789 prefixEnd_35789 16335074794547296953703 := by
  unfold tailWord_35789
  simp only [CollatzResearch.WordTrace]
  refine ⟨1305332067350040119686421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 870221378233360079790947 1305332067350040119686421)
  ·
    refine ⟨61187440657033130610301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1305332067350040119686421 61187440657033130610301)
    ·
      refine ⟨22945290246387423978863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61187440657033130610301 22945290246387423978863)
      ·
        refine ⟨34417935369581135968295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22945290246387423978863 34417935369581135968295)
        ·
          refine ⟨51626903054371703952443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34417935369581135968295 51626903054371703952443)
          ·
            refine ⟨77440354581557555928665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51626903054371703952443 77440354581557555928665)
            ·
              refine ⟨58080265936168166946499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77440354581557555928665 58080265936168166946499)
              ·
                refine ⟨87120398904252250419749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58080265936168166946499 87120398904252250419749)
                ·
                  refine ⟨16335074794547296953703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87120398904252250419749 16335074794547296953703)
                  ·
                    rfl

theorem cell20_35789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_35789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35789 prefixEnd_35789 := by exact prefixLift 35789
  have htrace : WordTrace (prefixWord ++ tailWord_35789) baseStart_35789 baseEnd_35789 := by
    simpa [prefixWord, tailWord_35789, baseEnd_35789] using wordTrace_append hprefix tailTrace_35789
  have hstable : (prefixWord ++ tailWord_35789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35789).length < 2 ^ (prefixWord ++ tailWord_35789).sum := by decide
  have hdescent : baseEnd_35789 < baseStart_35789 := by decide
  rcases family_descends (prefixWord ++ tailWord_35789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35790 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_35790 : Nat := 118140960795 + 35790 * 2 ^ 59
def prefixEnd_35790 : Nat := 4983230072969 + 3 ^ 40 * 35790 * 2
def baseEnd_35790 : Nat := 16335531221795737920365

theorem tailTrace_35790 : CollatzResearch.WordTrace tailWord_35790 prefixEnd_35790 16335531221795737920365 := by
  unfold tailWord_35790
  simp only [CollatzResearch.WordTrace]
  refine ⟨163171067543302161309103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 870245693564278193648549 163171067543302161309103)
  ·
    refine ⟨244756601314953241963655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163171067543302161309103 244756601314953241963655)
    ·
      refine ⟨367134901972429862945483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244756601314953241963655 367134901972429862945483)
      ·
        refine ⟨550702352958644794418225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367134901972429862945483 550702352958644794418225)
        ·
          refine ⟨413026764718983595813669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 550702352958644794418225 413026764718983595813669)
          ·
            refine ⟨77442518384809424215063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 413026764718983595813669 77442518384809424215063)
            ·
              refine ⟨116163777577214136322595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77442518384809424215063 116163777577214136322595)
              ·
                refine ⟨174245666365821204483893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116163777577214136322595 174245666365821204483893)
                ·
                  refine ⟨16335531221795737920365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 174245666365821204483893 16335531221795737920365)
                  ·
                    rfl

theorem cell20_35790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_35790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35790 prefixEnd_35790 := by exact prefixLift 35790
  have htrace : WordTrace (prefixWord ++ tailWord_35790) baseStart_35790 baseEnd_35790 := by
    simpa [prefixWord, tailWord_35790, baseEnd_35790] using wordTrace_append hprefix tailTrace_35790
  have hstable : (prefixWord ++ tailWord_35790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35790).length < 2 ^ (prefixWord ++ tailWord_35790).sum := by decide
  have hdescent : baseEnd_35790 < baseStart_35790 := by decide
  rcases family_descends (prefixWord ++ tailWord_35790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35838 : List Nat := [4, 2, 2, 2, 2, 2, 6]
def baseStart_35838 : Nat := 118140960795 + 35838 * 2 ^ 59
def prefixEnd_35838 : Nat := 4983230072969 + 3 ^ 40 * 35838 * 2
def baseEnd_35838 : Nat := 1817493303302322702241

theorem tailTrace_35838 : CollatzResearch.WordTrace tailWord_35838 prefixEnd_35838 1817493303302322702241 := by
  unfold tailWord_35838
  simp only [CollatzResearch.WordTrace]
  refine ⟨163389905521565186027521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 871412829448347658813445 163389905521565186027521)
  ·
    refine ⟨122542429141173889520641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163389905521565186027521 122542429141173889520641)
    ·
      refine ⟨91906821855880417140481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122542429141173889520641 91906821855880417140481)
      ·
        refine ⟨68930116391910312855361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91906821855880417140481 68930116391910312855361)
        ·
          refine ⟨51697587293932734641521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68930116391910312855361 51697587293932734641521)
          ·
            refine ⟨38773190470449550981141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51697587293932734641521 38773190470449550981141)
            ·
              refine ⟨1817493303302322702241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38773190470449550981141 1817493303302322702241)
              ·
                rfl

theorem cell20_35838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 6].length) (baseStart_35838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35838 prefixEnd_35838 := by exact prefixLift 35838
  have htrace : WordTrace (prefixWord ++ tailWord_35838) baseStart_35838 baseEnd_35838 := by
    simpa [prefixWord, tailWord_35838, baseEnd_35838] using wordTrace_append hprefix tailTrace_35838
  have hstable : (prefixWord ++ tailWord_35838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35838).length < 2 ^ (prefixWord ++ tailWord_35838).sum := by decide
  have hdescent : baseEnd_35838 < baseStart_35838 := by decide
  rcases family_descends (prefixWord ++ tailWord_35838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35852 : List Nat := [2, 2, 1, 2, 3, 4, 1, 1, 4]
def baseStart_35852 : Nat := 118140960795 + 35852 * 2 ^ 59
def prefixEnd_35852 : Nat := 4983230072969 + 3 ^ 40 * 35852 * 2
def baseEnd_35852 : Nat := 16363829711199077853445

theorem tailTrace_35852 : CollatzResearch.WordTrace tailWord_35852 prefixEnd_35852 16363829711199077853445 := by
  unfold tailWord_35852
  simp only [CollatzResearch.WordTrace]
  refine ⟨653814933060900939614905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 871753244081201252819873 653814933060900939614905)
  ·
    refine ⟨490361199795675704711179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 653814933060900939614905 490361199795675704711179)
    ·
      refine ⟨735541799693513557066769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 490361199795675704711179 735541799693513557066769)
      ·
        refine ⟨551656349770135167800077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 735541799693513557066769 551656349770135167800077)
        ·
          refine ⟨206871131163800687925029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 551656349770135167800077 206871131163800687925029)
          ·
            refine ⟨38788337093212628985943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 206871131163800687925029 38788337093212628985943)
            ·
              refine ⟨58182505639818943478915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38788337093212628985943 58182505639818943478915)
              ·
                refine ⟨87273758459728415218373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58182505639818943478915 87273758459728415218373)
                ·
                  refine ⟨16363829711199077853445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87273758459728415218373 16363829711199077853445)
                  ·
                    rfl

theorem cell20_35852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_35852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35852 prefixEnd_35852 := by exact prefixLift 35852
  have htrace : WordTrace (prefixWord ++ tailWord_35852) baseStart_35852 baseEnd_35852 := by
    simpa [prefixWord, tailWord_35852, baseEnd_35852] using wordTrace_append hprefix tailTrace_35852
  have hstable : (prefixWord ++ tailWord_35852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35852).length < 2 ^ (prefixWord ++ tailWord_35852).sum := by decide
  have hdescent : baseEnd_35852 < baseStart_35852 := by decide
  rcases family_descends (prefixWord ++ tailWord_35852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35866 : List Nat := [3, 1, 1, 3, 1, 2, 3, 3, 3]
def baseStart_35866 : Nat := 118140960795 + 35866 * 2 ^ 59
def prefixEnd_35866 : Nat := 4983230072969 + 3 ^ 40 * 35866 * 2
def baseEnd_35866 : Nat := 16370219692677251386721

theorem tailTrace_35866 : CollatzResearch.WordTrace tailWord_35866 prefixEnd_35866 16370219692677251386721 := by
  unfold tailWord_35866
  simp only [CollatzResearch.WordTrace]
  refine ⟨327035122017770567559863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 872093658714054846826301 327035122017770567559863)
  ·
    refine ⟨490552683026655851339795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 327035122017770567559863 490552683026655851339795)
    ·
      refine ⟨735829024539983777009693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 490552683026655851339795 735829024539983777009693)
      ·
        refine ⟨275935884202493916378635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 735829024539983777009693 275935884202493916378635)
        ·
          refine ⟨413903826303740874567953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275935884202493916378635 413903826303740874567953)
          ·
            refine ⟨310427869727805655925965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 413903826303740874567953 310427869727805655925965)
            ·
              refine ⟨116410451147927120972237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 310427869727805655925965 116410451147927120972237)
              ·
                refine ⟨43653919180472670364589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116410451147927120972237 43653919180472670364589)
                ·
                  refine ⟨16370219692677251386721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43653919180472670364589 16370219692677251386721)
                  ·
                    rfl

theorem cell20_35866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_35866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35866 prefixEnd_35866 := by exact prefixLift 35866
  have htrace : WordTrace (prefixWord ++ tailWord_35866) baseStart_35866 baseEnd_35866 := by
    simpa [prefixWord, tailWord_35866, baseEnd_35866] using wordTrace_append hprefix tailTrace_35866
  have hstable : (prefixWord ++ tailWord_35866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35866).length < 2 ^ (prefixWord ++ tailWord_35866).sum := by decide
  have hdescent : baseEnd_35866 < baseStart_35866 := by decide
  rcases family_descends (prefixWord ++ tailWord_35866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35890 : List Nat := [3, 2, 1, 1, 2, 2, 2, 5, 2]
def baseStart_35890 : Nat := 118140960795 + 35890 * 2 ^ 59
def prefixEnd_35890 : Nat := 4983230072969 + 3 ^ 40 * 35890 * 2
def baseEnd_35890 : Nat := 16381173946639834586623

theorem tailTrace_35890 : CollatzResearch.WordTrace tailWord_35890 prefixEnd_35890 16381173946639834586623 := by
  unfold tailWord_35890
  simp only [CollatzResearch.WordTrace]
  refine ⟨327253959996033592278281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 872677226656089579408749 327253959996033592278281)
  ·
    refine ⟨245440469997025194208711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 327253959996033592278281 245440469997025194208711)
    ·
      refine ⟨368160704995537791313067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245440469997025194208711 368160704995537791313067)
      ·
        refine ⟨552241057493306686969601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368160704995537791313067 552241057493306686969601)
        ·
          refine ⟨414180793119980015227201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 552241057493306686969601 414180793119980015227201)
          ·
            refine ⟨310635594839985011420401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 414180793119980015227201 310635594839985011420401)
            ·
              refine ⟨232976696129988758565301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310635594839985011420401 232976696129988758565301)
              ·
                refine ⟨21841565262186446115497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 232976696129988758565301 21841565262186446115497)
                ·
                  refine ⟨16381173946639834586623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21841565262186446115497 16381173946639834586623)
                  ·
                    rfl

theorem cell20_35890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_35890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35890 prefixEnd_35890 := by exact prefixLift 35890
  have htrace : WordTrace (prefixWord ++ tailWord_35890) baseStart_35890 baseEnd_35890 := by
    simpa [prefixWord, tailWord_35890, baseEnd_35890] using wordTrace_append hprefix tailTrace_35890
  have hstable : (prefixWord ++ tailWord_35890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35890).length < 2 ^ (prefixWord ++ tailWord_35890).sum := by decide
  have hdescent : baseEnd_35890 < baseStart_35890 := by decide
  rcases family_descends (prefixWord ++ tailWord_35890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35904 : List Nat := [2, 1, 1, 2, 2, 3, 4, 2, 3]
def baseStart_35904 : Nat := 118140960795 + 35904 * 2 ^ 59
def prefixEnd_35904 : Nat := 4983230072969 + 3 ^ 40 * 35904 * 2
def baseEnd_35904 : Nat := 16387563928118008119899

theorem tailTrace_35904 : CollatzResearch.WordTrace tailWord_35904 prefixEnd_35904 16387563928118008119899 := by
  unfold tailWord_35904
  simp only [CollatzResearch.WordTrace]
  refine ⟨654763230966707380061383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 873017641288943173415177 654763230966707380061383)
  ·
    refine ⟨982144846450061070092075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 654763230966707380061383 982144846450061070092075)
    ·
      refine ⟨1473217269675091605138113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 982144846450061070092075 1473217269675091605138113)
      ·
        refine ⟨1104912952256318703853585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1473217269675091605138113 1104912952256318703853585)
        ·
          refine ⟨828684714192239027890189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1104912952256318703853585 828684714192239027890189)
          ·
            refine ⟨310756767822089635458821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 828684714192239027890189 310756767822089635458821)
            ·
              refine ⟨58266893966641806648529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 310756767822089635458821 58266893966641806648529)
              ·
                refine ⟨43700170474981354986397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58266893966641806648529 43700170474981354986397)
                ·
                  refine ⟨16387563928118008119899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43700170474981354986397 16387563928118008119899)
                  ·
                    rfl

theorem cell20_35904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 3].length) (baseStart_35904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35904 prefixEnd_35904 := by exact prefixLift 35904
  have htrace : WordTrace (prefixWord ++ tailWord_35904) baseStart_35904 baseEnd_35904 := by
    simpa [prefixWord, tailWord_35904, baseEnd_35904] using wordTrace_append hprefix tailTrace_35904
  have hstable : (prefixWord ++ tailWord_35904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35904).length < 2 ^ (prefixWord ++ tailWord_35904).sum := by decide
  have hdescent : baseEnd_35904 < baseStart_35904 := by decide
  rcases family_descends (prefixWord ++ tailWord_35904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35976 : List Nat := [2, 1, 3, 4, 2, 1, 3, 1, 3]
def baseStart_35976 : Nat := 118140960795 + 35976 * 2 ^ 59
def prefixEnd_35976 : Nat := 4983230072969 + 3 ^ 40 * 35976 * 2
def baseEnd_35976 : Nat := 16420426690005757719605

theorem tailTrace_35976 : CollatzResearch.WordTrace tailWord_35976 prefixEnd_35976 16420426690005757719605 := by
  unfold tailWord_35976
  simp only [CollatzResearch.WordTrace]
  refine ⟨656076258836285528371891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 874768345115047371162521 656076258836285528371891)
  ·
    refine ⟨984114388254428292557837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 656076258836285528371891 984114388254428292557837)
    ·
      refine ⟨369042895595410609709189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 984114388254428292557837 369042895595410609709189)
      ·
        refine ⟨69195542924139489320473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 369042895595410609709189 69195542924139489320473)
        ·
          refine ⟨51896657193104616990355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69195542924139489320473 51896657193104616990355)
          ·
            refine ⟨77844985789656925485533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51896657193104616990355 77844985789656925485533)
            ·
              refine ⟨29191869671121347057075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77844985789656925485533 29191869671121347057075)
              ·
                refine ⟨43787804506682020585613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29191869671121347057075 43787804506682020585613)
                ·
                  refine ⟨16420426690005757719605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43787804506682020585613 16420426690005757719605)
                  ·
                    rfl

theorem cell20_35976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 3].length) (baseStart_35976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_35976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_35976 prefixEnd_35976 := by exact prefixLift 35976
  have htrace : WordTrace (prefixWord ++ tailWord_35976) baseStart_35976 baseEnd_35976 := by
    simpa [prefixWord, tailWord_35976, baseEnd_35976] using wordTrace_append hprefix tailTrace_35976
  have hstable : (prefixWord ++ tailWord_35976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35976).length < 2 ^ (prefixWord ++ tailWord_35976).sum := by decide
  have hdescent : baseEnd_35976 < baseStart_35976 := by decide
  rcases family_descends (prefixWord ++ tailWord_35976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36001 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 7]
def baseStart_36001 : Nat := 118140960795 + 36001 * 2 ^ 59
def prefixEnd_36001 : Nat := 4983230072969 + 3 ^ 40 * 36001 * 2
def baseEnd_36001 : Nat := 16431837371216781886169

theorem tailTrace_36001 : CollatzResearch.WordTrace tailWord_36001 prefixEnd_36001 16431837371216781886169 := by
  unfold tailWord_36001
  simp only [CollatzResearch.WordTrace]
  refine ⟨1313064342582000326403857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 875376228388000217602571 1313064342582000326403857)
  ·
    refine ⟨984798256936500244802893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1313064342582000326403857 984798256936500244802893)
    ·
      refine ⟨369299346351187591801085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 984798256936500244802893 369299346351187591801085)
      ·
        refine ⟨138487254881695346925407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 369299346351187591801085 138487254881695346925407)
        ·
          refine ⟨207730882322543020388111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138487254881695346925407 207730882322543020388111)
          ·
            refine ⟨311596323483814530582167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207730882322543020388111 311596323483814530582167)
            ·
              refine ⟨467394485225721795873251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311596323483814530582167 467394485225721795873251)
              ·
                refine ⟨701091727838582693809877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 467394485225721795873251 701091727838582693809877)
                ·
                  refine ⟨16431837371216781886169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 701091727838582693809877 16431837371216781886169)
                  ·
                    rfl

theorem cell20_36001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_36001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36001 prefixEnd_36001 := by exact prefixLift 36001
  have htrace : WordTrace (prefixWord ++ tailWord_36001) baseStart_36001 baseEnd_36001 := by
    simpa [prefixWord, tailWord_36001, baseEnd_36001] using wordTrace_append hprefix tailTrace_36001
  have hstable : (prefixWord ++ tailWord_36001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36001).length < 2 ^ (prefixWord ++ tailWord_36001).sum := by decide
  have hdescent : baseEnd_36001 < baseStart_36001 := by decide
  rcases family_descends (prefixWord ++ tailWord_36001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36015 : List Nat := [1, 1, 2, 1, 2, 3, 10]
def baseStart_36015 : Nat := 118140960795 + 36015 * 2 ^ 59
def prefixEnd_36015 : Nat := 4983230072969 + 3 ^ 40 * 36015 * 2
def baseEnd_36015 : Nat := 1826469705854995046605

theorem tailTrace_36015 : CollatzResearch.WordTrace tailWord_36015 prefixEnd_36015 1826469705854995046605 := by
  unfold tailWord_36015
  simp only [CollatzResearch.WordTrace]
  refine ⟨1313574964531280717413499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 875716643020853811608999 1313574964531280717413499)
  ·
    refine ⟨1970362446796921076120249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1313574964531280717413499 1970362446796921076120249)
    ·
      refine ⟨1477771835097690807090187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1970362446796921076120249 1477771835097690807090187)
      ·
        refine ⟨2216657752646536210635281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1477771835097690807090187 2216657752646536210635281)
        ·
          refine ⟨1662493314484902157976461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2216657752646536210635281 1662493314484902157976461)
          ·
            refine ⟨623434992931838309241173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1662493314484902157976461 623434992931838309241173)
            ·
              refine ⟨1826469705854995046605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 623434992931838309241173 1826469705854995046605)
              ·
                rfl

theorem cell20_36015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 10].length) (baseStart_36015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36015 prefixEnd_36015 := by exact prefixLift 36015
  have htrace : WordTrace (prefixWord ++ tailWord_36015) baseStart_36015 baseEnd_36015 := by
    simpa [prefixWord, tailWord_36015, baseEnd_36015] using wordTrace_append hprefix tailTrace_36015
  have hstable : (prefixWord ++ tailWord_36015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36015).length < 2 ^ (prefixWord ++ tailWord_36015).sum := by decide
  have hdescent : baseEnd_36015 < baseStart_36015 := by decide
  rcases family_descends (prefixWord ++ tailWord_36015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36025 : List Nat := [1, 2, 1, 4, 1, 3, 3, 1, 4]
def baseStart_36025 : Nat := 118140960795 + 36025 * 2 ^ 59
def prefixEnd_36025 : Nat := 4983230072969 + 3 ^ 40 * 36025 * 2
def baseEnd_36025 : Nat := 16442791625179365086071

theorem tailTrace_36025 : CollatzResearch.WordTrace tailWord_36025 prefixEnd_36025 16442791625179365086071 := by
  unfold tailWord_36025
  simp only [CollatzResearch.WordTrace]
  refine ⟨1313939694495052425277529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 875959796330034950185019 1313939694495052425277529)
  ·
    refine ⟨985454770871289318958147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1313939694495052425277529 985454770871289318958147)
    ·
      refine ⟨1478182156306933978437221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 985454770871289318958147 1478182156306933978437221)
      ·
        refine ⟨277159154307550120956979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1478182156306933978437221 277159154307550120956979)
        ·
          refine ⟨415738731461325181435469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277159154307550120956979 415738731461325181435469)
          ·
            refine ⟨155902024297996943038301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 415738731461325181435469 155902024297996943038301)
            ·
              refine ⟨58463259111748853639363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155902024297996943038301 58463259111748853639363)
              ·
                refine ⟨87694888667623280459045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58463259111748853639363 87694888667623280459045)
                ·
                  refine ⟨16442791625179365086071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87694888667623280459045 16442791625179365086071)
                  ·
                    rfl

theorem cell20_36025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_36025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36025 prefixEnd_36025 := by exact prefixLift 36025
  have htrace : WordTrace (prefixWord ++ tailWord_36025) baseStart_36025 baseEnd_36025 := by
    simpa [prefixWord, tailWord_36025, baseEnd_36025] using wordTrace_append hprefix tailTrace_36025
  have hstable : (prefixWord ++ tailWord_36025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36025).length < 2 ^ (prefixWord ++ tailWord_36025).sum := by decide
  have hdescent : baseEnd_36025 < baseStart_36025 := by decide
  rcases family_descends (prefixWord ++ tailWord_36025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
