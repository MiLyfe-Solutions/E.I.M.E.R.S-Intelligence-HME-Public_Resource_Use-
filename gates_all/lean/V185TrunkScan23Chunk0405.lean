import V185TrunkScan23Chunk0404

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2394801 : List Nat := [1, 2, 2, 6, 2, 1, 1, 1, 7]
def baseStart_2394801 : Nat := 118140960795 + 2394801 * 2 ^ 59
def prefixEnd_2394801 : Nat := 4983230072969 + 3 ^ 40 * 2394801 * 2
def baseEnd_2394801 : Nat := 136631553874221118197113

theorem tailTrace_2394801 : CollatzResearch.WordTrace tailWord_2394801 prefixEnd_2394801 136631553874221118197113 := by
  unfold tailWord_2394801
  simp only [CollatzResearch.WordTrace]
  refine ⟨87345568197052451293800257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58230378798034967529200171 87345568197052451293800257)
  ·
    refine ⟨65509176147789338470350193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87345568197052451293800257 65509176147789338470350193)
    ·
      refine ⟨49131882110842003852762645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65509176147789338470350193 49131882110842003852762645)
      ·
        refine ⟨2303056973945718930598249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 49131882110842003852762645 2303056973945718930598249)
        ·
          refine ⟨1727292730459289197948687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2303056973945718930598249 1727292730459289197948687)
          ·
            refine ⟨2590939095688933796923031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1727292730459289197948687 2590939095688933796923031)
            ·
              refine ⟨3886408643533400695384547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2590939095688933796923031 3886408643533400695384547)
              ·
                refine ⟨5829612965300101043076821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3886408643533400695384547 5829612965300101043076821)
                ·
                  refine ⟨136631553874221118197113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5829612965300101043076821 136631553874221118197113)
                  ·
                    rfl

theorem cell23_2394801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 7].length) (baseStart_2394801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394801 prefixEnd_2394801 := by exact prefixLift 2394801
  have htrace : WordTrace (prefixWord ++ tailWord_2394801) baseStart_2394801 baseEnd_2394801 := by
    simpa [prefixWord, tailWord_2394801, baseEnd_2394801] using wordTrace_append hprefix tailTrace_2394801
  have hstable : (prefixWord ++ tailWord_2394801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394801).length < 2 ^ (prefixWord ++ tailWord_2394801).sum := by decide
  have hdescent : baseEnd_2394801 < baseStart_2394801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394807 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 5]
def baseStart_2394807 : Nat := 118140960795 + 2394807 * 2 ^ 59
def prefixEnd_2394807 : Nat := 4983230072969 + 3 ^ 40 * 2394807 * 2
def baseEnd_2394807 : Nat := 1229687065751917040298989

theorem tailTrace_2394807 : CollatzResearch.WordTrace tailWord_2394807 prefixEnd_2394807 1229687065751917040298989 := by
  unfold tailWord_2394807
  simp only [CollatzResearch.WordTrace]
  refine ⟨87345787035030714318518675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58230524690020476212345783 87345787035030714318518675)
  ·
    refine ⟨131018680552546071477778013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87345787035030714318518675 131018680552546071477778013)
    ·
      refine ⟨49132005207204776804166755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131018680552546071477778013 49132005207204776804166755)
      ·
        refine ⟨73698007810807165206250133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49132005207204776804166755 73698007810807165206250133)
        ·
          refine ⟨3454594116131585869042975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 73698007810807165206250133 3454594116131585869042975)
          ·
            refine ⟨5181891174197378803564463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3454594116131585869042975 5181891174197378803564463)
            ·
              refine ⟨7772836761296068205346695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5181891174197378803564463 7772836761296068205346695)
              ·
                refine ⟨11659255141944102308020043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7772836761296068205346695 11659255141944102308020043)
                ·
                  refine ⟨17488882712916153462030065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11659255141944102308020043 17488882712916153462030065)
                  ·
                    refine ⟨13116662034687115096522549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17488882712916153462030065 13116662034687115096522549)
                    ·
                      refine ⟨1229687065751917040298989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13116662034687115096522549 1229687065751917040298989)
                      ·
                        rfl

theorem cell23_2394807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 5].length) (baseStart_2394807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394807 prefixEnd_2394807 := by exact prefixLift 2394807
  have htrace : WordTrace (prefixWord ++ tailWord_2394807) baseStart_2394807 baseEnd_2394807 := by
    simpa [prefixWord, tailWord_2394807, baseEnd_2394807] using wordTrace_append hprefix tailTrace_2394807
  have hstable : (prefixWord ++ tailWord_2394807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394807).length < 2 ^ (prefixWord ++ tailWord_2394807).sum := by decide
  have hdescent : baseEnd_2394807 < baseStart_2394807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394860 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 6]
def baseStart_2394860 : Nat := 118140960795 + 2394860 * 2 ^ 59
def prefixEnd_2394860 : Nat := 4983230072969 + 3 ^ 40 * 2394860 * 2
def baseEnd_2394860 : Nat := 1229714280226605332936245

theorem tailTrace_2394860 : CollatzResearch.WordTrace tailWord_2394860 prefixEnd_2394860 1229714280226605332936245 := by
  unfold tailWord_2394860
  simp only [CollatzResearch.WordTrace]
  refine ⟨43673860051919352185099017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58231813402559136246798689 43673860051919352185099017)
  ·
    refine ⟨32755395038939514138824263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43673860051919352185099017 32755395038939514138824263)
    ·
      refine ⟨49133092558409271208236395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32755395038939514138824263 49133092558409271208236395)
      ·
        refine ⟨73699638837613906812354593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49133092558409271208236395 73699638837613906812354593)
        ·
          refine ⟨55274729128210430109265945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73699638837613906812354593 55274729128210430109265945)
          ·
            refine ⟨41456046846157822581949459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55274729128210430109265945 41456046846157822581949459)
            ·
              refine ⟨62184070269236733872924189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41456046846157822581949459 62184070269236733872924189)
              ·
                refine ⟨23319026350963775202346571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62184070269236733872924189 23319026350963775202346571)
                ·
                  refine ⟨34978539526445662803519857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23319026350963775202346571 34978539526445662803519857)
                  ·
                    refine ⟨26233904644834247102639893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34978539526445662803519857 26233904644834247102639893)
                    ·
                      refine ⟨1229714280226605332936245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26233904644834247102639893 1229714280226605332936245)
                      ·
                        rfl

theorem cell23_2394860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_2394860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394860 prefixEnd_2394860 := by exact prefixLift 2394860
  have htrace : WordTrace (prefixWord ++ tailWord_2394860) baseStart_2394860 baseEnd_2394860 := by
    simpa [prefixWord, tailWord_2394860, baseEnd_2394860] using wordTrace_append hprefix tailTrace_2394860
  have hstable : (prefixWord ++ tailWord_2394860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394860).length < 2 ^ (prefixWord ++ tailWord_2394860).sum := by decide
  have hdescent : baseEnd_2394860 < baseStart_2394860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394861 : List Nat := [1, 5, 1, 2, 1, 1, 3, 4, 1, 4]
def baseStart_2394861 : Nat := 118140960795 + 2394861 * 2 ^ 59
def prefixEnd_2394861 : Nat := 4983230072969 + 3 ^ 40 * 2394861 * 2
def baseEnd_2394861 : Nat := 409904931235753276341247

theorem tailTrace_2394861 : CollatzResearch.WordTrace tailWord_2394861 prefixEnd_2394861 409904931235753276341247 := by
  unfold tailWord_2394861
  simp only [CollatzResearch.WordTrace]
  refine ⟨87347756576835081540984437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58231837717890054360656291 87347756576835081540984437)
  ·
    refine ⟨8188852179078288894467291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87347756576835081540984437 8188852179078288894467291)
    ·
      refine ⟨12283278268617433341700937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8188852179078288894467291 12283278268617433341700937)
      ·
        refine ⟨9212458701463075006275703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12283278268617433341700937 9212458701463075006275703)
        ·
          refine ⟨13818688052194612509413555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9212458701463075006275703 13818688052194612509413555)
          ·
            refine ⟨20728032078291918764120333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13818688052194612509413555 20728032078291918764120333)
            ·
              refine ⟨7773012029359469536545125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20728032078291918764120333 7773012029359469536545125)
              ·
                refine ⟨1457439755504900538102211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7773012029359469536545125 1457439755504900538102211)
                ·
                  refine ⟨2186159633257350807153317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1457439755504900538102211 2186159633257350807153317)
                  ·
                    refine ⟨409904931235753276341247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2186159633257350807153317 409904931235753276341247)
                    ·
                      rfl

theorem cell23_2394861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_2394861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394861 prefixEnd_2394861 := by exact prefixLift 2394861
  have htrace : WordTrace (prefixWord ++ tailWord_2394861) baseStart_2394861 baseEnd_2394861 := by
    simpa [prefixWord, tailWord_2394861, baseEnd_2394861] using wordTrace_append hprefix tailTrace_2394861
  have hstable : (prefixWord ++ tailWord_2394861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394861).length < 2 ^ (prefixWord ++ tailWord_2394861).sum := by decide
  have hdescent : baseEnd_2394861 < baseStart_2394861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394964 : List Nat := [2, 4, 1, 1, 4, 2, 9]
def baseStart_2394964 : Nat := 118140960795 + 2394964 * 2 ^ 59
def prefixEnd_2394964 : Nat := 4983230072969 + 3 ^ 40 * 2394964 * 2
def baseEnd_2394964 : Nat := 15182317064378678099207

theorem tailTrace_2394964 : CollatzResearch.WordTrace tailWord_2394964 prefixEnd_2394964 15182317064378678099207 := by
  unfold tailWord_2394964
  simp only [CollatzResearch.WordTrace]
  refine ⟨43675756647730965065991973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58234342196974620087989297 43675756647730965065991973)
  ·
    refine ⟨8189204371449555949873495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43675756647730965065991973 8189204371449555949873495)
    ·
      refine ⟨12283806557174333924810243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8189204371449555949873495 12283806557174333924810243)
      ·
        refine ⟨18425709835761500887215365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12283806557174333924810243 18425709835761500887215365)
        ·
          refine ⟨3454820594205281416352881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18425709835761500887215365 3454820594205281416352881)
          ·
            refine ⟨2591115445653961062264661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3454820594205281416352881 2591115445653961062264661)
            ·
              refine ⟨15182317064378678099207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2591115445653961062264661 15182317064378678099207)
              ·
                rfl

theorem cell23_2394964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 9].length) (baseStart_2394964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394964 prefixEnd_2394964 := by exact prefixLift 2394964
  have htrace : WordTrace (prefixWord ++ tailWord_2394964) baseStart_2394964 baseEnd_2394964 := by
    simpa [prefixWord, tailWord_2394964, baseEnd_2394964] using wordTrace_append hprefix tailTrace_2394964
  have hstable : (prefixWord ++ tailWord_2394964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394964).length < 2 ^ (prefixWord ++ tailWord_2394964).sum := by decide
  have hdescent : baseEnd_2394964 < baseStart_2394964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394975 : List Nat := [1, 1, 2, 3, 1, 3, 5, 2, 1, 2, 2]
def baseStart_2394975 : Nat := 118140960795 + 2394975 * 2 ^ 59
def prefixEnd_2394975 : Nat := 4983230072969 + 3 ^ 40 * 2394975 * 2
def baseEnd_2394975 : Nat := 1229773330501872382998217

theorem tailTrace_2394975 : CollatzResearch.WordTrace tailWord_2394975 prefixEnd_2394975 1229773330501872382998217 := by
  unfold tailWord_2394975
  simp only [CollatzResearch.WordTrace]
  refine ⟨87351914498422079010634379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58234609665614719340422919 87351914498422079010634379)
  ·
    refine ⟨131027871747633118515951569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87351914498422079010634379 131027871747633118515951569)
    ·
      refine ⟨98270903810724838886963677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131027871747633118515951569 98270903810724838886963677)
      ·
        refine ⟨36851588929021814582611379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98270903810724838886963677 36851588929021814582611379)
        ·
          refine ⟨55277383393532721873917069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36851588929021814582611379 55277383393532721873917069)
          ·
            refine ⟨20729018772574770702718901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55277383393532721873917069 20729018772574770702718901)
            ·
              refine ⟨1943345509928884753379897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20729018772574770702718901 1943345509928884753379897)
              ·
                refine ⟨1457509132446663565034923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1943345509928884753379897 1457509132446663565034923)
                ·
                  refine ⟨2186263698669995347552385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1457509132446663565034923 2186263698669995347552385)
                  ·
                    refine ⟨1639697774002496510664289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2186263698669995347552385 1639697774002496510664289)
                    ·
                      refine ⟨1229773330501872382998217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1639697774002496510664289 1229773330501872382998217)
                      ·
                        rfl

theorem cell23_2394975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 1, 2, 2].length) (baseStart_2394975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394975 prefixEnd_2394975 := by exact prefixLift 2394975
  have htrace : WordTrace (prefixWord ++ tailWord_2394975) baseStart_2394975 baseEnd_2394975 := by
    simpa [prefixWord, tailWord_2394975, baseEnd_2394975] using wordTrace_append hprefix tailTrace_2394975
  have hstable : (prefixWord ++ tailWord_2394975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394975).length < 2 ^ (prefixWord ++ tailWord_2394975).sum := by decide
  have hdescent : baseEnd_2394975 < baseStart_2394975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395001 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 3, 3, 2]
def baseStart_2395001 : Nat := 118140960795 + 2395001 * 2 ^ 59
def prefixEnd_2395001 : Nat := 4983230072969 + 3 ^ 40 * 2395001 * 2
def baseEnd_2395001 : Nat := 1229786680998889281273097

theorem tailTrace_2395001 : CollatzResearch.WordTrace tailWord_2395001 prefixEnd_2395001 1229786680998889281273097 := by
  unfold tailWord_2395001
  simp only [CollatzResearch.WordTrace]
  refine ⟨87352862796327885451080857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58235241864218590300720571 87352862796327885451080857)
  ·
    refine ⟨65514647097245914088310643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87352862796327885451080857 65514647097245914088310643)
    ·
      refine ⟨98271970645868871132465965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65514647097245914088310643 98271970645868871132465965)
      ·
        refine ⟨36851988992200826674674737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98271970645868871132465965 36851988992200826674674737)
        ·
          refine ⟨27638991744150620006006053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36851988992200826674674737 27638991744150620006006053)
          ·
            refine ⟨5182310952028241251126135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27638991744150620006006053 5182310952028241251126135)
            ·
              refine ⟨7773466428042361876689203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5182310952028241251126135 7773466428042361876689203)
              ·
                refine ⟨11660199642063542815033805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7773466428042361876689203 11660199642063542815033805)
                ·
                  refine ⟨4372574865773828555637677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11660199642063542815033805 4372574865773828555637677)
                  ·
                    refine ⟨1639715574665185708364129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4372574865773828555637677 1639715574665185708364129)
                    ·
                      refine ⟨1229786680998889281273097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1639715574665185708364129 1229786680998889281273097)
                      ·
                        rfl

theorem cell23_2395001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 3, 2].length) (baseStart_2395001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395001 prefixEnd_2395001 := by exact prefixLift 2395001
  have htrace : WordTrace (prefixWord ++ tailWord_2395001) baseStart_2395001 baseEnd_2395001 := by
    simpa [prefixWord, tailWord_2395001, baseEnd_2395001] using wordTrace_append hprefix tailTrace_2395001
  have hstable : (prefixWord ++ tailWord_2395001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395001).length < 2 ^ (prefixWord ++ tailWord_2395001).sum := by decide
  have hdescent : baseEnd_2395001 < baseStart_2395001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395026 : List Nat := [3, 2, 3, 2, 3, 1, 2, 2, 1, 2, 2]
def baseStart_2395026 : Nat := 118140960795 + 2395026 * 2 ^ 59
def prefixEnd_2395026 : Nat := 4983230072969 + 3 ^ 40 * 2395026 * 2
def baseEnd_2395026 : Nat := 1229799518015251683460483

theorem tailTrace_2395026 : CollatzResearch.WordTrace tailWord_2395026 prefixEnd_2395026 1229799518015251683460483 := by
  unfold tailWord_2395026
  simp only [CollatzResearch.WordTrace]
  refine ⟨21838443655309328680185233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58235849747491543147160621 21838443655309328680185233)
  ·
    refine ⟨16378832741481996510138925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21838443655309328680185233 16378832741481996510138925)
    ·
      refine ⟨6142062278055748691302097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16378832741481996510138925 6142062278055748691302097)
      ·
        refine ⟨4606546708541811518476573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6142062278055748691302097 4606546708541811518476573)
        ·
          refine ⟨1727455015703179319428715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4606546708541811518476573 1727455015703179319428715)
          ·
            refine ⟨2591182523554768979143073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1727455015703179319428715 2591182523554768979143073)
            ·
              refine ⟨1943386892666076734357305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2591182523554768979143073 1943386892666076734357305)
              ·
                refine ⟨1457540169499557550767979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1943386892666076734357305 1457540169499557550767979)
                ·
                  refine ⟨2186310254249336326151969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1457540169499557550767979 2186310254249336326151969)
                  ·
                    refine ⟨1639732690687002244613977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2186310254249336326151969 1639732690687002244613977)
                    ·
                      refine ⟨1229799518015251683460483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1639732690687002244613977 1229799518015251683460483)
                      ·
                        rfl

theorem cell23_2395026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_2395026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395026 prefixEnd_2395026 := by exact prefixLift 2395026
  have htrace : WordTrace (prefixWord ++ tailWord_2395026) baseStart_2395026 baseEnd_2395026 := by
    simpa [prefixWord, tailWord_2395026, baseEnd_2395026] using wordTrace_append hprefix tailTrace_2395026
  have hstable : (prefixWord ++ tailWord_2395026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395026).length < 2 ^ (prefixWord ++ tailWord_2395026).sum := by decide
  have hdescent : baseEnd_2395026 < baseStart_2395026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395044 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 2, 2, 4]
def baseStart_2395044 : Nat := 118140960795 + 2395044 * 2 ^ 59
def prefixEnd_2395044 : Nat := 4983230072969 + 3 ^ 40 * 2395044 * 2
def baseEnd_2395044 : Nat := 1229808760667032613035399

theorem tailTrace_2395044 : CollatzResearch.WordTrace tailWord_2395044 prefixEnd_2395044 1229808760667032613035399 := by
  unfold tailWord_2395044
  simp only [CollatzResearch.WordTrace]
  refine ⟨43677215567586051897448093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58236287423448069196597457 43677215567586051897448093)
  ·
    refine ⟨16378955837844769461543035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43677215567586051897448093 16378955837844769461543035)
    ·
      refine ⟨24568433756767154192314553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16378955837844769461543035 24568433756767154192314553)
      ·
        refine ⟨18426325317575365644235915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24568433756767154192314553 18426325317575365644235915)
        ·
          refine ⟨27639487976363048466353873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18426325317575365644235915 27639487976363048466353873)
          ·
            refine ⟨20729615982272286349765405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27639487976363048466353873 20729615982272286349765405)
            ·
              refine ⟨7773605993352107381162027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20729615982272286349765405 7773605993352107381162027)
              ·
                refine ⟨11660408990028161071743041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7773605993352107381162027 11660408990028161071743041)
                ·
                  refine ⟨8745306742521120803807281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11660408990028161071743041 8745306742521120803807281)
                  ·
                    refine ⟨6558980056890840602855461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8745306742521120803807281 6558980056890840602855461)
                    ·
                      refine ⟨1229808760667032613035399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6558980056890840602855461 1229808760667032613035399)
                      ·
                        rfl

theorem cell23_2395044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_2395044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395044 prefixEnd_2395044 := by exact prefixLift 2395044
  have htrace : WordTrace (prefixWord ++ tailWord_2395044) baseStart_2395044 baseEnd_2395044 := by
    simpa [prefixWord, tailWord_2395044, baseEnd_2395044] using wordTrace_append hprefix tailTrace_2395044
  have hstable : (prefixWord ++ tailWord_2395044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395044).length < 2 ^ (prefixWord ++ tailWord_2395044).sum := by decide
  have hdescent : baseEnd_2395044 < baseStart_2395044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395084 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 4, 5]
def baseStart_2395084 : Nat := 118140960795 + 2395084 * 2 ^ 59
def prefixEnd_2395084 : Nat := 4983230072969 + 3 ^ 40 * 2395084 * 2
def baseEnd_2395084 : Nat := 409943099964404152178405

theorem tailTrace_2395084 : CollatzResearch.WordTrace tailWord_2395084 prefixEnd_2395084 409943099964404152178405 := by
  unfold tailWord_2395084
  simp only [CollatzResearch.WordTrace]
  refine ⟨43677945027513595313176153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58237260036684793750901537 43677945027513595313176153)
  ·
    refine ⟨32758458770635196484882115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43677945027513595313176153 32758458770635196484882115)
    ·
      refine ⟨49137688155952794727323173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32758458770635196484882115 49137688155952794727323173)
      ·
        refine ⟨9213316529241149011373095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49137688155952794727323173 9213316529241149011373095)
        ·
          refine ⟨13819974793861723517059643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9213316529241149011373095 13819974793861723517059643)
          ·
            refine ⟨20729962190792585275589465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13819974793861723517059643 20729962190792585275589465)
            ·
              refine ⟨15547471643094438956692099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20729962190792585275589465 15547471643094438956692099)
              ·
                refine ⟨23321207464641658435038149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15547471643094438956692099 23321207464641658435038149)
                ·
                  refine ⟨4372726399620310956569653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23321207464641658435038149 4372726399620310956569653)
                  ·
                    refine ⟨409943099964404152178405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4372726399620310956569653 409943099964404152178405)
                    ·
                      rfl

theorem cell23_2395084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_2395084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395084 prefixEnd_2395084 := by exact prefixLift 2395084
  have htrace : WordTrace (prefixWord ++ tailWord_2395084) baseStart_2395084 baseEnd_2395084 := by
    simpa [prefixWord, tailWord_2395084, baseEnd_2395084] using wordTrace_append hprefix tailTrace_2395084
  have hstable : (prefixWord ++ tailWord_2395084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395084).length < 2 ^ (prefixWord ++ tailWord_2395084).sum := by decide
  have hdescent : baseEnd_2395084 < baseStart_2395084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395122 : List Nat := [3, 2, 1, 5, 2, 1, 1, 3, 5]
def baseStart_2395122 : Nat := 118140960795 + 2395122 * 2 ^ 59
def prefixEnd_2395122 : Nat := 4983230072969 + 3 ^ 40 * 2395122 * 2
def baseEnd_2395122 : Nat := 136649868017564811984449

theorem tailTrace_2395122 : CollatzResearch.WordTrace tailWord_2395122 prefixEnd_2395122 136649868017564811984449 := by
  unfold tailWord_2395122
  simp only [CollatzResearch.WordTrace]
  refine ⟨21839319007222380779058905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58238184019259682077490413 21839319007222380779058905)
  ·
    refine ⟨16379489255416785584294179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21839319007222380779058905 16379489255416785584294179)
    ·
      refine ⟨24569233883125178376441269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16379489255416785584294179 24569233883125178376441269)
      ·
        refine ⟨2303365676542985472791369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24569233883125178376441269 2303365676542985472791369)
        ·
          refine ⟨1727524257407239104593527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2303365676542985472791369 1727524257407239104593527)
          ·
            refine ⟨2591286386110858656890291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1727524257407239104593527 2591286386110858656890291)
            ·
              refine ⟨3886929579166287985335437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2591286386110858656890291 3886929579166287985335437)
              ·
                refine ⟨1457598592187357994500789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3886929579166287985335437 1457598592187357994500789)
                ·
                  refine ⟨136649868017564811984449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1457598592187357994500789 136649868017564811984449)
                  ·
                    rfl

theorem cell23_2395122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_2395122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395122 prefixEnd_2395122 := by exact prefixLift 2395122
  have htrace : WordTrace (prefixWord ++ tailWord_2395122) baseStart_2395122 baseEnd_2395122 := by
    simpa [prefixWord, tailWord_2395122, baseEnd_2395122] using wordTrace_append hprefix tailTrace_2395122
  have hstable : (prefixWord ++ tailWord_2395122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395122).length < 2 ^ (prefixWord ++ tailWord_2395122).sum := by decide
  have hdescent : baseEnd_2395122 < baseStart_2395122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395141 : List Nat := [1, 3, 1, 1, 2, 3, 3, 2, 2, 2, 3]
def baseStart_2395141 : Nat := 118140960795 + 2395141 * 2 ^ 59
def prefixEnd_2395141 : Nat := 4983230072969 + 3 ^ 40 * 2395141 * 2
def baseEnd_2395141 : Nat := 1229858568290518733522453

theorem tailTrace_2395141 : CollatzResearch.WordTrace tailWord_2395141 prefixEnd_2395141 1229858568290518733522453 := by
  unfold tailWord_2395141
  simp only [CollatzResearch.WordTrace]
  refine ⟨87357969015820689361177277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58238646010547126240784851 87357969015820689361177277)
  ·
    refine ⟨32759238380932758510441479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87357969015820689361177277 32759238380932758510441479)
    ·
      refine ⟨49138857571399137765662219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32759238380932758510441479 49138857571399137765662219)
      ·
        refine ⟨73708286357098706648493329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49138857571399137765662219 73708286357098706648493329)
        ·
          refine ⟨55281214767824029986369997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73708286357098706648493329 55281214767824029986369997)
          ·
            refine ⟨20730455537934011244888749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55281214767824029986369997 20730455537934011244888749)
            ·
              refine ⟨7773920826725254216833281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20730455537934011244888749 7773920826725254216833281)
              ·
                refine ⟨5830440620043940662624961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7773920826725254216833281 5830440620043940662624961)
                ·
                  refine ⟨4372830465032955496968721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5830440620043940662624961 4372830465032955496968721)
                  ·
                    refine ⟨3279622848774716622726541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4372830465032955496968721 3279622848774716622726541)
                    ·
                      refine ⟨1229858568290518733522453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3279622848774716622726541 1229858568290518733522453)
                      ·
                        rfl

theorem cell23_2395141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 2, 3].length) (baseStart_2395141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395141 prefixEnd_2395141 := by exact prefixLift 2395141
  have htrace : WordTrace (prefixWord ++ tailWord_2395141) baseStart_2395141 baseEnd_2395141 := by
    simpa [prefixWord, tailWord_2395141, baseEnd_2395141] using wordTrace_append hprefix tailTrace_2395141
  have hstable : (prefixWord ++ tailWord_2395141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395141).length < 2 ^ (prefixWord ++ tailWord_2395141).sum := by decide
  have hdescent : baseEnd_2395141 < baseStart_2395141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395144 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 8]
def baseStart_2395144 : Nat := 118140960795 + 2395144 * 2 ^ 59
def prefixEnd_2395144 : Nat := 4983230072969 + 3 ^ 40 * 2395144 * 2
def baseEnd_2395144 : Nat := 136651123192498024642771

theorem tailTrace_2395144 : CollatzResearch.WordTrace tailWord_2395144 prefixEnd_2395144 136651123192498024642771 := by
  unfold tailWord_2395144
  simp only [CollatzResearch.WordTrace]
  refine ⟨43679039217404910436768243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58238718956539880582357657 43679039217404910436768243)
  ·
    refine ⟨65518558826107365655152365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43679039217404910436768243 65518558826107365655152365)
    ·
      refine ⟨24569459559790262120682137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65518558826107365655152365 24569459559790262120682137)
      ·
        refine ⟨18427094669842696590511603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24569459559790262120682137 18427094669842696590511603)
        ·
          refine ⟨27640642004764044885767405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18427094669842696590511603 27640642004764044885767405)
          ·
            refine ⟨10365240751786516832162777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27640642004764044885767405 10365240751786516832162777)
            ·
              refine ⟨7773930563839887624122083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10365240751786516832162777 7773930563839887624122083)
              ·
                refine ⟨11660895845759831436183125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7773930563839887624122083 11660895845759831436183125)
                ·
                  refine ⟨136651123192498024642771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11660895845759831436183125 136651123192498024642771)
                  ·
                    rfl

theorem cell23_2395144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 8].length) (baseStart_2395144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395144 prefixEnd_2395144 := by exact prefixLift 2395144
  have htrace : WordTrace (prefixWord ++ tailWord_2395144) baseStart_2395144 baseEnd_2395144 := by
    simpa [prefixWord, tailWord_2395144, baseEnd_2395144] using wordTrace_append hprefix tailTrace_2395144
  have hstable : (prefixWord ++ tailWord_2395144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395144).length < 2 ^ (prefixWord ++ tailWord_2395144).sum := by decide
  have hdescent : baseEnd_2395144 < baseStart_2395144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395148 : List Nat := [2, 2, 1, 2, 3, 4, 1, 1, 3, 4]
def baseStart_2395148 : Nat := 118140960795 + 2395148 * 2 ^ 59
def prefixEnd_2395148 : Nat := 4983230072969 + 3 ^ 40 * 2395148 * 2
def baseEnd_2395148 : Nat := 409954054218366735378307

theorem tailTrace_2395148 : CollatzResearch.WordTrace tailWord_2395148 prefixEnd_2395148 409954054218366735378307 := by
  unfold tailWord_2395148
  simp only [CollatzResearch.WordTrace]
  refine ⟨43679112163397664778341049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58238816217863553037788065 43679112163397664778341049)
  ·
    refine ⟨32759334122548248583755787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43679112163397664778341049 32759334122548248583755787)
    ·
      refine ⟨49139001183822372875633681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32759334122548248583755787 49139001183822372875633681)
      ·
        refine ⟨36854250887866779656725261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49139001183822372875633681 36854250887866779656725261)
        ·
          refine ⟨13820344082950042371271973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36854250887866779656725261 13820344082950042371271973)
          ·
            refine ⟨2591314515553132944613495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13820344082950042371271973 2591314515553132944613495)
            ·
              refine ⟨3886971773329699416920243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2591314515553132944613495 3886971773329699416920243)
              ·
                refine ⟨5830457659994549125380365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3886971773329699416920243 5830457659994549125380365)
                ·
                  refine ⟨2186421622497955922017637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5830457659994549125380365 2186421622497955922017637)
                  ·
                    refine ⟨409954054218366735378307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2186421622497955922017637 409954054218366735378307)
                    ·
                      rfl

theorem cell23_2395148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 3, 4].length) (baseStart_2395148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395148 prefixEnd_2395148 := by exact prefixLift 2395148
  have htrace : WordTrace (prefixWord ++ tailWord_2395148) baseStart_2395148 baseEnd_2395148 := by
    simpa [prefixWord, tailWord_2395148, baseEnd_2395148] using wordTrace_append hprefix tailTrace_2395148
  have hstable : (prefixWord ++ tailWord_2395148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395148).length < 2 ^ (prefixWord ++ tailWord_2395148).sum := by decide
  have hdescent : baseEnd_2395148 < baseStart_2395148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395161 : List Nat := [1, 2, 1, 2, 1, 1, 8, 1, 6]
def baseStart_2395161 : Nat := 118140960795 + 2395161 * 2 ^ 59
def prefixEnd_2395161 : Nat := 4983230072969 + 3 ^ 40 * 2395161 * 2
def baseEnd_2395161 : Nat := 136652093100400961696929

theorem tailTrace_2395161 : CollatzResearch.WordTrace tailWord_2395161 prefixEnd_2395161 136652093100400961696929 := by
  unfold tailWord_2395161
  simp only [CollatzResearch.WordTrace]
  refine ⟨87358698475748232776905337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58239132317165488517936891 87358698475748232776905337)
  ·
    refine ⟨65519023856811174582679003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87358698475748232776905337 65519023856811174582679003)
    ·
      refine ⟨98278535785216761874018505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65519023856811174582679003 98278535785216761874018505)
      ·
        refine ⟨73708901838912571405513879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98278535785216761874018505 73708901838912571405513879)
        ·
          refine ⟨110563352758368857108270819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73708901838912571405513879 110563352758368857108270819)
          ·
            refine ⟨165845029137553285662406229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110563352758368857108270819 165845029137553285662406229)
            ·
              refine ⟨1943496435205702566356323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 165845029137553285662406229 1943496435205702566356323)
              ·
                refine ⟨2915244652808553849534485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1943496435205702566356323 2915244652808553849534485)
                ·
                  refine ⟨136652093100400961696929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2915244652808553849534485 136652093100400961696929)
                  ·
                    rfl

theorem cell23_2395161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 6].length) (baseStart_2395161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395161 prefixEnd_2395161 := by exact prefixLift 2395161
  have htrace : WordTrace (prefixWord ++ tailWord_2395161) baseStart_2395161 baseEnd_2395161 := by
    simpa [prefixWord, tailWord_2395161, baseEnd_2395161] using wordTrace_append hprefix tailTrace_2395161
  have hstable : (prefixWord ++ tailWord_2395161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395161).length < 2 ^ (prefixWord ++ tailWord_2395161).sum := by decide
  have hdescent : baseEnd_2395161 < baseStart_2395161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395175 : List Nat := [1, 1, 7, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_2395175 : Nat := 118140960795 + 2395175 * 2 ^ 59
def prefixEnd_2395175 : Nat := 4983230072969 + 3 ^ 40 * 2395175 * 2
def baseEnd_2395175 : Nat := 1229876026632771600497297

theorem tailTrace_2395175 : CollatzResearch.WordTrace tailWord_2395175 prefixEnd_2395175 1229876026632771600497297 := by
  unfold tailWord_2395175
  simp only [CollatzResearch.WordTrace]
  refine ⟨87359209097697513167914979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58239472731798342111943319 87359209097697513167914979)
  ·
    refine ⟨131038813646546269751872469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87359209097697513167914979 131038813646546269751872469)
    ·
      refine ⟨3071222194840928197309511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 131038813646546269751872469 3071222194840928197309511)
      ·
        refine ⟨4606833292261392295964267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3071222194840928197309511 4606833292261392295964267)
        ·
          refine ⟨6910249938392088443946401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4606833292261392295964267 6910249938392088443946401)
          ·
            refine ⟨5182687453794066332959801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6910249938392088443946401 5182687453794066332959801)
            ·
              refine ⟨3887015590345549749719851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5182687453794066332959801 3887015590345549749719851)
              ·
                refine ⟨5830523385518324624579777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3887015590345549749719851 5830523385518324624579777)
                ·
                  refine ⟨4372892539138743468434833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5830523385518324624579777 4372892539138743468434833)
                  ·
                    refine ⟨3279669404354057601326125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4372892539138743468434833 3279669404354057601326125)
                    ·
                      refine ⟨1229876026632771600497297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3279669404354057601326125 1229876026632771600497297)
                      ·
                        rfl

theorem cell23_2395175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_2395175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395175 prefixEnd_2395175 := by exact prefixLift 2395175
  have htrace : WordTrace (prefixWord ++ tailWord_2395175) baseStart_2395175 baseEnd_2395175 := by
    simpa [prefixWord, tailWord_2395175, baseEnd_2395175] using wordTrace_append hprefix tailTrace_2395175
  have hstable : (prefixWord ++ tailWord_2395175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395175).length < 2 ^ (prefixWord ++ tailWord_2395175).sum := by decide
  have hdescent : baseEnd_2395175 < baseStart_2395175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395221 : List Nat := [1, 3, 2, 2, 1, 2, 4, 1, 1, 6]
def baseStart_2395221 : Nat := 118140960795 + 2395221 * 2 ^ 59
def prefixEnd_2395221 : Nat := 4983230072969 + 3 ^ 40 * 2395221 * 2
def baseEnd_2395221 : Nat := 409966548914292806840695

theorem tailTrace_2395221 : CollatzResearch.WordTrace tailWord_2395221 prefixEnd_2395221 409966548914292806840695 := by
  unfold tailWord_2395221
  simp only [CollatzResearch.WordTrace]
  refine ⟨87360886855530863024089517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58240591237020575349393011 87360886855530863024089517)
  ·
    refine ⟨32760332570824073634033569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87360886855530863024089517 32760332570824073634033569)
    ·
      refine ⟨24570249428118055225525177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32760332570824073634033569 24570249428118055225525177)
      ·
        refine ⟨18427687071088541419143883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24570249428118055225525177 18427687071088541419143883)
        ·
          refine ⟨27641530606632812128715825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18427687071088541419143883 27641530606632812128715825)
          ·
            refine ⟨20731147954974609096536869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27641530606632812128715825 20731147954974609096536869)
            ·
              refine ⟨3887090241557739205600663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20731147954974609096536869 3887090241557739205600663)
              ·
                refine ⟨5830635362336608808400995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3887090241557739205600663 5830635362336608808400995)
                ·
                  refine ⟨8745953043504913212601493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5830635362336608808400995 8745953043504913212601493)
                  ·
                    refine ⟨409966548914292806840695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8745953043504913212601493 409966548914292806840695)
                    ·
                      rfl

theorem cell23_2395221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_2395221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395221 prefixEnd_2395221 := by exact prefixLift 2395221
  have htrace : WordTrace (prefixWord ++ tailWord_2395221) baseStart_2395221 baseEnd_2395221 := by
    simpa [prefixWord, tailWord_2395221, baseEnd_2395221] using wordTrace_append hprefix tailTrace_2395221
  have hstable : (prefixWord ++ tailWord_2395221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395221).length < 2 ^ (prefixWord ++ tailWord_2395221).sum := by decide
  have hdescent : baseEnd_2395221 < baseStart_2395221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395228 : List Nat := [2, 2, 4, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_2395228 : Nat := 118140960795 + 2395228 * 2 ^ 59
def prefixEnd_2395228 : Nat := 4983230072969 + 3 ^ 40 * 2395228 * 2
def baseEnd_2395228 : Nat := 1229903241107459893134553

theorem tailTrace_2395228 : CollatzResearch.WordTrace tailWord_2395228 prefixEnd_2395228 1229903241107459893134553 := by
  unfold tailWord_2395228
  simp only [CollatzResearch.WordTrace]
  refine ⟨43680571083252751609797169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58240761444337002146396225 43680571083252751609797169)
  ·
    refine ⟨32760428312439563707347877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43680571083252751609797169 32760428312439563707347877)
    ·
      refine ⟨6142580308582418195127727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32760428312439563707347877 6142580308582418195127727)
      ·
        refine ⟨9213870462873627292691591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6142580308582418195127727 9213870462873627292691591)
        ·
          refine ⟨13820805694310440939037387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9213870462873627292691591 13820805694310440939037387)
          ·
            refine ⟨20731208541465661408556081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13820805694310440939037387 20731208541465661408556081)
            ·
              refine ⟨15548406406099246056417061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20731208541465661408556081 15548406406099246056417061)
              ·
                refine ⟨2915326201143608635578199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15548406406099246056417061 2915326201143608635578199)
                ·
                  refine ⟨4372989301715412953367299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2915326201143608635578199 4372989301715412953367299)
                  ·
                    refine ⟨6559483952573119430050949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4372989301715412953367299 6559483952573119430050949)
                    ·
                      refine ⟨1229903241107459893134553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6559483952573119430050949 1229903241107459893134553)
                      ·
                        rfl

theorem cell23_2395228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_2395228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395228 prefixEnd_2395228 := by exact prefixLift 2395228
  have htrace : WordTrace (prefixWord ++ tailWord_2395228) baseStart_2395228 baseEnd_2395228 := by
    simpa [prefixWord, tailWord_2395228, baseEnd_2395228] using wordTrace_append hprefix tailTrace_2395228
  have hstable : (prefixWord ++ tailWord_2395228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395228).length < 2 ^ (prefixWord ++ tailWord_2395228).sum := by decide
  have hdescent : baseEnd_2395228 < baseStart_2395228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395231 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 3]
def baseStart_2395231 : Nat := 118140960795 + 2395231 * 2 ^ 59
def prefixEnd_2395231 : Nat := 4983230072969 + 3 ^ 40 * 2395231 * 2
def baseEnd_2395231 : Nat := 1229904781549423381397039

theorem tailTrace_2395231 : CollatzResearch.WordTrace tailWord_2395231 prefixEnd_2395231 1229904781549423381397039 := by
  unfold tailWord_2395231
  simp only [CollatzResearch.WordTrace]
  refine ⟨87361251585494634731953547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58240834390329756487969031 87361251585494634731953547)
  ·
    refine ⟨131041877378241952097930321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87361251585494634731953547 131041877378241952097930321)
    ·
      refine ⟨98281408033681464073447741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131041877378241952097930321 98281408033681464073447741)
      ·
        refine ⟨36855528012630549027542903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98281408033681464073447741 36855528012630549027542903)
        ·
          refine ⟨55283292018945823541314355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36855528012630549027542903 55283292018945823541314355)
          ·
            refine ⟨82924938028418735311971533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55283292018945823541314355 82924938028418735311971533)
            ·
              refine ⟨31096851760657025741989325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82924938028418735311971533 31096851760657025741989325)
              ·
                refine ⟨11661319410246384653245997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31096851760657025741989325 11661319410246384653245997)
                ·
                  refine ⟨4372994778842394244967249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11661319410246384653245997 4372994778842394244967249)
                  ·
                    refine ⟨3279746084131795683725437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4372994778842394244967249 3279746084131795683725437)
                    ·
                      refine ⟨1229904781549423381397039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3279746084131795683725437 1229904781549423381397039)
                      ·
                        rfl

theorem cell23_2395231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_2395231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395231 prefixEnd_2395231 := by exact prefixLift 2395231
  have htrace : WordTrace (prefixWord ++ tailWord_2395231) baseStart_2395231 baseEnd_2395231 := by
    simpa [prefixWord, tailWord_2395231, baseEnd_2395231] using wordTrace_append hprefix tailTrace_2395231
  have hstable : (prefixWord ++ tailWord_2395231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395231).length < 2 ^ (prefixWord ++ tailWord_2395231).sum := by decide
  have hdescent : baseEnd_2395231 < baseStart_2395231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395241 : List Nat := [1, 2, 1, 1, 1, 6, 2, 2, 1, 2, 4]
def baseStart_2395241 : Nat := 118140960795 + 2395241 * 2 ^ 59
def prefixEnd_2395241 : Nat := 4983230072969 + 3 ^ 40 * 2395241 * 2
def baseEnd_2395241 : Nat := 1229909916355968342271993

theorem tailTrace_2395241 : CollatzResearch.WordTrace tailWord_2395241 prefixEnd_2395241 1229909916355968342271993 := by
  unfold tailWord_2395241
  simp only [CollatzResearch.WordTrace]
  refine ⟨87361616315458406439817577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58241077543638937626545051 87361616315458406439817577)
  ·
    refine ⟨65521212236593804829863183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87361616315458406439817577 65521212236593804829863183)
    ·
      refine ⟨98281818354890707244794775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65521212236593804829863183 98281818354890707244794775)
      ·
        refine ⟨147422727532336060867192163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98281818354890707244794775 147422727532336060867192163)
        ·
          refine ⟨221134091298504091300788245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147422727532336060867192163 221134091298504091300788245)
          ·
            refine ⟨10365660529617379279724449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 221134091298504091300788245 10365660529617379279724449)
            ·
              refine ⟨7774245397213034459793337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10365660529617379279724449 7774245397213034459793337)
              ·
                refine ⟨5830684047909775844845003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7774245397213034459793337 5830684047909775844845003)
                ·
                  refine ⟨8746026071864663767267505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5830684047909775844845003 8746026071864663767267505)
                  ·
                    refine ⟨6559519553898497825450629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8746026071864663767267505 6559519553898497825450629)
                    ·
                      refine ⟨1229909916355968342271993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6559519553898497825450629 1229909916355968342271993)
                      ·
                        rfl

theorem cell23_2395241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 2, 4].length) (baseStart_2395241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395241 prefixEnd_2395241 := by exact prefixLift 2395241
  have htrace : WordTrace (prefixWord ++ tailWord_2395241) baseStart_2395241 baseEnd_2395241 := by
    simpa [prefixWord, tailWord_2395241, baseEnd_2395241] using wordTrace_append hprefix tailTrace_2395241
  have hstable : (prefixWord ++ tailWord_2395241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395241).length < 2 ^ (prefixWord ++ tailWord_2395241).sum := by decide
  have hdescent : baseEnd_2395241 < baseStart_2395241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395245 : List Nat := [1, 5, 1, 1, 2, 2, 4, 1, 1, 1, 4]
def baseStart_2395245 : Nat := 118140960795 + 2395245 * 2 ^ 59
def prefixEnd_2395245 : Nat := 4983230072969 + 3 ^ 40 * 2395245 * 2
def baseEnd_2395245 : Nat := 1229911970278586326621975

theorem tailTrace_2395245 : CollatzResearch.WordTrace tailWord_2395245 prefixEnd_2395245 1229911970278586326621975 := by
  unfold tailWord_2395245
  simp only [CollatzResearch.WordTrace]
  refine ⟨87361762207443915122963189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58241174804962610081975459 87361762207443915122963189)
  ·
    refine ⟨8190165206947867042777799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87361762207443915122963189 8190165206947867042777799)
    ·
      refine ⟨12285247810421800564166699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8190165206947867042777799 12285247810421800564166699)
      ·
        refine ⟨18427871715632700846250049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12285247810421800564166699 18427871715632700846250049)
        ·
          refine ⟨13820903786724525634687537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18427871715632700846250049 13820903786724525634687537)
          ·
            refine ⟨10365677840043394226015653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13820903786724525634687537 10365677840043394226015653)
            ·
              refine ⟨1943564595008136417377935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10365677840043394226015653 1943564595008136417377935)
              ·
                refine ⟨2915346892512204626066903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1943564595008136417377935 2915346892512204626066903)
                ·
                  refine ⟨4373020338768306939100355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2915346892512204626066903 4373020338768306939100355)
                  ·
                    refine ⟨6559530508152460408650533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4373020338768306939100355 6559530508152460408650533)
                    ·
                      refine ⟨1229911970278586326621975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6559530508152460408650533 1229911970278586326621975)
                      ·
                        rfl

theorem cell23_2395245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_2395245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395245 prefixEnd_2395245 := by exact prefixLift 2395245
  have htrace : WordTrace (prefixWord ++ tailWord_2395245) baseStart_2395245 baseEnd_2395245 := by
    simpa [prefixWord, tailWord_2395245, baseEnd_2395245] using wordTrace_append hprefix tailTrace_2395245
  have hstable : (prefixWord ++ tailWord_2395245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395245).length < 2 ^ (prefixWord ++ tailWord_2395245).sum := by decide
  have hdescent : baseEnd_2395245 < baseStart_2395245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395248 : List Nat := [2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 3]
def baseStart_2395248 : Nat := 118140960795 + 2395248 * 2 ^ 59
def prefixEnd_2395248 : Nat := 4983230072969 + 3 ^ 40 * 2395248 * 2
def baseEnd_2395248 : Nat := 1229913510720549814884461

theorem tailTrace_2395248 : CollatzResearch.WordTrace tailWord_2395248 prefixEnd_2395248 1229913510720549814884461 := by
  unfold tailWord_2395248
  simp only [CollatzResearch.WordTrace]
  refine ⟨43680935813216523317661199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58241247750955364423548265 43680935813216523317661199)
  ·
    refine ⟨65521403719824784976491799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43680935813216523317661199 65521403719824784976491799)
    ·
      refine ⟨98282105579737177464737699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65521403719824784976491799 98282105579737177464737699)
      ·
        refine ⟨147423158369605766197106549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98282105579737177464737699 147423158369605766197106549)
        ·
          refine ⟨13820921097150540580978739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 147423158369605766197106549 13820921097150540580978739)
          ·
            refine ⟨20731381645725810871468109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13820921097150540580978739 20731381645725810871468109)
            ·
              refine ⟨7774268117147179076800541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20731381645725810871468109 7774268117147179076800541)
              ·
                refine ⟨2915350543930192153800203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7774268117147179076800541 2915350543930192153800203)
                ·
                  refine ⟨4373025815895288230700305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2915350543930192153800203 4373025815895288230700305)
                  ·
                    refine ⟨3279769361921466173025229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4373025815895288230700305 3279769361921466173025229)
                    ·
                      refine ⟨1229913510720549814884461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3279769361921466173025229 1229913510720549814884461)
                      ·
                        rfl

theorem cell23_2395248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 3].length) (baseStart_2395248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395248 prefixEnd_2395248 := by exact prefixLift 2395248
  have htrace : WordTrace (prefixWord ++ tailWord_2395248) baseStart_2395248 baseEnd_2395248 := by
    simpa [prefixWord, tailWord_2395248, baseEnd_2395248] using wordTrace_append hprefix tailTrace_2395248
  have hstable : (prefixWord ++ tailWord_2395248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395248).length < 2 ^ (prefixWord ++ tailWord_2395248).sum := by decide
  have hdescent : baseEnd_2395248 < baseStart_2395248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395264 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 1, 9]
def baseStart_2395264 : Nat := 118140960795 + 2395264 * 2 ^ 59
def prefixEnd_2395264 : Nat := 4983230072969 + 3 ^ 40 * 2395264 * 2
def baseEnd_2395264 : Nat := 409973908803673917428129

theorem tailTrace_2395264 : CollatzResearch.WordTrace tailWord_2395264 prefixEnd_2395264 409973908803673917428129 := by
  unfold tailWord_2395264
  simp only [CollatzResearch.WordTrace]
  refine ⟨43681227597187540683952423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58241636796250054245269897 43681227597187540683952423)
  ·
    refine ⟨65521841395781311025928635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43681227597187540683952423 65521841395781311025928635)
    ·
      refine ⟨98282762093671966538892953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65521841395781311025928635 98282762093671966538892953)
      ·
        refine ⟨73712071570253974904169715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98282762093671966538892953 73712071570253974904169715)
        ·
          refine ⟨110568107355380962356254573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73712071570253974904169715 110568107355380962356254573)
          ·
            refine ⟨41463040258267860883595465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110568107355380962356254573 41463040258267860883595465)
            ·
              refine ⟨31097280193700895662696599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41463040258267860883595465 31097280193700895662696599)
              ·
                refine ⟨46645920290551343494044899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31097280193700895662696599 46645920290551343494044899)
                ·
                  refine ⟨69968880435827015241067349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46645920290551343494044899 69968880435827015241067349)
                  ·
                    refine ⟨409973908803673917428129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 69968880435827015241067349 409973908803673917428129)
                    ·
                      rfl

theorem cell23_2395264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 9].length) (baseStart_2395264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395264 prefixEnd_2395264 := by exact prefixLift 2395264
  have htrace : WordTrace (prefixWord ++ tailWord_2395264) baseStart_2395264 baseEnd_2395264 := by
    simpa [prefixWord, tailWord_2395264, baseEnd_2395264] using wordTrace_append hprefix tailTrace_2395264
  have hstable : (prefixWord ++ tailWord_2395264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395264).length < 2 ^ (prefixWord ++ tailWord_2395264).sum := by decide
  have hdescent : baseEnd_2395264 < baseStart_2395264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395272 : List Nat := [2, 1, 3, 4, 2, 1, 3, 1, 2, 4]
def baseStart_2395272 : Nat := 118140960795 + 2395272 * 2 ^ 59
def prefixEnd_2395272 : Nat := 4983230072969 + 3 ^ 40 * 2395272 * 2
def baseEnd_2395272 : Nat := 409975278085419240328117

theorem tailTrace_2395272 : CollatzResearch.WordTrace tailWord_2395272 prefixEnd_2395272 409975278085419240328117 := by
  unfold tailWord_2395272
  simp only [CollatzResearch.WordTrace]
  refine ⟨43681373489173049367098035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58241831318897399156130713 43681373489173049367098035)
  ·
    refine ⟨65522060233759574050647053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43681373489173049367098035 65522060233759574050647053)
    ·
      refine ⟨24570772587659840268992645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65522060233759574050647053 24570772587659840268992645)
      ·
        refine ⟨4607019860186220050436121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24570772587659840268992645 4607019860186220050436121)
        ·
          refine ⟨3455264895139665037827091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4607019860186220050436121 3455264895139665037827091)
          ·
            refine ⟨5182897342709497556740637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3455264895139665037827091 5182897342709497556740637)
            ·
              refine ⟨1943586503516061583777739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5182897342709497556740637 1943586503516061583777739)
              ·
                refine ⟨2915379755274092375666609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1943586503516061583777739 2915379755274092375666609)
                ·
                  refine ⟨2186534816455569281749957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2915379755274092375666609 2186534816455569281749957)
                  ·
                    refine ⟨409975278085419240328117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2186534816455569281749957 409975278085419240328117)
                    ·
                      rfl

theorem cell23_2395272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_2395272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395272 prefixEnd_2395272 := by exact prefixLift 2395272
  have htrace : WordTrace (prefixWord ++ tailWord_2395272) baseStart_2395272 baseEnd_2395272 := by
    simpa [prefixWord, tailWord_2395272, baseEnd_2395272] using wordTrace_append hprefix tailTrace_2395272
  have hstable : (prefixWord ++ tailWord_2395272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395272).length < 2 ^ (prefixWord ++ tailWord_2395272).sum := by decide
  have hdescent : baseEnd_2395272 < baseStart_2395272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395329 : List Nat := [1, 2, 6, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_2395329 : Nat := 118140960795 + 2395329 * 2 ^ 59
def prefixEnd_2395329 : Nat := 4983230072969 + 3 ^ 40 * 2395329 * 2
def baseEnd_2395329 : Nat := 1229955102653563997971589

theorem tailTrace_2395329 : CollatzResearch.WordTrace tailWord_2395329 prefixEnd_2395329 1229955102653563997971589 := by
  unfold tailWord_2395329
  simp only [CollatzResearch.WordTrace]
  refine ⟨87364825939139597469021041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58243217292759731646014027 87364825939139597469021041)
  ·
    refine ⟨65523619454354698101765781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87364825939139597469021041 65523619454354698101765781)
    ·
      refine ⟨3071419661922876473520271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65523619454354698101765781 3071419661922876473520271)
      ·
        refine ⟨4607129492884314710280407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3071419661922876473520271 4607129492884314710280407)
        ·
          refine ⟨6910694239326472065420611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4607129492884314710280407 6910694239326472065420611)
          ·
            refine ⟨10366041358989708098130917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6910694239326472065420611 10366041358989708098130917)
            ·
              refine ⟨1943632754810570268399547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10366041358989708098130917 1943632754810570268399547)
              ·
                refine ⟨2915449132215855402599321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1943632754810570268399547 2915449132215855402599321)
                ·
                  refine ⟨2186586849161891551949491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2915449132215855402599321 2186586849161891551949491)
                  ·
                    refine ⟨3279880273742837327924237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2186586849161891551949491 3279880273742837327924237)
                    ·
                      refine ⟨1229955102653563997971589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3279880273742837327924237 1229955102653563997971589)
                      ·
                        rfl

theorem cell23_2395329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_2395329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395329 prefixEnd_2395329 := by exact prefixLift 2395329
  have htrace : WordTrace (prefixWord ++ tailWord_2395329) baseStart_2395329 baseEnd_2395329 := by
    simpa [prefixWord, tailWord_2395329, baseEnd_2395329] using wordTrace_append hprefix tailTrace_2395329
  have hstable : (prefixWord ++ tailWord_2395329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395329).length < 2 ^ (prefixWord ++ tailWord_2395329).sum := by decide
  have hdescent : baseEnd_2395329 < baseStart_2395329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395368 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 2, 3, 3]
def baseStart_2395368 : Nat := 118140960795 + 2395368 * 2 ^ 59
def prefixEnd_2395368 : Nat := 4983230072969 + 3 ^ 40 * 2395368 * 2
def baseEnd_2395368 : Nat := 1229975128399089345383909

theorem tailTrace_2395368 : CollatzResearch.WordTrace tailWord_2395368 prefixEnd_2395368 1229975128399089345383909 := by
  unfold tailWord_2395368
  simp only [CollatzResearch.WordTrace]
  refine ⟨43683124192999153564845379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58244165590665538086460505 43683124192999153564845379)
  ·
    refine ⟨65524686289498730347268069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43683124192999153564845379 65524686289498730347268069)
    ·
      refine ⟨12285878679281011940112763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65524686289498730347268069 12285878679281011940112763)
      ·
        refine ⟨18428818018921517910169145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12285878679281011940112763 18428818018921517910169145)
        ·
          refine ⟨13821613514191138432626859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18428818018921517910169145 13821613514191138432626859)
          ·
            refine ⟨20732420271286707648940289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13821613514191138432626859 20732420271286707648940289)
            ·
              refine ⟨15549315203465030736705217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20732420271286707648940289 15549315203465030736705217)
              ·
                refine ⟨11661986402598773052528913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15549315203465030736705217 11661986402598773052528913)
                ·
                  refine ⟨8746489801949079789396685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11661986402598773052528913 8746489801949079789396685)
                  ·
                    refine ⟨3279933675730904921023757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8746489801949079789396685 3279933675730904921023757)
                    ·
                      refine ⟨1229975128399089345383909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3279933675730904921023757 1229975128399089345383909)
                      ·
                        rfl

theorem cell23_2395368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_2395368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395368 prefixEnd_2395368 := by exact prefixLift 2395368
  have htrace : WordTrace (prefixWord ++ tailWord_2395368) baseStart_2395368 baseEnd_2395368 := by
    simpa [prefixWord, tailWord_2395368, baseEnd_2395368] using wordTrace_append hprefix tailTrace_2395368
  have hstable : (prefixWord ++ tailWord_2395368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395368).length < 2 ^ (prefixWord ++ tailWord_2395368).sum := by decide
  have hdescent : baseEnd_2395368 < baseStart_2395368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395375 : List Nat := [1, 1, 2, 1, 7, 1, 1, 4, 5]
def baseStart_2395375 : Nat := 118140960795 + 2395375 * 2 ^ 59
def prefixEnd_2395375 : Nat := 4983230072969 + 3 ^ 40 * 2395375 * 2
def baseEnd_2395375 : Nat := 136664302529296757555153

theorem tailTrace_2395375 : CollatzResearch.WordTrace tailWord_2395375 prefixEnd_2395375 136664302529296757555153 := by
  unfold tailWord_2395375
  simp only [CollatzResearch.WordTrace]
  refine ⟨87366503696972947325195579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58244335797981964883463719 87366503696972947325195579)
  ·
    refine ⟨131049755545459420987793369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87366503696972947325195579 131049755545459420987793369)
    ·
      refine ⟨98287316659094565740845027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131049755545459420987793369 98287316659094565740845027)
      ·
        refine ⟨147430974988641848611267541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98287316659094565740845027 147430974988641848611267541)
        ·
          refine ⟨3455413476296293326826583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 147430974988641848611267541 3455413476296293326826583)
          ·
            refine ⟨5183120214444439990239875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3455413476296293326826583 5183120214444439990239875)
            ·
              refine ⟨7774680321666659985359813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5183120214444439990239875 7774680321666659985359813)
              ·
                refine ⟨1457752560312498747254965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7774680321666659985359813 1457752560312498747254965)
                ·
                  refine ⟨136664302529296757555153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1457752560312498747254965 136664302529296757555153)
                  ·
                    rfl

theorem cell23_2395375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 5].length) (baseStart_2395375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395375 prefixEnd_2395375 := by exact prefixLift 2395375
  have htrace : WordTrace (prefixWord ++ tailWord_2395375) baseStart_2395375 baseEnd_2395375 := by
    simpa [prefixWord, tailWord_2395375, baseEnd_2395375] using wordTrace_append hprefix tailTrace_2395375
  have hstable : (prefixWord ++ tailWord_2395375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395375).length < 2 ^ (prefixWord ++ tailWord_2395375).sum := by decide
  have hdescent : baseEnd_2395375 < baseStart_2395375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395461 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 2, 9]
def baseStart_2395461 : Nat := 118140960795 + 2395461 * 2 ^ 59
def prefixEnd_2395461 : Nat := 4983230072969 + 3 ^ 40 * 2395461 * 2
def baseEnd_2395461 : Nat := 410007627366652493840327

theorem tailTrace_2395461 : CollatzResearch.WordTrace tailWord_2395461 prefixEnd_2395461 410007627366652493840327 := by
  unfold tailWord_2395461
  simp only [CollatzResearch.WordTrace]
  refine ⟨87369640374661384012826237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58246426916440922675217491 87369640374661384012826237)
  ·
    refine ⟨32763615140498019004809839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87369640374661384012826237 32763615140498019004809839)
    ·
      refine ⟨49145422710747028507214759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32763615140498019004809839 49145422710747028507214759)
      ·
        refine ⟨73718134066120542760822139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49145422710747028507214759 73718134066120542760822139)
        ·
          refine ⟨110577201099180814141233209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73718134066120542760822139 110577201099180814141233209)
          ·
            refine ⟨82932900824385610605924907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110577201099180814141233209 82932900824385610605924907)
            ·
              refine ⟨124399351236578415908887361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82932900824385610605924907 124399351236578415908887361)
              ·
                refine ⟨93299513427433811931665521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124399351236578415908887361 93299513427433811931665521)
                ·
                  refine ⟨69974635070575358948749141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93299513427433811931665521 69974635070575358948749141)
                  ·
                    refine ⟨410007627366652493840327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 69974635070575358948749141 410007627366652493840327)
                    ·
                      rfl

theorem cell23_2395461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_2395461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395461 prefixEnd_2395461 := by exact prefixLift 2395461
  have htrace : WordTrace (prefixWord ++ tailWord_2395461) baseStart_2395461 baseEnd_2395461 := by
    simpa [prefixWord, tailWord_2395461, baseEnd_2395461] using wordTrace_append hprefix tailTrace_2395461
  have hstable : (prefixWord ++ tailWord_2395461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395461).length < 2 ^ (prefixWord ++ tailWord_2395461).sum := by decide
  have hdescent : baseEnd_2395461 < baseStart_2395461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395471 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 7]
def baseStart_2395471 : Nat := 118140960795 + 2395471 * 2 ^ 59
def prefixEnd_2395471 : Nat := 4983230072969 + 3 ^ 40 * 2395471 * 2
def baseEnd_2395471 : Nat := 1230028016906502442395935

theorem tailTrace_2395471 : CollatzResearch.WordTrace tailWord_2395471 prefixEnd_2395471 1230028016906502442395935 := by
  unfold tailWord_2395471
  simp only [CollatzResearch.WordTrace]
  refine ⟨87370005104625155720690267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58246670069750103813793511 87370005104625155720690267)
  ·
    refine ⟨131055007656937733581035401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87370005104625155720690267 131055007656937733581035401)
    ·
      refine ⟨98291255742703300185776551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131055007656937733581035401 98291255742703300185776551)
      ·
        refine ⟨147436883614054950278664827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98291255742703300185776551 147436883614054950278664827)
        ·
          refine ⟨221155325421082425417997241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147436883614054950278664827 221155325421082425417997241)
          ·
            refine ⟨165866494065811819063497931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221155325421082425417997241 165866494065811819063497931)
            ·
              refine ⟨248799741098717728595246897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165866494065811819063497931 248799741098717728595246897)
              ·
                refine ⟨186599805824038296446435173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 248799741098717728595246897 186599805824038296446435173)
                ·
                  refine ⟨34987463592007180583706595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 186599805824038296446435173 34987463592007180583706595)
                  ·
                    refine ⟨52481195388010770875559893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34987463592007180583706595 52481195388010770875559893)
                    ·
                      refine ⟨1230028016906502442395935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52481195388010770875559893 1230028016906502442395935)
                      ·
                        rfl

theorem cell23_2395471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_2395471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395471 prefixEnd_2395471 := by exact prefixLift 2395471
  have htrace : WordTrace (prefixWord ++ tailWord_2395471) baseStart_2395471 baseEnd_2395471 := by
    simpa [prefixWord, tailWord_2395471, baseEnd_2395471] using wordTrace_append hprefix tailTrace_2395471
  have hstable : (prefixWord ++ tailWord_2395471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395471).length < 2 ^ (prefixWord ++ tailWord_2395471).sum := by decide
  have hdescent : baseEnd_2395471 < baseStart_2395471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395492 : List Nat := [2, 3, 1, 1, 3, 2, 3, 1, 3, 1, 3]
def baseStart_2395492 : Nat := 118140960795 + 2395492 * 2 ^ 59
def prefixEnd_2395492 : Nat := 4983230072969 + 3 ^ 40 * 2395492 * 2
def baseEnd_2395492 : Nat := 1230038800000246860233339

theorem tailTrace_2395492 : CollatzResearch.WordTrace tailWord_2395492 prefixEnd_2395492 1230038800000246860233339 := by
  unfold tailWord_2395492
  simp only [CollatzResearch.WordTrace]
  refine ⟨43685385518774538153602365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58247180691699384204803153 43685385518774538153602365)
  ·
    refine ⟨16382019569540451807600887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43685385518774538153602365 16382019569540451807600887)
    ·
      refine ⟨24573029354310677711401331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16382019569540451807600887 24573029354310677711401331)
      ·
        refine ⟨36859544031466016567101997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24573029354310677711401331 36859544031466016567101997)
        ·
          refine ⟨13822329011799756212663249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36859544031466016567101997 13822329011799756212663249)
          ·
            refine ⟨10366746758849817159497437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13822329011799756212663249 10366746758849817159497437)
            ·
              refine ⟨3887530034568681434811539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10366746758849817159497437 3887530034568681434811539)
              ·
                refine ⟨5831295051853022152217309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3887530034568681434811539 5831295051853022152217309)
                ·
                  refine ⟨2186735644444883307081491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5831295051853022152217309 2186735644444883307081491)
                  ·
                    refine ⟨3280103466667324960622237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2186735644444883307081491 3280103466667324960622237)
                    ·
                      refine ⟨1230038800000246860233339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3280103466667324960622237 1230038800000246860233339)
                      ·
                        rfl

theorem cell23_2395492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_2395492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395492 prefixEnd_2395492 := by exact prefixLift 2395492
  have htrace : WordTrace (prefixWord ++ tailWord_2395492) baseStart_2395492 baseEnd_2395492 := by
    simpa [prefixWord, tailWord_2395492, baseEnd_2395492] using wordTrace_append hprefix tailTrace_2395492
  have hstable : (prefixWord ++ tailWord_2395492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395492).length < 2 ^ (prefixWord ++ tailWord_2395492).sum := by decide
  have hdescent : baseEnd_2395492 < baseStart_2395492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395532 : List Nat := [2, 2, 1, 2, 1, 3, 5, 1, 1, 1, 4]
def baseStart_2395532 : Nat := 118140960795 + 2395532 * 2 ^ 59
def prefixEnd_2395532 : Nat := 4983230072969 + 3 ^ 40 * 2395532 * 2
def baseEnd_2395532 : Nat := 1230059339226426703733155

theorem tailTrace_2395532 : CollatzResearch.WordTrace tailWord_2395532 prefixEnd_2395532 1230059339226426703733155 := by
  unfold tailWord_2395532
  simp only [CollatzResearch.WordTrace]
  refine ⟨43686114978702081569330425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58248153304936108759107233 43686114978702081569330425)
  ·
    refine ⟨32764586234026561176997819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43686114978702081569330425 32764586234026561176997819)
    ·
      refine ⟨49146879351039841765496729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32764586234026561176997819 49146879351039841765496729)
      ·
        refine ⟨36860159513279881324122547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49146879351039841765496729 36860159513279881324122547)
        ·
          refine ⟨55290239269919821986183821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36860159513279881324122547 55290239269919821986183821)
          ·
            refine ⟨20733839726219933244818933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55290239269919821986183821 20733839726219933244818933)
            ·
              refine ⟨1943797474333118741701775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20733839726219933244818933 1943797474333118741701775)
              ·
                refine ⟨2915696211499678112552663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1943797474333118741701775 2915696211499678112552663)
                ·
                  refine ⟨4373544317249517168828995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2915696211499678112552663 4373544317249517168828995)
                  ·
                    refine ⟨6560316475874275753243493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4373544317249517168828995 6560316475874275753243493)
                    ·
                      refine ⟨1230059339226426703733155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6560316475874275753243493 1230059339226426703733155)
                      ·
                        rfl

theorem cell23_2395532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 1, 1, 4].length) (baseStart_2395532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395532 prefixEnd_2395532 := by exact prefixLift 2395532
  have htrace : WordTrace (prefixWord ++ tailWord_2395532) baseStart_2395532 baseEnd_2395532 := by
    simpa [prefixWord, tailWord_2395532, baseEnd_2395532] using wordTrace_append hprefix tailTrace_2395532
  have hstable : (prefixWord ++ tailWord_2395532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395532).length < 2 ^ (prefixWord ++ tailWord_2395532).sum := by decide
  have hdescent : baseEnd_2395532 < baseStart_2395532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395582 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3]
def baseStart_2395582 : Nat := 118140960795 + 2395582 * 2 ^ 59
def prefixEnd_2395582 : Nat := 4983230072969 + 3 ^ 40 * 2395582 * 2
def baseEnd_2395582 : Nat := 1230085013259151508107925

theorem tailTrace_2395582 : CollatzResearch.WordTrace tailWord_2395582 prefixEnd_2395582 1230085013259151508107925 := by
  unfold tailWord_2395582
  simp only [CollatzResearch.WordTrace]
  refine ⟨10921756700902877709747625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58249369071482014451987333 10921756700902877709747625)
  ·
    refine ⟨8191317525677158282310719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10921756700902877709747625 8191317525677158282310719)
    ·
      refine ⟨12286976288515737423466079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8191317525677158282310719 12286976288515737423466079)
      ·
        refine ⟨18430464432773606135199119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12286976288515737423466079 18430464432773606135199119)
        ·
          refine ⟨27645696649160409202798679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18430464432773606135199119 27645696649160409202798679)
          ·
            refine ⟨41468544973740613804198019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27645696649160409202798679 41468544973740613804198019)
            ·
              refine ⟨62202817460610920706297029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41468544973740613804198019 62202817460610920706297029)
              ·
                refine ⟨11663028273864547632430693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62202817460610920706297029 11663028273864547632430693)
                ·
                  refine ⟨2186817801349602681080755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11663028273864547632430693 2186817801349602681080755)
                  ·
                    refine ⟨3280226702024404021621133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2186817801349602681080755 3280226702024404021621133)
                    ·
                      refine ⟨1230085013259151508107925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3280226702024404021621133 1230085013259151508107925)
                      ·
                        rfl

theorem cell23_2395582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_2395582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395582 prefixEnd_2395582 := by exact prefixLift 2395582
  have htrace : WordTrace (prefixWord ++ tailWord_2395582) baseStart_2395582 baseEnd_2395582 := by
    simpa [prefixWord, tailWord_2395582, baseEnd_2395582] using wordTrace_append hprefix tailTrace_2395582
  have hstable : (prefixWord ++ tailWord_2395582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395582).length < 2 ^ (prefixWord ++ tailWord_2395582).sum := by decide
  have hdescent : baseEnd_2395582 < baseStart_2395582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395626 : List Nat := [3, 1, 3, 1, 4, 1, 2, 2, 1, 3, 2]
def baseStart_2395626 : Nat := 118140960795 + 2395626 * 2 ^ 59
def prefixEnd_2395626 : Nat := 4983230072969 + 3 ^ 40 * 2395626 * 2
def baseEnd_2395626 : Nat := 1230107606407949335957723

theorem tailTrace_2395626 : CollatzResearch.WordTrace tailWord_2395626 prefixEnd_2395626 1230107606407949335957723 := by
  unfold tailWord_2395626
  simp only [CollatzResearch.WordTrace]
  refine ⟨21843914604765904298145683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58250438946042411461721821 21843914604765904298145683)
  ·
    refine ⟨32765871907148856447218525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21843914604765904298145683 32765871907148856447218525)
    ·
      refine ⟨12287201965180821167706947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32765871907148856447218525 12287201965180821167706947)
      ·
        refine ⟨18430802947771231751560421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12287201965180821167706947 18430802947771231751560421)
        ·
          refine ⟨3455775552707105953417579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18430802947771231751560421 3455775552707105953417579)
          ·
            refine ⟨5183663329060658930126369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3455775552707105953417579 5183663329060658930126369)
            ·
              refine ⟨3887747496795494197594777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5183663329060658930126369 3887747496795494197594777)
              ·
                refine ⟨2915810622596620648196083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3887747496795494197594777 2915810622596620648196083)
                ·
                  refine ⟨4373715933894930972294125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2915810622596620648196083 4373715933894930972294125)
                  ·
                    refine ⟨1640143475210599114610297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4373715933894930972294125 1640143475210599114610297)
                    ·
                      refine ⟨1230107606407949335957723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1640143475210599114610297 1230107606407949335957723)
                      ·
                        rfl

theorem cell23_2395626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_2395626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395626 prefixEnd_2395626 := by exact prefixLift 2395626
  have htrace : WordTrace (prefixWord ++ tailWord_2395626) baseStart_2395626 baseEnd_2395626 := by
    simpa [prefixWord, tailWord_2395626, baseEnd_2395626] using wordTrace_append hprefix tailTrace_2395626
  have hstable : (prefixWord ++ tailWord_2395626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395626).length < 2 ^ (prefixWord ++ tailWord_2395626).sum := by decide
  have hdescent : baseEnd_2395626 < baseStart_2395626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395628 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 9]
def baseStart_2395628 : Nat := 118140960795 + 2395628 * 2 ^ 59
def prefixEnd_2395628 : Nat := 4983230072969 + 3 ^ 40 * 2395628 * 2
def baseEnd_2395628 : Nat := 136678737041028703125857

theorem tailTrace_2395628 : CollatzResearch.WordTrace tailWord_2395628 prefixEnd_2395628 136678737041028703125857 := by
  unfold tailWord_2395628
  simp only [CollatzResearch.WordTrace]
  refine ⟨43687865682528185767077769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58250487576704247689437025 43687865682528185767077769)
  ·
    refine ⟨32765899261896139325308327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43687865682528185767077769 32765899261896139325308327)
    ·
      refine ⟨49148848892844208987962491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32765899261896139325308327 49148848892844208987962491)
      ·
        refine ⟨73723273339266313481943737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49148848892844208987962491 73723273339266313481943737)
        ·
          refine ⟨55292455004449735111457803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73723273339266313481943737 55292455004449735111457803)
          ·
            refine ⟨82938682506674602667186705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55292455004449735111457803 82938682506674602667186705)
            ·
              refine ⟨62204011880005952000390029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82938682506674602667186705 62204011880005952000390029)
              ·
                refine ⟨23326504455002232000146261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62204011880005952000390029 23326504455002232000146261)
                ·
                  refine ⟨136678737041028703125857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23326504455002232000146261 136678737041028703125857)
                  ·
                    rfl

theorem cell23_2395628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 9].length) (baseStart_2395628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395628 prefixEnd_2395628 := by exact prefixLift 2395628
  have htrace : WordTrace (prefixWord ++ tailWord_2395628) baseStart_2395628 baseEnd_2395628 := by
    simpa [prefixWord, tailWord_2395628, baseEnd_2395628] using wordTrace_append hprefix tailTrace_2395628
  have hstable : (prefixWord ++ tailWord_2395628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395628).length < 2 ^ (prefixWord ++ tailWord_2395628).sum := by decide
  have hdescent : baseEnd_2395628 < baseStart_2395628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395648 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 6]
def baseStart_2395648 : Nat := 118140960795 + 2395648 * 2 ^ 59
def prefixEnd_2395648 : Nat := 4983230072969 + 3 ^ 40 * 2395648 * 2
def baseEnd_2395648 : Nat := 1230118902982348249882621

theorem tailTrace_2395648 : CollatzResearch.WordTrace tailWord_2395648 prefixEnd_2395648 1230118902982348249882621 := by
  unfold tailWord_2395648
  simp only [CollatzResearch.WordTrace]
  refine ⟨43688230412491957474941799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58250973883322609966589065 43688230412491957474941799)
  ·
    refine ⟨65532345618737936212412699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43688230412491957474941799 65532345618737936212412699)
    ·
      refine ⟨98298518428106904318619049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65532345618737936212412699 98298518428106904318619049)
      ·
        refine ⟨73723888821080178238964287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98298518428106904318619049 73723888821080178238964287)
        ·
          refine ⟨110585833231620267358446431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73723888821080178238964287 110585833231620267358446431)
          ·
            refine ⟨165878749847430401037669647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110585833231620267358446431 165878749847430401037669647)
            ·
              refine ⟨248818124771145601556504471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165878749847430401037669647 248818124771145601556504471)
              ·
                refine ⟨373227187156718402334756707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248818124771145601556504471 373227187156718402334756707)
                ·
                  refine ⟨559840780735077603502135061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 373227187156718402334756707 559840780735077603502135061)
                  ·
                    refine ⟨26242536596956762664162581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 559840780735077603502135061 26242536596956762664162581)
                    ·
                      refine ⟨1230118902982348249882621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26242536596956762664162581 1230118902982348249882621)
                      ·
                        rfl

theorem cell23_2395648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_2395648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395648 prefixEnd_2395648 := by exact prefixLift 2395648
  have htrace : WordTrace (prefixWord ++ tailWord_2395648) baseStart_2395648 baseEnd_2395648 := by
    simpa [prefixWord, tailWord_2395648, baseEnd_2395648] using wordTrace_append hprefix tailTrace_2395648
  have hstable : (prefixWord ++ tailWord_2395648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395648).length < 2 ^ (prefixWord ++ tailWord_2395648).sum := by decide
  have hdescent : baseEnd_2395648 < baseStart_2395648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395712 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 2, 4, 2]
def baseStart_2395712 : Nat := 118140960795 + 2395712 * 2 ^ 59
def prefixEnd_2395712 : Nat := 4983230072969 + 3 ^ 40 * 2395712 * 2
def baseEnd_2395712 : Nat := 1230151765744235999482327

theorem tailTrace_2395712 : CollatzResearch.WordTrace tailWord_2395712 prefixEnd_2395712 1230151765744235999482327 := by
  unfold tailWord_2395712
  simp only [CollatzResearch.WordTrace]
  refine ⟨43689397548376026940106695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58252530064501369253475593 43689397548376026940106695)
  ·
    refine ⟨65534096322564040410160043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43689397548376026940106695 65534096322564040410160043)
    ·
      refine ⟨98301144483846060615240065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65534096322564040410160043 98301144483846060615240065)
      ·
        refine ⟨73725858362884545461430049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98301144483846060615240065 73725858362884545461430049)
        ·
          refine ⟨55294393772163409096072537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73725858362884545461430049 55294393772163409096072537)
          ·
            refine ⟨41470795329122556822054403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55294393772163409096072537 41470795329122556822054403)
            ·
              refine ⟨62206192993683835233081605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41470795329122556822054403 62206192993683835233081605)
              ·
                refine ⟨11663661186315719106202801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62206192993683835233081605 11663661186315719106202801)
                ·
                  refine ⟨8747745889736789329652101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11663661186315719106202801 8747745889736789329652101)
                  ·
                    refine ⟨1640202354325647999309769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8747745889736789329652101 1640202354325647999309769)
                    ·
                      refine ⟨1230151765744235999482327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1640202354325647999309769 1230151765744235999482327)
                      ·
                        rfl

theorem cell23_2395712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 2, 4, 2].length) (baseStart_2395712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395712 prefixEnd_2395712 := by exact prefixLift 2395712
  have htrace : WordTrace (prefixWord ++ tailWord_2395712) baseStart_2395712 baseEnd_2395712 := by
    simpa [prefixWord, tailWord_2395712, baseEnd_2395712] using wordTrace_append hprefix tailTrace_2395712
  have hstable : (prefixWord ++ tailWord_2395712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395712).length < 2 ^ (prefixWord ++ tailWord_2395712).sum := by decide
  have hdescent : baseEnd_2395712 < baseStart_2395712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395715 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 3]
def baseStart_2395715 : Nat := 118140960795 + 2395715 * 2 ^ 59
def prefixEnd_2395715 : Nat := 4983230072969 + 3 ^ 40 * 2395715 * 2
def baseEnd_2395715 : Nat := 1230153306186199487744813

theorem tailTrace_2395715 : CollatzResearch.WordTrace tailWord_2395715 prefixEnd_2395715 1230153306186199487744813 := by
  unfold tailWord_2395715
  simp only [CollatzResearch.WordTrace]
  refine ⟨87378904515741185392572599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58252603010494123595048399 87378904515741185392572599)
  ·
    refine ⟨131068356773611778088858899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87378904515741185392572599 131068356773611778088858899)
    ·
      refine ⟨196602535160417667133288349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131068356773611778088858899 196602535160417667133288349)
      ·
        refine ⟨73725950685156625174983131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196602535160417667133288349 73725950685156625174983131)
        ·
          refine ⟨110588926027734937762474697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73725950685156625174983131 110588926027734937762474697)
          ·
            refine ⟨82941694520801203321856023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110588926027734937762474697 82941694520801203321856023)
            ·
              refine ⟨124412541781201804982784035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82941694520801203321856023 124412541781201804982784035)
              ·
                refine ⟨186618812671802707474176053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124412541781201804982784035 186618812671802707474176053)
                ·
                  refine ⟨17495513687981503825704005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 186618812671802707474176053 17495513687981503825704005)
                  ·
                    refine ⟨3280408816496531967319501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17495513687981503825704005 3280408816496531967319501)
                    ·
                      refine ⟨1230153306186199487744813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3280408816496531967319501 1230153306186199487744813)
                      ·
                        rfl

theorem cell23_2395715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 3].length) (baseStart_2395715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395715 prefixEnd_2395715 := by exact prefixLift 2395715
  have htrace : WordTrace (prefixWord ++ tailWord_2395715) baseStart_2395715 baseEnd_2395715 := by
    simpa [prefixWord, tailWord_2395715, baseEnd_2395715] using wordTrace_append hprefix tailTrace_2395715
  have hstable : (prefixWord ++ tailWord_2395715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395715).length < 2 ^ (prefixWord ++ tailWord_2395715).sum := by decide
  have hdescent : baseEnd_2395715 < baseStart_2395715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395722 : List Nat := [3, 1, 2, 1, 1, 3, 2, 3, 3, 4]
def baseStart_2395722 : Nat := 118140960795 + 2395722 * 2 ^ 59
def prefixEnd_2395722 : Nat := 4983230072969 + 3 ^ 40 * 2395722 * 2
def baseEnd_2395722 : Nat := 410052300183593653452427

theorem tailTrace_2395722 : CollatzResearch.WordTrace tailWord_2395722 prefixEnd_2395722 410052300183593653452427 := by
  unfold tailWord_2395722
  simp only [CollatzResearch.WordTrace]
  refine ⟨21844789956678956397019355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58252773217810550392051613 21844789956678956397019355)
  ·
    refine ⟨32767184935018434595529033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21844789956678956397019355 32767184935018434595529033)
    ·
      refine ⟨24575388701263825946646775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32767184935018434595529033 24575388701263825946646775)
      ·
        refine ⟨36863083051895738919970163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24575388701263825946646775 36863083051895738919970163)
        ·
          refine ⟨55294624577843608379955245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36863083051895738919970163 55294624577843608379955245)
          ·
            refine ⟨20735484216691353142483217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55294624577843608379955245 20735484216691353142483217)
            ·
              refine ⟨15551613162518514856862413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20735484216691353142483217 15551613162518514856862413)
              ·
                refine ⟨5831854935944443071323405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15551613162518514856862413 5831854935944443071323405)
                ·
                  refine ⟨2186945600979166151746277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5831854935944443071323405 2186945600979166151746277)
                  ·
                    refine ⟨410052300183593653452427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2186945600979166151746277 410052300183593653452427)
                    ·
                      rfl

theorem cell23_2395722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_2395722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395722 prefixEnd_2395722 := by exact prefixLift 2395722
  have htrace : WordTrace (prefixWord ++ tailWord_2395722) baseStart_2395722 baseEnd_2395722 := by
    simpa [prefixWord, tailWord_2395722, baseEnd_2395722] using wordTrace_append hprefix tailTrace_2395722
  have hstable : (prefixWord ++ tailWord_2395722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395722).length < 2 ^ (prefixWord ++ tailWord_2395722).sum := by decide
  have hdescent : baseEnd_2395722 < baseStart_2395722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395732 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 1, 4, 3]
def baseStart_2395732 : Nat := 118140960795 + 2395732 * 2 ^ 59
def prefixEnd_2395732 : Nat := 4983230072969 + 3 ^ 40 * 2395732 * 2
def baseEnd_2395732 : Nat := 1230162035357325921232235

theorem tailTrace_2395732 : CollatzResearch.WordTrace tailWord_2395732 prefixEnd_2395732 1230162035357325921232235 := by
  unfold tailWord_2395732
  simp only [CollatzResearch.WordTrace]
  refine ⟨43689762278339798647970725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58253016371119731530627633 43689762278339798647970725)
  ·
    refine ⟨8191830427188712246494511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43689762278339798647970725 8191830427188712246494511)
    ·
      refine ⟨12287745640783068369741767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8191830427188712246494511 12287745640783068369741767)
      ·
        refine ⟨18431618461174602554612651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12287745640783068369741767 18431618461174602554612651)
        ·
          refine ⟨27647427691761903831918977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18431618461174602554612651 27647427691761903831918977)
          ·
            refine ⟨20735570768821427873939233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27647427691761903831918977 20735570768821427873939233)
            ·
              refine ⟨15551678076616070905454425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20735570768821427873939233 15551678076616070905454425)
              ·
                refine ⟨11663758557462053179090819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15551678076616070905454425 11663758557462053179090819)
                ·
                  refine ⟨17495637836193079768636229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11663758557462053179090819 17495637836193079768636229)
                  ·
                    refine ⟨3280432094286202456619293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17495637836193079768636229 3280432094286202456619293)
                    ·
                      refine ⟨1230162035357325921232235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3280432094286202456619293 1230162035357325921232235)
                      ·
                        rfl

theorem cell23_2395732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_2395732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395732 prefixEnd_2395732 := by exact prefixLift 2395732
  have htrace : WordTrace (prefixWord ++ tailWord_2395732) baseStart_2395732 baseEnd_2395732 := by
    simpa [prefixWord, tailWord_2395732, baseEnd_2395732] using wordTrace_append hprefix tailTrace_2395732
  have hstable : (prefixWord ++ tailWord_2395732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395732).length < 2 ^ (prefixWord ++ tailWord_2395732).sum := by decide
  have hdescent : baseEnd_2395732 < baseStart_2395732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395749 : List Nat := [1, 3, 1, 3, 3, 1, 3, 1, 2, 2, 3]
def baseStart_2395749 : Nat := 118140960795 + 2395749 * 2 ^ 59
def prefixEnd_2395749 : Nat := 4983230072969 + 3 ^ 40 * 2395749 * 2
def baseEnd_2395749 : Nat := 1230170764528452354719657

theorem tailTrace_2395749 : CollatzResearch.WordTrace tailWord_2395749 prefixEnd_2395749 1230170764528452354719657 := by
  unfold tailWord_2395749
  simp only [CollatzResearch.WordTrace]
  refine ⟨87380144597618009199310301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58253429731745339466206867 87380144597618009199310301)
  ·
    refine ⟨32767554224106753449741363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87380144597618009199310301 32767554224106753449741363)
    ·
      refine ⟨49151331336160130174612045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32767554224106753449741363 49151331336160130174612045)
      ·
        refine ⟨18431749251060048815479517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49151331336160130174612045 18431749251060048815479517)
        ·
          refine ⟨6911905969147518305804819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18431749251060048815479517 6911905969147518305804819)
          ·
            refine ⟨10367858953721277458707229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6911905969147518305804819 10367858953721277458707229)
            ·
              refine ⟨3887947107645479047015211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10367858953721277458707229 3887947107645479047015211)
              ·
                refine ⟨5831920661468218570522817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3887947107645479047015211 5831920661468218570522817)
                ·
                  refine ⟨4373940496101163927892113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5831920661468218570522817 4373940496101163927892113)
                  ·
                    refine ⟨3280455372075872945919085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4373940496101163927892113 3280455372075872945919085)
                    ·
                      refine ⟨1230170764528452354719657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3280455372075872945919085 1230170764528452354719657)
                      ·
                        rfl

theorem cell23_2395749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_2395749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395749 prefixEnd_2395749 := by exact prefixLift 2395749
  have htrace : WordTrace (prefixWord ++ tailWord_2395749) baseStart_2395749 baseEnd_2395749 := by
    simpa [prefixWord, tailWord_2395749, baseEnd_2395749] using wordTrace_append hprefix tailTrace_2395749
  have hstable : (prefixWord ++ tailWord_2395749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395749).length < 2 ^ (prefixWord ++ tailWord_2395749).sum := by decide
  have hdescent : baseEnd_2395749 < baseStart_2395749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395799 : List Nat := [1, 1, 3, 3, 2, 3, 2, 2, 1, 5]
def baseStart_2395799 : Nat := 118140960795 + 2395799 * 2 ^ 59
def prefixEnd_2395799 : Nat := 4983230072969 + 3 ^ 40 * 2395799 * 2
def baseEnd_2395799 : Nat := 410065479520392386364809

theorem tailTrace_2395799 : CollatzResearch.WordTrace tailWord_2395799 prefixEnd_2395799 410065479520392386364809 := by
  unfold tailWord_2395799
  simp only [CollatzResearch.WordTrace]
  refine ⟨87381968247436867738630451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58254645498291245159086967 87381968247436867738630451)
  ·
    refine ⟨131072952371155301607945677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87381968247436867738630451 131072952371155301607945677)
    ·
      refine ⟨49152357139183238102979629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131072952371155301607945677 49152357139183238102979629)
      ·
        refine ⟨18432133927193714288617361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49152357139183238102979629 18432133927193714288617361)
        ·
          refine ⟨13824100445395285716463021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18432133927193714288617361 13824100445395285716463021)
          ·
            refine ⟨5184037667023232143673633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13824100445395285716463021 5184037667023232143673633)
            ·
              refine ⟨3888028250267424107755225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5184037667023232143673633 3888028250267424107755225)
              ·
                refine ⟨2916021187700568080816419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3888028250267424107755225 2916021187700568080816419)
                ·
                  refine ⟨4374031781550852121224629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2916021187700568080816419 4374031781550852121224629)
                  ·
                    refine ⟨410065479520392386364809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4374031781550852121224629 410065479520392386364809)
                    ·
                      rfl

theorem cell23_2395799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 5].length) (baseStart_2395799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395799 prefixEnd_2395799 := by exact prefixLift 2395799
  have htrace : WordTrace (prefixWord ++ tailWord_2395799) baseStart_2395799 baseEnd_2395799 := by
    simpa [prefixWord, tailWord_2395799, baseEnd_2395799] using wordTrace_append hprefix tailTrace_2395799
  have hstable : (prefixWord ++ tailWord_2395799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395799).length < 2 ^ (prefixWord ++ tailWord_2395799).sum := by decide
  have hdescent : baseEnd_2395799 < baseStart_2395799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395806 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 1, 5, 2]
def baseStart_2395806 : Nat := 118140960795 + 2395806 * 2 ^ 59
def prefixEnd_2395806 : Nat := 4983230072969 + 3 ^ 40 * 2395806 * 2
def baseEnd_2395806 : Nat := 1230200032925758631706895

theorem tailTrace_2395806 : CollatzResearch.WordTrace tailWord_2395806 prefixEnd_2395806 1230200032925758631706895 := by
  unfold tailWord_2395806
  simp only [CollatzResearch.WordTrace]
  refine ⟨10922777944801438491766909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58254815705607671956090181 10922777944801438491766909)
  ·
    refine ⟨4096041729300539434412591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10922777944801438491766909 4096041729300539434412591)
    ·
      refine ⟨6144062593950809151618887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4096041729300539434412591 6144062593950809151618887)
      ·
        refine ⟨9216093890926213727428331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6144062593950809151618887 9216093890926213727428331)
        ·
          refine ⟨13824140836389320591142497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9216093890926213727428331 13824140836389320591142497)
          ·
            refine ⟨10368105627291990443356873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13824140836389320591142497 10368105627291990443356873)
            ·
              refine ⟨7776079220468992832517655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10368105627291990443356873 7776079220468992832517655)
              ·
                refine ⟨11664118830703489248776483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7776079220468992832517655 11664118830703489248776483)
                ·
                  refine ⟨17496178246055233873164725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11664118830703489248776483 17496178246055233873164725)
                  ·
                    refine ⟨1640266710567678175609193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17496178246055233873164725 1640266710567678175609193)
                    ·
                      refine ⟨1230200032925758631706895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1640266710567678175609193 1230200032925758631706895)
                      ·
                        rfl

theorem cell23_2395806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_2395806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395806 prefixEnd_2395806 := by exact prefixLift 2395806
  have htrace : WordTrace (prefixWord ++ tailWord_2395806) baseStart_2395806 baseEnd_2395806 := by
    simpa [prefixWord, tailWord_2395806, baseEnd_2395806] using wordTrace_append hprefix tailTrace_2395806
  have hstable : (prefixWord ++ tailWord_2395806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395806).length < 2 ^ (prefixWord ++ tailWord_2395806).sum := by decide
  have hdescent : baseEnd_2395806 < baseStart_2395806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395830 : List Nat := [5, 1, 3, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_2395830 : Nat := 118140960795 + 2395830 * 2 ^ 59
def prefixEnd_2395830 : Nat := 4983230072969 + 3 ^ 40 * 2395830 * 2
def baseEnd_2395830 : Nat := 1230212356461466537806785

theorem tailTrace_2395830 : CollatzResearch.WordTrace tailWord_2395830 prefixEnd_2395830 1230212356461466537806785 := by
  unfold tailWord_2395830
  simp only [CollatzResearch.WordTrace]
  refine ⟨5461443681895285002063059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58255399273549706688672629 5461443681895285002063059)
  ·
    refine ⟨8192165522842927503094589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5461443681895285002063059 8192165522842927503094589)
    ·
      refine ⟨3072062071066097813660471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8192165522842927503094589 3072062071066097813660471)
      ·
        refine ⟨4608093106599146720490707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3072062071066097813660471 4608093106599146720490707)
        ·
          refine ⟨6912139659898720080736061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4608093106599146720490707 6912139659898720080736061)
          ·
            refine ⟨2592052372462020030276023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6912139659898720080736061 2592052372462020030276023)
            ·
              refine ⟨3888078558693030045414035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2592052372462020030276023 3888078558693030045414035)
              ·
                refine ⟨5832117838039545068121053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3888078558693030045414035 5832117838039545068121053)
                ·
                  refine ⟨2187044189264829400545395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5832117838039545068121053 2187044189264829400545395)
                  ·
                    refine ⟨3280566283897244100818093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2187044189264829400545395 3280566283897244100818093)
                    ·
                      refine ⟨1230212356461466537806785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3280566283897244100818093 1230212356461466537806785)
                      ·
                        rfl

theorem cell23_2395830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_2395830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395830 prefixEnd_2395830 := by exact prefixLift 2395830
  have htrace : WordTrace (prefixWord ++ tailWord_2395830) baseStart_2395830 baseEnd_2395830 := by
    simpa [prefixWord, tailWord_2395830, baseEnd_2395830] using wordTrace_append hprefix tailTrace_2395830
  have hstable : (prefixWord ++ tailWord_2395830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395830).length < 2 ^ (prefixWord ++ tailWord_2395830).sum := by decide
  have hdescent : baseEnd_2395830 < baseStart_2395830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395853 : List Nat := [1, 6, 2, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_2395853 : Nat := 118140960795 + 2395853 * 2 ^ 59
def prefixEnd_2395853 : Nat := 4983230072969 + 3 ^ 40 * 2395853 * 2
def baseEnd_2395853 : Nat := 1230224166516519947819179

theorem tailTrace_2395853 : CollatzResearch.WordTrace tailWord_2395853 prefixEnd_2395853 1230224166516519947819179 := by
  unfold tailWord_2395853
  simp only [CollatzResearch.WordTrace]
  refine ⟨87383937789241234961096213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58255958526160823307397475 87383937789241234961096213)
  ·
    refine ⟨4096122083870682888801385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 87383937789241234961096213 4096122083870682888801385)
    ·
      refine ⟨3072091562903012166601039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4096122083870682888801385 3072091562903012166601039)
      ·
        refine ⟨4608137344354518249901559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3072091562903012166601039 4608137344354518249901559)
        ·
          refine ⟨6912206016531777374852339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4608137344354518249901559 6912206016531777374852339)
          ·
            refine ⟨10368309024797666062278509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6912206016531777374852339 10368309024797666062278509)
            ·
              refine ⟨3888115884299124773354441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10368309024797666062278509 3888115884299124773354441)
              ·
                refine ⟨2916086913224343580015831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3888115884299124773354441 2916086913224343580015831)
                ·
                  refine ⟨4374130369836515370023747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2916086913224343580015831 4374130369836515370023747)
                  ·
                    refine ⟨6561195554754773055035621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4374130369836515370023747 6561195554754773055035621)
                    ·
                      refine ⟨1230224166516519947819179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6561195554754773055035621 1230224166516519947819179)
                      ·
                        rfl

theorem cell23_2395853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_2395853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395853 prefixEnd_2395853 := by exact prefixLift 2395853
  have htrace : WordTrace (prefixWord ++ tailWord_2395853) baseStart_2395853 baseEnd_2395853 := by
    simpa [prefixWord, tailWord_2395853, baseEnd_2395853] using wordTrace_append hprefix tailTrace_2395853
  have hstable : (prefixWord ++ tailWord_2395853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395853).length < 2 ^ (prefixWord ++ tailWord_2395853).sum := by decide
  have hdescent : baseEnd_2395853 < baseStart_2395853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395873 : List Nat := [1, 2, 3, 1, 5, 1, 3, 1, 1, 2, 3]
def baseStart_2395873 : Nat := 118140960795 + 2395873 * 2 ^ 59
def prefixEnd_2395873 : Nat := 4983230072969 + 3 ^ 40 * 2395873 * 2
def baseEnd_2395873 : Nat := 1230234436129609869569087

theorem tailTrace_2395873 : CollatzResearch.WordTrace tailWord_2395873 prefixEnd_2395873 1230234436129609869569087 := by
  unfold tailWord_2395873
  simp only [CollatzResearch.WordTrace]
  refine ⟨87384667249168778376824273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58256444832779185584549515 87384667249168778376824273)
  ·
    refine ⟨65538500436876583782618205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87384667249168778376824273 65538500436876583782618205)
    ·
      refine ⟨24576937663828718918481827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65538500436876583782618205 24576937663828718918481827)
      ·
        refine ⟨36865406495743078377722741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24576937663828718918481827 36865406495743078377722741)
        ·
          refine ⟨3456131858975913597911507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36865406495743078377722741 3456131858975913597911507)
          ·
            refine ⟨5184197788463870396867261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3456131858975913597911507 5184197788463870396867261)
            ·
              refine ⟨1944074170673951398825223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5184197788463870396867261 1944074170673951398825223)
              ·
                refine ⟨2916111256010927098237835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1944074170673951398825223 2916111256010927098237835)
                ·
                  refine ⟨4374166884016390647356753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2916111256010927098237835 4374166884016390647356753)
                  ·
                    refine ⟨3280625163012292985517565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4374166884016390647356753 3280625163012292985517565)
                    ·
                      refine ⟨1230234436129609869569087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3280625163012292985517565 1230234436129609869569087)
                      ·
                        rfl

theorem cell23_2395873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 1, 2, 3].length) (baseStart_2395873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395873 prefixEnd_2395873 := by exact prefixLift 2395873
  have htrace : WordTrace (prefixWord ++ tailWord_2395873) baseStart_2395873 baseEnd_2395873 := by
    simpa [prefixWord, tailWord_2395873, baseEnd_2395873] using wordTrace_append hprefix tailTrace_2395873
  have hstable : (prefixWord ++ tailWord_2395873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395873).length < 2 ^ (prefixWord ++ tailWord_2395873).sum := by decide
  have hdescent : baseEnd_2395873 < baseStart_2395873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395882 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_2395882 : Nat := 118140960795 + 2395882 * 2 ^ 59
def prefixEnd_2395882 : Nat := 4983230072969 + 3 ^ 40 * 2395882 * 2
def baseEnd_2395882 : Nat := 1230239057455500334356545

theorem tailTrace_2395882 : CollatzResearch.WordTrace tailWord_2395882 prefixEnd_2395882 1230239057455500334356545 := by
  unfold tailWord_2395882
  simp only [CollatzResearch.WordTrace]
  refine ⟨21846248876534043228475475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58256663670757448609267933 21846248876534043228475475)
  ·
    refine ⟨32769373314801064842713213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21846248876534043228475475 32769373314801064842713213)
    ·
      refine ⟨12288514993050399316017455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32769373314801064842713213 12288514993050399316017455)
      ·
        refine ⟨18432772489575598974026183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12288514993050399316017455 18432772489575598974026183)
        ·
          refine ⟨27649158734363398461039275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18432772489575598974026183 27649158734363398461039275)
          ·
            refine ⟨41473738101545097691558913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27649158734363398461039275 41473738101545097691558913)
            ·
              refine ⟨31105303576158823268669185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41473738101545097691558913 31105303576158823268669185)
              ·
                refine ⟨23328977682119117451501889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31105303576158823268669185 23328977682119117451501889)
                ·
                  refine ⟨17496733261589338088626417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23328977682119117451501889 17496733261589338088626417)
                  ·
                    refine ⟨13122549946192003566469813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17496733261589338088626417 13122549946192003566469813)
                    ·
                      refine ⟨1230239057455500334356545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13122549946192003566469813 1230239057455500334356545)
                      ·
                        rfl

theorem cell23_2395882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_2395882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395882 prefixEnd_2395882 := by exact prefixLift 2395882
  have htrace : WordTrace (prefixWord ++ tailWord_2395882) baseStart_2395882 baseEnd_2395882 := by
    simpa [prefixWord, tailWord_2395882, baseEnd_2395882] using wordTrace_append hprefix tailTrace_2395882
  have hstable : (prefixWord ++ tailWord_2395882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395882).length < 2 ^ (prefixWord ++ tailWord_2395882).sum := by decide
  have hdescent : baseEnd_2395882 < baseStart_2395882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395924 : List Nat := [2, 4, 4, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_2395924 : Nat := 118140960795 + 2395924 * 2 ^ 59
def prefixEnd_2395924 : Nat := 4983230072969 + 3 ^ 40 * 2395924 * 2
def baseEnd_2395924 : Nat := 1230260623642989170031353

theorem tailTrace_2395924 : CollatzResearch.WordTrace tailWord_2395924 prefixEnd_2395924 1230260623642989170031353 := by
  unfold tailWord_2395924
  simp only [CollatzResearch.WordTrace]
  refine ⟨43693263685992007043465413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58257684914656009391287217 43693263685992007043465413)
  ·
    refine ⟨8192486941123501320649765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43693263685992007043465413 8192486941123501320649765)
    ·
      refine ⟨1536091301460656497621831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8192486941123501320649765 1536091301460656497621831)
      ·
        refine ⟨2304136952190984746432747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1536091301460656497621831 2304136952190984746432747)
        ·
          refine ⟨3456205428286477119649121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2304136952190984746432747 3456205428286477119649121)
          ·
            refine ⟨2592154071214857839736841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3456205428286477119649121 2592154071214857839736841)
            ·
              refine ⟨1944115553411143379802631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2592154071214857839736841 1944115553411143379802631)
              ·
                refine ⟨2916173330116715069703947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1944115553411143379802631 2916173330116715069703947)
                ·
                  refine ⟨4374259995175072604555921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2916173330116715069703947 4374259995175072604555921)
                  ·
                    refine ⟨3280694996381304453416941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4374259995175072604555921 3280694996381304453416941)
                    ·
                      refine ⟨1230260623642989170031353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3280694996381304453416941 1230260623642989170031353)
                      ·
                        rfl

theorem cell23_2395924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_2395924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395924 prefixEnd_2395924 := by exact prefixLift 2395924
  have htrace : WordTrace (prefixWord ++ tailWord_2395924) baseStart_2395924 baseEnd_2395924 := by
    simpa [prefixWord, tailWord_2395924, baseEnd_2395924] using wordTrace_append hprefix tailTrace_2395924
  have hstable : (prefixWord ++ tailWord_2395924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395924).length < 2 ^ (prefixWord ++ tailWord_2395924).sum := by decide
  have hdescent : baseEnd_2395924 < baseStart_2395924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395930 : List Nat := [3, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2]
def baseStart_2395930 : Nat := 118140960795 + 2395930 * 2 ^ 59
def prefixEnd_2395930 : Nat := 4983230072969 + 3 ^ 40 * 2395930 * 2
def baseEnd_2395930 : Nat := 1230263704526916146556325

theorem tailTrace_2395930 : CollatzResearch.WordTrace tailWord_2395930 prefixEnd_2395930 1230263704526916146556325 := by
  unfold tailWord_2395930
  simp only [CollatzResearch.WordTrace]
  refine ⟨21846686552490569277912311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58257830806641518074432829 21846686552490569277912311)
  ·
    refine ⟨32770029828735853916868467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21846686552490569277912311 32770029828735853916868467)
    ·
      refine ⟨49155044743103780875302701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32770029828735853916868467 49155044743103780875302701)
      ·
        refine ⟨18433141778663917828238513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49155044743103780875302701 18433141778663917828238513)
        ·
          refine ⟨13824856333997938371178885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18433141778663917828238513 13824856333997938371178885)
          ·
            refine ⟨2592160562624613444596041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13824856333997938371178885 2592160562624613444596041)
            ·
              refine ⟨1944120421968460083447031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2592160562624613444596041 1944120421968460083447031)
              ·
                refine ⟨2916180632952690125170547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1944120421968460083447031 2916180632952690125170547)
                ·
                  refine ⟨4374270949429035187755821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2916180632952690125170547 4374270949429035187755821)
                  ·
                    refine ⟨1640351606035888195408433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4374270949429035187755821 1640351606035888195408433)
                    ·
                      refine ⟨1230263704526916146556325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1640351606035888195408433 1230263704526916146556325)
                      ·
                        rfl

theorem cell23_2395930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_2395930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395930 prefixEnd_2395930 := by exact prefixLift 2395930
  have htrace : WordTrace (prefixWord ++ tailWord_2395930) baseStart_2395930 baseEnd_2395930 := by
    simpa [prefixWord, tailWord_2395930, baseEnd_2395930] using wordTrace_append hprefix tailTrace_2395930
  have hstable : (prefixWord ++ tailWord_2395930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395930).length < 2 ^ (prefixWord ++ tailWord_2395930).sum := by decide
  have hdescent : baseEnd_2395930 < baseStart_2395930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395932 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 9]
def baseStart_2395932 : Nat := 118140960795 + 2395932 * 2 ^ 59
def prefixEnd_2395932 : Nat := 4983230072969 + 3 ^ 40 * 2395932 * 2
def baseEnd_2395932 : Nat := 136696081276469459859035

theorem tailTrace_2395932 : CollatzResearch.WordTrace tailWord_2395932 prefixEnd_2395932 136696081276469459859035 := by
  unfold tailWord_2395932
  simp only [CollatzResearch.WordTrace]
  refine ⟨43693409577977515726611025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58257879437303354302148033 43693409577977515726611025)
  ·
    refine ⟨32770057183483136794958269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43693409577977515726611025 32770057183483136794958269)
    ·
      refine ⟨12288771443806176298109351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32770057183483136794958269 12288771443806176298109351)
      ·
        refine ⟨18433157165709264447164027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12288771443806176298109351 18433157165709264447164027)
        ·
          refine ⟨27649735748563896670746041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18433157165709264447164027 27649735748563896670746041)
          ·
            refine ⟨20737301811422922503059531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27649735748563896670746041 20737301811422922503059531)
            ·
              refine ⟨31105952717134383754589297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20737301811422922503059531 31105952717134383754589297)
              ·
                refine ⟨23329464537850787815941973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31105952717134383754589297 23329464537850787815941973)
                ·
                  refine ⟨136696081276469459859035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23329464537850787815941973 136696081276469459859035)
                  ·
                    rfl

theorem cell23_2395932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 9].length) (baseStart_2395932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395932 prefixEnd_2395932 := by exact prefixLift 2395932
  have htrace : WordTrace (prefixWord ++ tailWord_2395932) baseStart_2395932 baseEnd_2395932 := by
    simpa [prefixWord, tailWord_2395932, baseEnd_2395932] using wordTrace_append hprefix tailTrace_2395932
  have hstable : (prefixWord ++ tailWord_2395932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395932).length < 2 ^ (prefixWord ++ tailWord_2395932).sum := by decide
  have hdescent : baseEnd_2395932 < baseStart_2395932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395956 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_2395956 : Nat := 118140960795 + 2395956 * 2 ^ 59
def prefixEnd_2395956 : Nat := 4983230072969 + 3 ^ 40 * 2395956 * 2
def baseEnd_2395956 : Nat := 1230277055023933044831205

theorem tailTrace_2395956 : CollatzResearch.WordTrace tailWord_2395956 prefixEnd_2395956 1230277055023933044831205 := by
  unfold tailWord_2395956
  simp only [CollatzResearch.WordTrace]
  refine ⟨43693847253934041776047861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58258463005245389034730481 43693847253934041776047861)
  ·
    refine ⟨4096298180056316416504487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43693847253934041776047861 4096298180056316416504487)
    ·
      refine ⟨6144447270084474624756731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4096298180056316416504487 6144447270084474624756731)
      ·
        refine ⟨9216670905126711937135097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6144447270084474624756731 9216670905126711937135097)
        ·
          refine ⟨6912503178845033952851323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9216670905126711937135097 6912503178845033952851323)
          ·
            refine ⟨10368754768267550929276985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6912503178845033952851323 10368754768267550929276985)
            ·
              refine ⟨7776566076200663196957739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10368754768267550929276985 7776566076200663196957739)
              ·
                refine ⟨11664849114300994795436609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7776566076200663196957739 11664849114300994795436609)
                ·
                  refine ⟨8748636835725746096577457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11664849114300994795436609 8748636835725746096577457)
                  ·
                    refine ⟨6561477626794309572433093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8748636835725746096577457 6561477626794309572433093)
                    ·
                      refine ⟨1230277055023933044831205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6561477626794309572433093 1230277055023933044831205)
                      ·
                        rfl

theorem cell23_2395956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_2395956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395956 prefixEnd_2395956 := by exact prefixLift 2395956
  have htrace : WordTrace (prefixWord ++ tailWord_2395956) baseStart_2395956 baseEnd_2395956 := by
    simpa [prefixWord, tailWord_2395956, baseEnd_2395956] using wordTrace_append hprefix tailTrace_2395956
  have hstable : (prefixWord ++ tailWord_2395956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395956).length < 2 ^ (prefixWord ++ tailWord_2395956).sum := by decide
  have hdescent : baseEnd_2395956 < baseStart_2395956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395960 : List Nat := [2, 1, 2, 1, 3, 4, 3, 1, 2, 2, 2]
def baseStart_2395960 : Nat := 118140960795 + 2395960 * 2 ^ 59
def prefixEnd_2395960 : Nat := 4983230072969 + 3 ^ 40 * 2395960 * 2
def baseEnd_2395960 : Nat := 1230279108946551029181187

theorem tailTrace_2395960 : CollatzResearch.WordTrace tailWord_2395960 prefixEnd_2395960 1230279108946551029181187 := by
  unfold tailWord_2395960
  simp only [CollatzResearch.WordTrace]
  refine ⟨43693920199926796117620667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58258560266569061490160889 43693920199926796117620667)
  ·
    refine ⟨65540880299890194176431001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43693920199926796117620667 65540880299890194176431001)
    ·
      refine ⟨49155660224917645632323251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65540880299890194176431001 49155660224917645632323251)
      ·
        refine ⟨73733490337376468448484877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49155660224917645632323251 73733490337376468448484877)
        ·
          refine ⟨27650058876516175668181829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73733490337376468448484877 27650058876516175668181829)
          ·
            refine ⟨5184386039346782937784093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27650058876516175668181829 5184386039346782937784093)
            ·
              refine ⟨1944144764755043601669035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5184386039346782937784093 1944144764755043601669035)
              ·
                refine ⟨2916217147132565402503553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1944144764755043601669035 2916217147132565402503553)
                ·
                  refine ⟨2187162860349424051877665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2916217147132565402503553 2187162860349424051877665)
                  ·
                    refine ⟨1640372145262068038908249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2187162860349424051877665 1640372145262068038908249)
                    ·
                      refine ⟨1230279108946551029181187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1640372145262068038908249 1230279108946551029181187)
                      ·
                        rfl

theorem cell23_2395960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 2, 2, 2].length) (baseStart_2395960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395960 prefixEnd_2395960 := by exact prefixLift 2395960
  have htrace : WordTrace (prefixWord ++ tailWord_2395960) baseStart_2395960 baseEnd_2395960 := by
    simpa [prefixWord, tailWord_2395960, baseEnd_2395960] using wordTrace_append hprefix tailTrace_2395960
  have hstable : (prefixWord ++ tailWord_2395960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395960).length < 2 ^ (prefixWord ++ tailWord_2395960).sum := by decide
  have hdescent : baseEnd_2395960 < baseStart_2395960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2395999 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 4]
def baseStart_2395999 : Nat := 118140960795 + 2395999 * 2 ^ 59
def prefixEnd_2395999 : Nat := 4983230072969 + 3 ^ 40 * 2395999 * 2
def baseEnd_2395999 : Nat := 1230299134692076376593507

theorem tailTrace_2395999 : CollatzResearch.WordTrace tailWord_2395999 prefixEnd_2395999 1230299134692076376593507 := by
  unfold tailWord_2395999
  simp only [CollatzResearch.WordTrace]
  refine ⟨87389262846712301895911051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58259508564474867930607367 87389262846712301895911051)
  ·
    refine ⟨131083894270068452843866577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87389262846712301895911051 131083894270068452843866577)
    ·
      refine ⟨98312920702551339632899933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131083894270068452843866577 98312920702551339632899933)
      ·
        refine ⟨36867345263456752362337475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98312920702551339632899933 36867345263456752362337475)
        ·
          refine ⟨55301017895185128543506213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36867345263456752362337475 55301017895185128543506213)
          ·
            refine ⟨10368940855347211601907415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55301017895185128543506213 10368940855347211601907415)
            ·
              refine ⟨15553411283020817402861123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10368940855347211601907415 15553411283020817402861123)
              ·
                refine ⟨23330116924531226104291685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15553411283020817402861123 23330116924531226104291685)
                ·
                  refine ⟨4374396923349604894554691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23330116924531226104291685 4374396923349604894554691)
                  ·
                    refine ⟨6561595385024407341832037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4374396923349604894554691 6561595385024407341832037)
                    ·
                      refine ⟨1230299134692076376593507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6561595385024407341832037 1230299134692076376593507)
                      ·
                        rfl

theorem cell23_2395999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_2395999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2395999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2395999 prefixEnd_2395999 := by exact prefixLift 2395999
  have htrace : WordTrace (prefixWord ++ tailWord_2395999) baseStart_2395999 baseEnd_2395999 := by
    simpa [prefixWord, tailWord_2395999, baseEnd_2395999] using wordTrace_append hprefix tailTrace_2395999
  have hstable : (prefixWord ++ tailWord_2395999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2395999).length < 2 ^ (prefixWord ++ tailWord_2395999).sum := by decide
  have hdescent : baseEnd_2395999 < baseStart_2395999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2395999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396019 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 3]
def baseStart_2396019 : Nat := 118140960795 + 2396019 * 2 ^ 59
def prefixEnd_2396019 : Nat := 4983230072969 + 3 ^ 40 * 2396019 * 2
def baseEnd_2396019 : Nat := 1230309404305166298343415

theorem tailTrace_2396019 : CollatzResearch.WordTrace tailWord_2396019 prefixEnd_2396019 1230309404305166298343415 := by
  unfold tailWord_2396019
  simp only [CollatzResearch.WordTrace]
  refine ⟨87389992306639845311639111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58259994871093230207759407 87389992306639845311639111)
  ·
    refine ⟨131084988459959767967458667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87389992306639845311639111 131084988459959767967458667)
    ·
      refine ⟨196627482689939651951188001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131084988459959767967458667 196627482689939651951188001)
      ·
        refine ⟨147470612017454738963391001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196627482689939651951188001 147470612017454738963391001)
        ·
          refine ⟨110602959013091054222543251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147470612017454738963391001 110602959013091054222543251)
          ·
            refine ⟨165904438519636581333814877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110602959013091054222543251 165904438519636581333814877)
            ·
              refine ⟨62214164444863718000180579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165904438519636581333814877 62214164444863718000180579)
              ·
                refine ⟨93321246667295577000270869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62214164444863718000180579 93321246667295577000270869)
                ·
                  refine ⟨4374433437529480171887697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 93321246667295577000270869 4374433437529480171887697)
                  ·
                    refine ⟨3280825078147110128915773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4374433437529480171887697 3280825078147110128915773)
                    ·
                      refine ⟨1230309404305166298343415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3280825078147110128915773 1230309404305166298343415)
                      ·
                        rfl

theorem cell23_2396019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 3].length) (baseStart_2396019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396019 prefixEnd_2396019 := by exact prefixLift 2396019
  have htrace : WordTrace (prefixWord ++ tailWord_2396019) baseStart_2396019 baseEnd_2396019 := by
    simpa [prefixWord, tailWord_2396019, baseEnd_2396019] using wordTrace_append hprefix tailTrace_2396019
  have hstable : (prefixWord ++ tailWord_2396019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396019).length < 2 ^ (prefixWord ++ tailWord_2396019).sum := by decide
  have hdescent : baseEnd_2396019 < baseStart_2396019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396036 : List Nat := [2, 3, 2, 1, 1, 1, 3, 3, 2, 2, 3]
def baseStart_2396036 : Nat := 118140960795 + 2396036 * 2 ^ 59
def prefixEnd_2396036 : Nat := 4983230072969 + 3 ^ 40 * 2396036 * 2
def baseEnd_2396036 : Nat := 1230318133476292731830837

theorem tailTrace_2396036 : CollatzResearch.WordTrace tailWord_2396036 prefixEnd_2396036 1230318133476292731830837 := by
  unfold tailWord_2396036
  simp only [CollatzResearch.WordTrace]
  refine ⟨43695306173789128607503981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58260408231718838143338641 43695306173789128607503981)
  ·
    refine ⟨16385739815170923227813993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43695306173789128607503981 16385739815170923227813993)
    ·
      refine ⟨12289304861378192420860495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16385739815170923227813993 12289304861378192420860495)
      ·
        refine ⟨18433957292067288631290743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12289304861378192420860495 18433957292067288631290743)
        ·
          refine ⟨27650935938100932946936115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18433957292067288631290743 27650935938100932946936115)
          ·
            refine ⟨41476403907151399420404173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27650935938100932946936115 41476403907151399420404173)
            ·
              refine ⟨15553651465181774782651565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41476403907151399420404173 15553651465181774782651565)
              ·
                refine ⟨5832619299443165543494337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15553651465181774782651565 5832619299443165543494337)
                ·
                  refine ⟨4374464474582374157620753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5832619299443165543494337 4374464474582374157620753)
                  ·
                    refine ⟨3280848355936780618215565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4374464474582374157620753 3280848355936780618215565)
                    ·
                      refine ⟨1230318133476292731830837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3280848355936780618215565 1230318133476292731830837)
                      ·
                        rfl

theorem cell23_2396036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_2396036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396036 prefixEnd_2396036 := by exact prefixLift 2396036
  have htrace : WordTrace (prefixWord ++ tailWord_2396036) baseStart_2396036 baseEnd_2396036 := by
    simpa [prefixWord, tailWord_2396036, baseEnd_2396036] using wordTrace_append hprefix tailTrace_2396036
  have hstable : (prefixWord ++ tailWord_2396036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396036).length < 2 ^ (prefixWord ++ tailWord_2396036).sum := by decide
  have hdescent : baseEnd_2396036 < baseStart_2396036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396060 : List Nat := [2, 2, 3, 3, 1, 2, 1, 4, 1, 4]
def baseStart_2396060 : Nat := 118140960795 + 2396060 * 2 ^ 59
def prefixEnd_2396060 : Nat := 4983230072969 + 3 ^ 40 * 2396060 * 2
def baseEnd_2396060 : Nat := 410110152337333545976909

theorem tailTrace_2396060 : CollatzResearch.WordTrace tailWord_2396060 prefixEnd_2396060 410110152337333545976909 := by
  unfold tailWord_2396060
  simp only [CollatzResearch.WordTrace]
  refine ⟨43695743849745654656940817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58260991799660872875921089 43695743849745654656940817)
  ·
    refine ⟨32771807887309240992705613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43695743849745654656940817 32771807887309240992705613)
    ·
      refine ⟨12289427957740965372264605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32771807887309240992705613 12289427957740965372264605)
      ·
        refine ⟨4608535484152862014599227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12289427957740965372264605 4608535484152862014599227)
        ·
          refine ⟨6912803226229293021898841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4608535484152862014599227 6912803226229293021898841)
          ·
            refine ⟨5184602419671969766424131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6912803226229293021898841 5184602419671969766424131)
            ·
              refine ⟨7776903629507954649636197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5184602419671969766424131 7776903629507954649636197)
              ·
                refine ⟨1458169430532741496806787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7776903629507954649636197 1458169430532741496806787)
                ·
                  refine ⟨2187254145799112245210181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1458169430532741496806787 2187254145799112245210181)
                  ·
                    refine ⟨410110152337333545976909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2187254145799112245210181 410110152337333545976909)
                    ·
                      rfl

theorem cell23_2396060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_2396060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396060 prefixEnd_2396060 := by exact prefixLift 2396060
  have htrace : WordTrace (prefixWord ++ tailWord_2396060) baseStart_2396060 baseEnd_2396060 := by
    simpa [prefixWord, tailWord_2396060, baseEnd_2396060] using wordTrace_append hprefix tailTrace_2396060
  have hstable : (prefixWord ++ tailWord_2396060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396060).length < 2 ^ (prefixWord ++ tailWord_2396060).sum := by decide
  have hdescent : baseEnd_2396060 < baseStart_2396060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396093 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 1, 5, 2]
def baseStart_2396093 : Nat := 118140960795 + 2396093 * 2 ^ 59
def prefixEnd_2396093 : Nat := 4983230072969 + 3 ^ 40 * 2396093 * 2
def baseEnd_2396093 : Nat := 1230347401873599008818075

theorem tailTrace_2396093 : CollatzResearch.WordTrace tailWord_2396093 prefixEnd_2396093 1230347401873599008818075 := by
  unfold tailWord_2396093
  simp only [CollatzResearch.WordTrace]
  refine ⟨87392691308371755949832933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58261794205581170633221955 87392691308371755949832933)
  ·
    refine ⟨16386129620319704240593675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87392691308371755949832933 16386129620319704240593675)
    ·
      refine ⟨24579194430479556360890513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16386129620319704240593675 24579194430479556360890513)
      ·
        refine ⟨18434395822859667270667885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24579194430479556360890513 18434395822859667270667885)
        ·
          refine ⟨6912898433572375226500457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18434395822859667270667885 6912898433572375226500457)
          ·
            refine ⟨5184673825179281419875343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6912898433572375226500457 5184673825179281419875343)
            ·
              refine ⟨7777010737768922129813015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5184673825179281419875343 7777010737768922129813015)
              ·
                refine ⟨11665516106653383194719523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7777010737768922129813015 11665516106653383194719523)
                ·
                  refine ⟨17498274159980074792079285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11665516106653383194719523 17498274159980074792079285)
                  ·
                    refine ⟨1640463202498132011757433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17498274159980074792079285 1640463202498132011757433)
                    ·
                      refine ⟨1230347401873599008818075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1640463202498132011757433 1230347401873599008818075)
                      ·
                        rfl

theorem cell23_2396093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_2396093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396093 prefixEnd_2396093 := by exact prefixLift 2396093
  have htrace : WordTrace (prefixWord ++ tailWord_2396093) baseStart_2396093 baseEnd_2396093 := by
    simpa [prefixWord, tailWord_2396093, baseEnd_2396093] using wordTrace_append hprefix tailTrace_2396093
  have hstable : (prefixWord ++ tailWord_2396093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396093).length < 2 ^ (prefixWord ++ tailWord_2396093).sum := by decide
  have hdescent : baseEnd_2396093 < baseStart_2396093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396119 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 6]
def baseStart_2396119 : Nat := 118140960795 + 2396119 * 2 ^ 59
def prefixEnd_2396119 : Nat := 4983230072969 + 3 ^ 40 * 2396119 * 2
def baseEnd_2396119 : Nat := 1230360752370615907092955

theorem tailTrace_2396119 : CollatzResearch.WordTrace tailWord_2396119 prefixEnd_2396119 1230360752370615907092955 := by
  unfold tailWord_2396119
  simp only [CollatzResearch.WordTrace]
  refine ⟨87393639606277562390279411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58262426404185041593519607 87393639606277562390279411)
  ·
    refine ⟨131090459409416343585419117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87393639606277562390279411 131090459409416343585419117)
    ·
      refine ⟨49158922278531128844532169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131090459409416343585419117 49158922278531128844532169)
      ·
        refine ⟨36869191708898346633399127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49158922278531128844532169 36869191708898346633399127)
        ·
          refine ⟨55303787563347519950098691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36869191708898346633399127 55303787563347519950098691)
          ·
            refine ⟨82955681345021279925148037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55303787563347519950098691 82955681345021279925148037)
            ·
              refine ⟨15554190252191489985965257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82955681345021279925148037 15554190252191489985965257)
              ·
                refine ⟨11665642689143617489473943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15554190252191489985965257 11665642689143617489473943)
                ·
                  refine ⟨17498464033715426234210915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11665642689143617489473943 17498464033715426234210915)
                  ·
                    refine ⟨26247696050573139351316373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17498464033715426234210915 26247696050573139351316373)
                    ·
                      refine ⟨1230360752370615907092955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26247696050573139351316373 1230360752370615907092955)
                      ·
                        rfl

theorem cell23_2396119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_2396119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396119 prefixEnd_2396119 := by exact prefixLift 2396119
  have htrace : WordTrace (prefixWord ++ tailWord_2396119) baseStart_2396119 baseEnd_2396119 := by
    simpa [prefixWord, tailWord_2396119, baseEnd_2396119] using wordTrace_append hprefix tailTrace_2396119
  have hstable : (prefixWord ++ tailWord_2396119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396119).length < 2 ^ (prefixWord ++ tailWord_2396119).sum := by decide
  have hdescent : baseEnd_2396119 < baseStart_2396119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396143 : List Nat := [1, 1, 2, 1, 4, 2, 4, 2, 1, 2, 3]
def baseStart_2396143 : Nat := 118140960795 + 2396143 * 2 ^ 59
def prefixEnd_2396143 : Nat := 4983230072969 + 3 ^ 40 * 2396143 * 2
def baseEnd_2396143 : Nat := 1230373075906323813192845

theorem tailTrace_2396143 : CollatzResearch.WordTrace tailWord_2396143 prefixEnd_2396143 1230373075906323813192845 := by
  unfold tailWord_2396143
  simp only [CollatzResearch.WordTrace]
  refine ⟨87394514958190614489153083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58263009972127076326102055 87394514958190614489153083)
  ·
    refine ⟨131091772437285921733729625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87394514958190614489153083 131091772437285921733729625)
    ·
      refine ⟨98318829327964441300297219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131091772437285921733729625 98318829327964441300297219)
      ·
        refine ⟨147478243991946661950445829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98318829327964441300297219 147478243991946661950445829)
        ·
          refine ⟨27652170748489999115708593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147478243991946661950445829 27652170748489999115708593)
          ·
            refine ⟨20739128061367499336781445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27652170748489999115708593 20739128061367499336781445)
            ·
              refine ⟨3888586511506406125646521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20739128061367499336781445 3888586511506406125646521)
              ·
                refine ⟨2916439883629804594234891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3888586511506406125646521 2916439883629804594234891)
                ·
                  refine ⟨4374659825444706891352337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2916439883629804594234891 4374659825444706891352337)
                  ·
                    refine ⟨3280994869083530168514253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4374659825444706891352337 3280994869083530168514253)
                    ·
                      refine ⟨1230373075906323813192845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3280994869083530168514253 1230373075906323813192845)
                      ·
                        rfl

theorem cell23_2396143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 2, 3].length) (baseStart_2396143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396143 prefixEnd_2396143 := by exact prefixLift 2396143
  have htrace : WordTrace (prefixWord ++ tailWord_2396143) baseStart_2396143 baseEnd_2396143 := by
    simpa [prefixWord, tailWord_2396143, baseEnd_2396143] using wordTrace_append hprefix tailTrace_2396143
  have hstable : (prefixWord ++ tailWord_2396143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396143).length < 2 ^ (prefixWord ++ tailWord_2396143).sum := by decide
  have hdescent : baseEnd_2396143 < baseStart_2396143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396156 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 3, 3, 3]
def baseStart_2396156 : Nat := 118140960795 + 2396156 * 2 ^ 59
def prefixEnd_2396156 : Nat := 4983230072969 + 3 ^ 40 * 2396156 * 2
def baseEnd_2396156 : Nat := 1230379751154832262330285

theorem tailTrace_2396156 : CollatzResearch.WordTrace tailWord_2396156 prefixEnd_2396156 1230379751154832262330285 := by
  unfold tailWord_2396156
  simp only [CollatzResearch.WordTrace]
  refine ⟨43697494553571758854688161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58263326071429011806250881 43697494553571758854688161)
  ·
    refine ⟨32773120915178819141016121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43697494553571758854688161 32773120915178819141016121)
    ·
      refine ⟨24579840686384114355762091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32773120915178819141016121 24579840686384114355762091)
      ·
        refine ⟨36869761029576171533643137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24579840686384114355762091 36869761029576171533643137)
        ·
          refine ⟨27652320772182128650232353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36869761029576171533643137 27652320772182128650232353)
          ·
            refine ⟨20739240579136596487674265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27652320772182128650232353 20739240579136596487674265)
            ·
              refine ⟨15554430434352447365755699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20739240579136596487674265 15554430434352447365755699)
              ·
                refine ⟨23331645651528671048633549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15554430434352447365755699 23331645651528671048633549)
                ·
                  refine ⟨8749367119323251643237581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23331645651528671048633549 8749367119323251643237581)
                  ·
                    refine ⟨3281012669746219366214093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8749367119323251643237581 3281012669746219366214093)
                    ·
                      refine ⟨1230379751154832262330285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3281012669746219366214093 1230379751154832262330285)
                      ·
                        rfl

theorem cell23_2396156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_2396156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396156 prefixEnd_2396156 := by exact prefixLift 2396156
  have htrace : WordTrace (prefixWord ++ tailWord_2396156) baseStart_2396156 baseEnd_2396156 := by
    simpa [prefixWord, tailWord_2396156, baseEnd_2396156] using wordTrace_append hprefix tailTrace_2396156
  have hstable : (prefixWord ++ tailWord_2396156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396156).length < 2 ^ (prefixWord ++ tailWord_2396156).sum := by decide
  have hdescent : baseEnd_2396156 < baseStart_2396156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396157 : List Nat := [1, 4, 1, 1, 1, 2, 5, 3, 1, 2, 2]
def baseStart_2396157 : Nat := 118140960795 + 2396157 * 2 ^ 59
def prefixEnd_2396157 : Nat := 4983230072969 + 3 ^ 40 * 2396157 * 2
def baseEnd_2396157 : Nat := 1230380264635486758417781

theorem tailTrace_2396157 : CollatzResearch.WordTrace tailWord_2396157 prefixEnd_2396157 1230380264635486758417781 := by
  unfold tailWord_2396157
  simp only [CollatzResearch.WordTrace]
  refine ⟨87395025580139894880162725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58263350386759929920108483 87395025580139894880162725)
  ·
    refine ⟨16386567296276230290030511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87395025580139894880162725 16386567296276230290030511)
    ·
      refine ⟨24579850944414345435045767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16386567296276230290030511 24579850944414345435045767)
      ·
        refine ⟨36869776416621518152568651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24579850944414345435045767 36869776416621518152568651)
        ·
          refine ⟨55304664624932277228852977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36869776416621518152568651 55304664624932277228852977)
          ·
            refine ⟨41478498468699207921639733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55304664624932277228852977 41478498468699207921639733)
            ·
              refine ⟨3888609231440550742653725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41478498468699207921639733 3888609231440550742653725)
              ·
                refine ⟨1458228461790206528495147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3888609231440550742653725 1458228461790206528495147)
                ·
                  refine ⟨2187342692685309792742721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1458228461790206528495147 2187342692685309792742721)
                  ·
                    refine ⟨1640507019513982344557041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2187342692685309792742721 1640507019513982344557041)
                    ·
                      refine ⟨1230380264635486758417781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1640507019513982344557041 1230380264635486758417781)
                      ·
                        rfl

theorem cell23_2396157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 1, 2, 2].length) (baseStart_2396157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396157 prefixEnd_2396157 := by exact prefixLift 2396157
  have htrace : WordTrace (prefixWord ++ tailWord_2396157) baseStart_2396157 baseEnd_2396157 := by
    simpa [prefixWord, tailWord_2396157, baseEnd_2396157] using wordTrace_append hprefix tailTrace_2396157
  have hstable : (prefixWord ++ tailWord_2396157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396157).length < 2 ^ (prefixWord ++ tailWord_2396157).sum := by decide
  have hdescent : baseEnd_2396157 < baseStart_2396157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396174 : List Nat := [4, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2]
def baseStart_2396174 : Nat := 118140960795 + 2396174 * 2 ^ 59
def prefixEnd_2396174 : Nat := 4983230072969 + 3 ^ 40 * 2396174 * 2
def baseEnd_2396174 : Nat := 1230388993806613191905203

theorem tailTrace_2396174 : CollatzResearch.WordTrace tailWord_2396174 prefixEnd_2396174 1230388993806613191905203 := by
  unfold tailWord_2396174
  simp only [CollatzResearch.WordTrace]
  refine ⟨10924455702634788347941447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58263763747385537855687717 10924455702634788347941447)
  ·
    refine ⟨16386683553952182521912171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10924455702634788347941447 16386683553952182521912171)
    ·
      refine ⟨24580025330928273782868257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16386683553952182521912171 24580025330928273782868257)
      ·
        refine ⟨18435018998196205337151193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24580025330928273782868257 18435018998196205337151193)
        ·
          refine ⟨13826264248647154002863395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18435018998196205337151193 13826264248647154002863395)
          ·
            refine ⟨20739396372970731004295093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13826264248647154002863395 20739396372970731004295093)
            ·
              refine ⟨1944318409966006031652665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20739396372970731004295093 1944318409966006031652665)
              ·
                refine ⟨1458238807474504523739499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1944318409966006031652665 1458238807474504523739499)
                ·
                  refine ⟨2187358211211756785609249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1458238807474504523739499 2187358211211756785609249)
                  ·
                    refine ⟨1640518658408817589206937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2187358211211756785609249 1640518658408817589206937)
                    ·
                      refine ⟨1230388993806613191905203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1640518658408817589206937 1230388993806613191905203)
                      ·
                        rfl

theorem cell23_2396174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_2396174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396174 prefixEnd_2396174 := by exact prefixLift 2396174
  have htrace : WordTrace (prefixWord ++ tailWord_2396174) baseStart_2396174 baseEnd_2396174 := by
    simpa [prefixWord, tailWord_2396174, baseEnd_2396174] using wordTrace_append hprefix tailTrace_2396174
  have hstable : (prefixWord ++ tailWord_2396174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396174).length < 2 ^ (prefixWord ++ tailWord_2396174).sum := by decide
  have hdescent : baseEnd_2396174 < baseStart_2396174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396180 : List Nat := [2, 4, 3, 2, 1, 1, 2, 8]
def baseStart_2396180 : Nat := 118140960795 + 2396180 * 2 ^ 59
def prefixEnd_2396180 : Nat := 4983230072969 + 3 ^ 40 * 2396180 * 2
def baseEnd_2396180 : Nat := 45570076840390376608525

theorem tailTrace_2396180 : CollatzResearch.WordTrace tailWord_2396180 prefixEnd_2396180 45570076840390376608525 := by
  unfold tailWord_2396180
  simp only [CollatzResearch.WordTrace]
  refine ⟨43697932229528284904124997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58263909639371046538833329 43697932229528284904124997)
  ·
    refine ⟨8193362293036553419523437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43697932229528284904124997 8193362293036553419523437)
    ·
      refine ⟨3072510859888707532321289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8193362293036553419523437 3072510859888707532321289)
      ·
        refine ⟨2304383144916530649240967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3072510859888707532321289 2304383144916530649240967)
        ·
          refine ⟨3456574717374795973861451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2304383144916530649240967 3456574717374795973861451)
          ·
            refine ⟨5184862076062193960792177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3456574717374795973861451 5184862076062193960792177)
            ·
              refine ⟨3888646557046645470594133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5184862076062193960792177 3888646557046645470594133)
              ·
                refine ⟨45570076840390376608525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3888646557046645470594133 45570076840390376608525)
                ·
                  rfl

theorem cell23_2396180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 8].length) (baseStart_2396180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396180 prefixEnd_2396180 := by exact prefixLift 2396180
  have htrace : WordTrace (prefixWord ++ tailWord_2396180) baseStart_2396180 baseEnd_2396180 := by
    simpa [prefixWord, tailWord_2396180, baseEnd_2396180] using wordTrace_append hprefix tailTrace_2396180
  have hstable : (prefixWord ++ tailWord_2396180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396180).length < 2 ^ (prefixWord ++ tailWord_2396180).sum := by decide
  have hdescent : baseEnd_2396180 < baseStart_2396180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396213 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 3, 4, 2]
def baseStart_2396213 : Nat := 118140960795 + 2396213 * 2 ^ 59
def prefixEnd_2396213 : Nat := 4983230072969 + 3 ^ 40 * 2396213 * 2
def baseEnd_2396213 : Nat := 1230409019552138539317523

theorem tailTrace_2396213 : CollatzResearch.WordTrace tailWord_2396213 prefixEnd_2396213 1230409019552138539317523 := by
  unfold tailWord_2396213
  simp only [CollatzResearch.WordTrace]
  refine ⟨87397068067937016444201293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58264712045291344296134195 87397068067937016444201293)
  ·
    refine ⟨32773900525476381166575485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87397068067937016444201293 32773900525476381166575485)
    ·
      refine ⟨12290212697053642937465807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32773900525476381166575485 12290212697053642937465807)
      ·
        refine ⟨18435319045580464406198711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12290212697053642937465807 18435319045580464406198711)
        ·
          refine ⟨27652978568370696609298067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18435319045580464406198711 27652978568370696609298067)
          ·
            refine ⟨41479467852556044913947101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27652978568370696609298067 41479467852556044913947101)
            ·
              refine ⟨15554800444708516842730163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41479467852556044913947101 15554800444708516842730163)
              ·
                refine ⟨23332200667062775264095245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15554800444708516842730163 23332200667062775264095245)
                ·
                  refine ⟨8749575250148540724035717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23332200667062775264095245 8749575250148540724035717)
                  ·
                    refine ⟨1640545359402851385756697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8749575250148540724035717 1640545359402851385756697)
                    ·
                      refine ⟨1230409019552138539317523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1640545359402851385756697 1230409019552138539317523)
                      ·
                        rfl

theorem cell23_2396213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_2396213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396213 prefixEnd_2396213 := by exact prefixLift 2396213
  have htrace : WordTrace (prefixWord ++ tailWord_2396213) baseStart_2396213 baseEnd_2396213 := by
    simpa [prefixWord, tailWord_2396213, baseEnd_2396213] using wordTrace_append hprefix tailTrace_2396213
  have hstable : (prefixWord ++ tailWord_2396213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396213).length < 2 ^ (prefixWord ++ tailWord_2396213).sum := by decide
  have hdescent : baseEnd_2396213 < baseStart_2396213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396219 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 9]
def baseStart_2396219 : Nat := 118140960795 + 2396219 * 2 ^ 59
def prefixEnd_2396219 : Nat := 4983230072969 + 3 ^ 40 * 2396219 * 2
def baseEnd_2396219 : Nat := 136712455604007279538055

theorem tailTrace_2396219 : CollatzResearch.WordTrace tailWord_2396219 prefixEnd_2396219 136712455604007279538055 := by
  unfold tailWord_2396219
  simp only [CollatzResearch.WordTrace]
  refine ⟨87397286905915279468919711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58264857937276852979279807 87397286905915279468919711)
  ·
    refine ⟨131095930358872919203379567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87397286905915279468919711 131095930358872919203379567)
    ·
      refine ⟨196643895538309378805069351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131095930358872919203379567 196643895538309378805069351)
      ·
        refine ⟨294965843307464068207604027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196643895538309378805069351 294965843307464068207604027)
        ·
          refine ⟨442448764961196102311406041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294965843307464068207604027 442448764961196102311406041)
          ·
            refine ⟨331836573720897076733554531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 442448764961196102311406041 331836573720897076733554531)
            ·
              refine ⟨497754860581345615100331797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331836573720897076733554531 497754860581345615100331797)
              ·
                refine ⟨23332259089750575707828053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 497754860581345615100331797 23332259089750575707828053)
                ·
                  refine ⟨136712455604007279538055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23332259089750575707828053 136712455604007279538055)
                  ·
                    rfl

theorem cell23_2396219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 9].length) (baseStart_2396219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396219 prefixEnd_2396219 := by exact prefixLift 2396219
  have htrace : WordTrace (prefixWord ++ tailWord_2396219) baseStart_2396219 baseEnd_2396219 := by
    simpa [prefixWord, tailWord_2396219, baseEnd_2396219] using wordTrace_append hprefix tailTrace_2396219
  have hstable : (prefixWord ++ tailWord_2396219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396219).length < 2 ^ (prefixWord ++ tailWord_2396219).sum := by decide
  have hdescent : baseEnd_2396219 < baseStart_2396219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396253 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 9]
def baseStart_2396253 : Nat := 118140960795 + 2396253 * 2 ^ 59
def prefixEnd_2396253 : Nat := 4983230072969 + 3 ^ 40 * 2396253 * 2
def baseEnd_2396253 : Nat := 136714395419813153646371

theorem tailTrace_2396253 : CollatzResearch.WordTrace tailWord_2396253 prefixEnd_2396253 136714395419813153646371 := by
  unfold tailWord_2396253
  simp only [CollatzResearch.WordTrace]
  refine ⟨87398526987792103275657413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58265684658528068850438275 87398526987792103275657413)
  ·
    refine ⟨16387223810211019364185765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87398526987792103275657413 16387223810211019364185765)
    ·
      refine ⟨3072604464414566130784831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16387223810211019364185765 3072604464414566130784831)
      ·
        refine ⟨4608906696621849196177247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3072604464414566130784831 4608906696621849196177247)
        ·
          refine ⟨6913360044932773794265871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4608906696621849196177247 6913360044932773794265871)
          ·
            refine ⟨10370040067399160691398807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6913360044932773794265871 10370040067399160691398807)
            ·
              refine ⟨15555060101098741037098211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10370040067399160691398807 15555060101098741037098211)
              ·
                refine ⟨23332590151648111555647317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15555060101098741037098211 23332590151648111555647317)
                ·
                  refine ⟨136714395419813153646371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23332590151648111555647317 136714395419813153646371)
                  ·
                    rfl

theorem cell23_2396253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_2396253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396253 prefixEnd_2396253 := by exact prefixLift 2396253
  have htrace : WordTrace (prefixWord ++ tailWord_2396253) baseStart_2396253 baseEnd_2396253 := by
    simpa [prefixWord, tailWord_2396253, baseEnd_2396253] using wordTrace_append hprefix tailTrace_2396253
  have hstable : (prefixWord ++ tailWord_2396253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396253).length < 2 ^ (prefixWord ++ tailWord_2396253).sum := by decide
  have hdescent : baseEnd_2396253 < baseStart_2396253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396270 : List Nat := [4, 1, 2, 2, 1, 1, 4, 3, 5]
def baseStart_2396270 : Nat := 118140960795 + 2396270 * 2 ^ 59
def prefixEnd_2396270 : Nat := 4983230072969 + 3 ^ 40 * 2396270 * 2
def baseEnd_2396270 : Nat := 136715365327716090700529

theorem tailTrace_2396270 : CollatzResearch.WordTrace tailWord_2396270 prefixEnd_2396270 136715365327716090700529 := by
  unfold tailWord_2396270
  simp only [CollatzResearch.WordTrace]
  refine ⟨10924893378591314397378283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58266098019153676786017509 10924893378591314397378283)
  ·
    refine ⟨16387340067886971596067425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10924893378591314397378283 16387340067886971596067425)
    ·
      refine ⟨12290505050915228697050569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16387340067886971596067425 12290505050915228697050569)
      ·
        refine ⟨9217878788186421522787927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12290505050915228697050569 9217878788186421522787927)
        ·
          refine ⟨13826818182279632284181891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9217878788186421522787927 13826818182279632284181891)
          ·
            refine ⟨20740227273419448426272837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13826818182279632284181891 20740227273419448426272837)
            ·
              refine ⟨3888792613766146579926157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20740227273419448426272837 3888792613766146579926157)
              ·
                refine ⟨1458297230162304967472309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3888792613766146579926157 1458297230162304967472309)
                ·
                  refine ⟨136715365327716090700529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1458297230162304967472309 136715365327716090700529)
                  ·
                    rfl

theorem cell23_2396270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_2396270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396270 prefixEnd_2396270 := by exact prefixLift 2396270
  have htrace : WordTrace (prefixWord ++ tailWord_2396270) baseStart_2396270 baseEnd_2396270 := by
    simpa [prefixWord, tailWord_2396270, baseEnd_2396270] using wordTrace_append hprefix tailTrace_2396270
  have hstable : (prefixWord ++ tailWord_2396270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396270).length < 2 ^ (prefixWord ++ tailWord_2396270).sum := by decide
  have hdescent : baseEnd_2396270 < baseStart_2396270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396346 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8]
def baseStart_2396346 : Nat := 118140960795 + 2396346 * 2 ^ 59
def prefixEnd_2396346 : Nat := 4983230072969 + 3 ^ 40 * 2396346 * 2
def baseEnd_2396346 : Nat := 1230477312479186518954411

theorem tailTrace_2396346 : CollatzResearch.WordTrace tailWord_2396346 prefixEnd_2396346 1230477312479186518954411 := by
  unfold tailWord_2396346
  simp only [CollatzResearch.WordTrace]
  refine ⟨21850479744113795039698223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58267945984303453439195261 21850479744113795039698223)
  ·
    refine ⟨32775719616170692559547335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21850479744113795039698223 32775719616170692559547335)
    ·
      refine ⟨49163579424256038839321003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32775719616170692559547335 49163579424256038839321003)
      ·
        refine ⟨73745369136384058258981505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49163579424256038839321003 73745369136384058258981505)
        ·
          refine ⟨55309026852288043694236129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73745369136384058258981505 55309026852288043694236129)
          ·
            refine ⟨41481770139216032770677097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55309026852288043694236129 41481770139216032770677097)
            ·
              refine ⟨31111327604412024578007823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41481770139216032770677097 31111327604412024578007823)
              ·
                refine ⟨46666991406618036867011735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31111327604412024578007823 46666991406618036867011735)
                ·
                  refine ⟨70000487109927055300517603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46666991406618036867011735 70000487109927055300517603)
                  ·
                    refine ⟨105000730664890582950776405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70000487109927055300517603 105000730664890582950776405)
                    ·
                      refine ⟨1230477312479186518954411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 105000730664890582950776405 1230477312479186518954411)
                      ·
                        rfl

theorem cell23_2396346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_2396346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396346 prefixEnd_2396346 := by exact prefixLift 2396346
  have htrace : WordTrace (prefixWord ++ tailWord_2396346) baseStart_2396346 baseEnd_2396346 := by
    simpa [prefixWord, tailWord_2396346, baseEnd_2396346] using wordTrace_append hprefix tailTrace_2396346
  have hstable : (prefixWord ++ tailWord_2396346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396346).length < 2 ^ (prefixWord ++ tailWord_2396346).sum := by decide
  have hdescent : baseEnd_2396346 < baseStart_2396346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396347 : List Nat := [1, 1, 1, 1, 1, 2, 9, 2, 1, 4]
def baseStart_2396347 : Nat := 118140960795 + 2396347 * 2 ^ 59
def prefixEnd_2396347 : Nat := 4983230072969 + 3 ^ 40 * 2396347 * 2
def baseEnd_2396347 : Nat := 410159275319947005013969

theorem tailTrace_2396347 : CollatzResearch.WordTrace tailWord_2396347 prefixEnd_2396347 410159275319947005013969 := by
  unfold tailWord_2396347
  simp only [CollatzResearch.WordTrace]
  refine ⟨87401955449451557329579295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58267970299634371553052863 87401955449451557329579295)
  ·
    refine ⟨131102933174177335994368943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87401955449451557329579295 131102933174177335994368943)
    ·
      refine ⟨196654399761266003991553415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131102933174177335994368943 196654399761266003991553415)
      ·
        refine ⟨294981599641899005987330123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196654399761266003991553415 294981599641899005987330123)
        ·
          refine ⟨442472399462848508980995185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294981599641899005987330123 442472399462848508980995185)
          ·
            refine ⟨331854299597136381735746389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 442472399462848508980995185 331854299597136381735746389)
            ·
              refine ⟨1944458786701970986732889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 331854299597136381735746389 1944458786701970986732889)
              ·
                refine ⟨1458344090026478240049667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1944458786701970986732889 1458344090026478240049667)
                ·
                  refine ⟨2187516135039717360074501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1458344090026478240049667 2187516135039717360074501)
                  ·
                    refine ⟨410159275319947005013969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2187516135039717360074501 410159275319947005013969)
                    ·
                      rfl

theorem cell23_2396347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 1, 4].length) (baseStart_2396347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396347 prefixEnd_2396347 := by exact prefixLift 2396347
  have htrace : WordTrace (prefixWord ++ tailWord_2396347) baseStart_2396347 baseEnd_2396347 := by
    simpa [prefixWord, tailWord_2396347, baseEnd_2396347] using wordTrace_append hprefix tailTrace_2396347
  have hstable : (prefixWord ++ tailWord_2396347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396347).length < 2 ^ (prefixWord ++ tailWord_2396347).sum := by decide
  have hdescent : baseEnd_2396347 < baseStart_2396347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396374 : List Nat := [5, 2, 1, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_2396374 : Nat := 118140960795 + 2396374 * 2 ^ 59
def prefixEnd_2396374 : Nat := 4983230072969 + 3 ^ 40 * 2396374 * 2
def baseEnd_2396374 : Nat := 1230491689937512409404283

theorem tailTrace_2396374 : CollatzResearch.WordTrace tailWord_2396374 prefixEnd_2396374 1230491689937512409404283 := by
  unfold tailWord_2396374
  simp only [CollatzResearch.WordTrace]
  refine ⟨5462683763772108808800761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58268626813569160627208117 5462683763772108808800761)
  ·
    refine ⟨4097012822829081606600571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5462683763772108808800761 4097012822829081606600571)
    ·
      refine ⟨6145519234243622409900857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4097012822829081606600571 6145519234243622409900857)
      ·
        refine ⟨4609139425682716807425643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6145519234243622409900857 4609139425682716807425643)
        ·
          refine ⟨6913709138524075211138465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4609139425682716807425643 6913709138524075211138465)
          ·
            refine ⟨5185281853893056408353849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6913709138524075211138465 5185281853893056408353849)
            ·
              refine ⟨3888961390419792306265387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5185281853893056408353849 3888961390419792306265387)
              ·
                refine ⟨5833442085629688459398081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3888961390419792306265387 5833442085629688459398081)
                ·
                  refine ⟨4375081564222266344548561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5833442085629688459398081 4375081564222266344548561)
                  ·
                    refine ⟨3281311173166699758411421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4375081564222266344548561 3281311173166699758411421)
                    ·
                      refine ⟨1230491689937512409404283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3281311173166699758411421 1230491689937512409404283)
                      ·
                        rfl

theorem cell23_2396374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_2396374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396374 prefixEnd_2396374 := by exact prefixLift 2396374
  have htrace : WordTrace (prefixWord ++ tailWord_2396374) baseStart_2396374 baseEnd_2396374 := by
    simpa [prefixWord, tailWord_2396374, baseEnd_2396374] using wordTrace_append hprefix tailTrace_2396374
  have hstable : (prefixWord ++ tailWord_2396374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396374).length < 2 ^ (prefixWord ++ tailWord_2396374).sum := by decide
  have hdescent : baseEnd_2396374 < baseStart_2396374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396413 : List Nat := [1, 4, 1, 1, 1, 1, 1, 6, 1, 1, 5]
def baseStart_2396413 : Nat := 118140960795 + 2396413 * 2 ^ 59
def prefixEnd_2396413 : Nat := 4983230072969 + 3 ^ 40 * 2396413 * 2
def baseEnd_2396413 : Nat := 1230511715683037756816603

theorem tailTrace_2396413 : CollatzResearch.WordTrace tailWord_2396413 prefixEnd_2396413 1230511715683037756816603 := by
  unfold tailWord_2396413
  simp only [CollatzResearch.WordTrace]
  refine ⟨87404362667212450601481893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58269575111474967067654595 87404362667212450601481893)
  ·
    refine ⟨16388318000102334487777855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87404362667212450601481893 16388318000102334487777855)
    ·
      refine ⟨24582477000153501731666783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16388318000102334487777855 24582477000153501731666783)
      ·
        refine ⟨36873715500230252597500175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24582477000153501731666783 36873715500230252597500175)
        ·
          refine ⟨55310573250345378896250263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36873715500230252597500175 55310573250345378896250263)
          ·
            refine ⟨82965859875518068344375395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55310573250345378896250263 82965859875518068344375395)
            ·
              refine ⟨124448789813277102516563093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82965859875518068344375395 124448789813277102516563093)
              ·
                refine ⟨5833537022497364180463895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 124448789813277102516563093 5833537022497364180463895)
                ·
                  refine ⟨8750305533746046270695843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5833537022497364180463895 8750305533746046270695843)
                  ·
                    refine ⟨13125458300619069406043765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8750305533746046270695843 13125458300619069406043765)
                    ·
                      refine ⟨1230511715683037756816603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13125458300619069406043765 1230511715683037756816603)
                      ·
                        rfl

theorem cell23_2396413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_2396413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396413 prefixEnd_2396413 := by exact prefixLift 2396413
  have htrace : WordTrace (prefixWord ++ tailWord_2396413) baseStart_2396413 baseEnd_2396413 := by
    simpa [prefixWord, tailWord_2396413, baseEnd_2396413] using wordTrace_append hprefix tailTrace_2396413
  have hstable : (prefixWord ++ tailWord_2396413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396413).length < 2 ^ (prefixWord ++ tailWord_2396413).sum := by decide
  have hdescent : baseEnd_2396413 < baseStart_2396413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396427 : List Nat := [1, 1, 1, 1, 5, 2, 3, 2, 3, 2, 2]
def baseStart_2396427 : Nat := 118140960795 + 2396427 * 2 ^ 59
def prefixEnd_2396427 : Nat := 4983230072969 + 3 ^ 40 * 2396427 * 2
def baseEnd_2396427 : Nat := 1230518904412200702041539

theorem tailTrace_2396427 : CollatzResearch.WordTrace tailWord_2396427 prefixEnd_2396427 1230518904412200702041539 := by
  unfold tailWord_2396427
  simp only [CollatzResearch.WordTrace]
  refine ⟨87404873289161730992491535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58269915526107820661661023 87404873289161730992491535)
  ·
    refine ⟨131107309933742596488737303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87404873289161730992491535 131107309933742596488737303)
    ·
      refine ⟨196660964900613894733105955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131107309933742596488737303 196660964900613894733105955)
      ·
        refine ⟨294991447350920842099658933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196660964900613894733105955 294991447350920842099658933)
        ·
          refine ⟨27655448189148828946843025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 294991447350920842099658933 27655448189148828946843025)
          ·
            refine ⟨20741586141861621710132269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27655448189148828946843025 20741586141861621710132269)
            ·
              refine ⟨7778094803198108141299601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20741586141861621710132269 7778094803198108141299601)
              ·
                refine ⟨5833571102398581105974701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7778094803198108141299601 5833571102398581105974701)
                ·
                  refine ⟨2187589163399467914740513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5833571102398581105974701 2187589163399467914740513)
                  ·
                    refine ⟨1640691872549600936055385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2187589163399467914740513 1640691872549600936055385)
                    ·
                      refine ⟨1230518904412200702041539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1640691872549600936055385 1230518904412200702041539)
                      ·
                        rfl

theorem cell23_2396427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 2, 2].length) (baseStart_2396427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396427 prefixEnd_2396427 := by exact prefixLift 2396427
  have htrace : WordTrace (prefixWord ++ tailWord_2396427) baseStart_2396427 baseEnd_2396427 := by
    simpa [prefixWord, tailWord_2396427, baseEnd_2396427] using wordTrace_append hprefix tailTrace_2396427
  have hstable : (prefixWord ++ tailWord_2396427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396427).length < 2 ^ (prefixWord ++ tailWord_2396427).sum := by decide
  have hdescent : baseEnd_2396427 < baseStart_2396427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396430 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3]
def baseStart_2396430 : Nat := 118140960795 + 2396430 * 2 ^ 59
def prefixEnd_2396430 : Nat := 4983230072969 + 3 ^ 40 * 2396430 * 2
def baseEnd_2396430 : Nat := 1230520444854164190304025

theorem tailTrace_2396430 : CollatzResearch.WordTrace tailWord_2396430 prefixEnd_2396430 1230520444854164190304025 := by
  unfold tailWord_2396430
  simp only [CollatzResearch.WordTrace]
  refine ⟨10925622838518857813106343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58269988472100575003233829 10925622838518857813106343)
  ·
    refine ⟨16388434257778286719659515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10925622838518857813106343 16388434257778286719659515)
    ·
      refine ⟨24582651386667430079489273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16388434257778286719659515 24582651386667430079489273)
      ·
        refine ⟨18436988540000572559616955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24582651386667430079489273 18436988540000572559616955)
        ·
          refine ⟨27655482810000858839425433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18436988540000572559616955 27655482810000858839425433)
          ·
            refine ⟨20741612107500644129569075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27655482810000858839425433 20741612107500644129569075)
            ·
              refine ⟨31112418161250966194353613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20741612107500644129569075 31112418161250966194353613)
              ·
                refine ⟨11667156810469112322882605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31112418161250966194353613 11667156810469112322882605)
                ·
                  refine ⟨4375183803925917121080977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11667156810469112322882605 4375183803925917121080977)
                  ·
                    refine ⟨3281387852944437840810733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4375183803925917121080977 3281387852944437840810733)
                    ·
                      refine ⟨1230520444854164190304025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3281387852944437840810733 1230520444854164190304025)
                      ·
                        rfl

theorem cell23_2396430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_2396430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396430 prefixEnd_2396430 := by exact prefixLift 2396430
  have htrace : WordTrace (prefixWord ++ tailWord_2396430) baseStart_2396430 baseEnd_2396430 := by
    simpa [prefixWord, tailWord_2396430, baseEnd_2396430] using wordTrace_append hprefix tailTrace_2396430
  have hstable : (prefixWord ++ tailWord_2396430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396430).length < 2 ^ (prefixWord ++ tailWord_2396430).sum := by decide
  have hdescent : baseEnd_2396430 < baseStart_2396430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396447 : List Nat := [1, 1, 2, 4, 3, 2, 1, 3, 1, 2, 3]
def baseStart_2396447 : Nat := 118140960795 + 2396447 * 2 ^ 59
def prefixEnd_2396447 : Nat := 4983230072969 + 3 ^ 40 * 2396447 * 2
def baseEnd_2396447 : Nat := 1230529174025290623791447

theorem tailTrace_2396447 : CollatzResearch.WordTrace tailWord_2396447 prefixEnd_2396447 1230529174025290623791447 := by
  unfold tailWord_2396447
  simp only [CollatzResearch.WordTrace]
  refine ⟨87405602749089274408219595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58270401832726182938813063 87405602749089274408219595)
  ·
    refine ⟨131108404123633911612329393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87405602749089274408219595 131108404123633911612329393)
    ·
      refine ⟨98331303092725433709247045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131108404123633911612329393 98331303092725433709247045)
      ·
        refine ⟨18437119329886018820483821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98331303092725433709247045 18437119329886018820483821)
        ·
          refine ⟨6913919748707257057681433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18437119329886018820483821 6913919748707257057681433)
          ·
            refine ⟨5185439811530442793261075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6913919748707257057681433 5185439811530442793261075)
            ·
              refine ⟨7778159717295664189891613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5185439811530442793261075 7778159717295664189891613)
              ·
                refine ⟨2916809893985874071209355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7778159717295664189891613 2916809893985874071209355)
                ·
                  refine ⟨4375214840978811106814033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2916809893985874071209355 4375214840978811106814033)
                  ·
                    refine ⟨3281411130734108330110525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4375214840978811106814033 3281411130734108330110525)
                    ·
                      refine ⟨1230529174025290623791447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3281411130734108330110525 1230529174025290623791447)
                      ·
                        rfl

theorem cell23_2396447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_2396447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396447 prefixEnd_2396447 := by exact prefixLift 2396447
  have htrace : WordTrace (prefixWord ++ tailWord_2396447) baseStart_2396447 baseEnd_2396447 := by
    simpa [prefixWord, tailWord_2396447, baseEnd_2396447] using wordTrace_append hprefix tailTrace_2396447
  have hstable : (prefixWord ++ tailWord_2396447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396447).length < 2 ^ (prefixWord ++ tailWord_2396447).sum := by decide
  have hdescent : baseEnd_2396447 < baseStart_2396447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396483 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 4]
def baseStart_2396483 : Nat := 118140960795 + 2396483 * 2 ^ 59
def prefixEnd_2396483 : Nat := 4983230072969 + 3 ^ 40 * 2396483 * 2
def baseEnd_2396483 : Nat := 1230547659328852482941281

theorem tailTrace_2396483 : CollatzResearch.WordTrace tailWord_2396483 prefixEnd_2396483 1230547659328852482941281 := by
  unfold tailWord_2396483
  simp only [CollatzResearch.WordTrace]
  refine ⟨87406915776958852556530103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58271277184639235037686735 87406915776958852556530103)
  ·
    refine ⟨131110373665438278834795155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87406915776958852556530103 131110373665438278834795155)
    ·
      refine ⟨196665560498157418252192733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131110373665438278834795155 196665560498157418252192733)
      ·
        refine ⟨73749585186809031844572275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196665560498157418252192733 73749585186809031844572275)
        ·
          refine ⟨110624377780213547766858413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73749585186809031844572275 110624377780213547766858413)
          ·
            refine ⟨41484141667580080412571905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110624377780213547766858413 41484141667580080412571905)
            ·
              refine ⟨31113106250685060309428929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41484141667580080412571905 31113106250685060309428929)
              ·
                refine ⟨23334829688013795232071697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31113106250685060309428929 23334829688013795232071697)
                ·
                  refine ⟨17501122266010346424053773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23334829688013795232071697 17501122266010346424053773)
                  ·
                    refine ⟨6562920849753879909020165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17501122266010346424053773 6562920849753879909020165)
                    ·
                      refine ⟨1230547659328852482941281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6562920849753879909020165 1230547659328852482941281)
                      ·
                        rfl

theorem cell23_2396483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_2396483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396483 prefixEnd_2396483 := by exact prefixLift 2396483
  have htrace : WordTrace (prefixWord ++ tailWord_2396483) baseStart_2396483 baseEnd_2396483 := by
    simpa [prefixWord, tailWord_2396483, baseEnd_2396483] using wordTrace_append hprefix tailTrace_2396483
  have hstable : (prefixWord ++ tailWord_2396483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396483).length < 2 ^ (prefixWord ++ tailWord_2396483).sum := by decide
  have hdescent : baseEnd_2396483 < baseStart_2396483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396484 : List Nat := [2, 3, 4, 1, 2, 2, 2, 7]
def baseStart_2396484 : Nat := 118140960795 + 2396484 * 2 ^ 59
def prefixEnd_2396484 : Nat := 4983230072969 + 3 ^ 40 * 2396484 * 2
def baseEnd_2396484 : Nat := 45575858252203962186251

theorem tailTrace_2396484 : CollatzResearch.WordTrace tailWord_2396484 prefixEnd_2396484 45575858252203962186251 := by
  unfold tailWord_2396484
  simp only [CollatzResearch.WordTrace]
  refine ⟨43703476124977614863658253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58271301499970153151544337 43703476124977614863658253)
  ·
    refine ⟨16388803546866605573871845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43703476124977614863658253 16388803546866605573871845)
    ·
      refine ⟨3072900665037488545100971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16388803546866605573871845 3072900665037488545100971)
      ·
        refine ⟨4609350997556232817651457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3072900665037488545100971 4609350997556232817651457)
        ·
          refine ⟨3457013248167174613238593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4609350997556232817651457 3457013248167174613238593)
          ·
            refine ⟨2592759936125380959928945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3457013248167174613238593 2592759936125380959928945)
            ·
              refine ⟨1944569952094035719946709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2592759936125380959928945 1944569952094035719946709)
              ·
                refine ⟨45575858252203962186251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1944569952094035719946709 45575858252203962186251)
                ·
                  rfl

theorem cell23_2396484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 7].length) (baseStart_2396484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396484 prefixEnd_2396484 := by exact prefixLift 2396484
  have htrace : WordTrace (prefixWord ++ tailWord_2396484) baseStart_2396484 baseEnd_2396484 := by
    simpa [prefixWord, tailWord_2396484, baseEnd_2396484] using wordTrace_append hprefix tailTrace_2396484
  have hstable : (prefixWord ++ tailWord_2396484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396484).length < 2 ^ (prefixWord ++ tailWord_2396484).sum := by decide
  have hdescent : baseEnd_2396484 < baseStart_2396484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396580 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 1, 2, 5]
def baseStart_2396580 : Nat := 118140960795 + 2396580 * 2 ^ 59
def prefixEnd_2396580 : Nat := 4983230072969 + 3 ^ 40 * 2396580 * 2
def baseEnd_2396580 : Nat := 1230597466952338603428335

theorem tailTrace_2396580 : CollatzResearch.WordTrace tailWord_2396580 prefixEnd_2396580 1230597466952338603428335 := by
  unfold tailWord_2396580
  simp only [CollatzResearch.WordTrace]
  refine ⟨43705226828803719061405597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58273635771738292081874129 43705226828803719061405597)
  ·
    refine ⟨16389460060801394648027099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43705226828803719061405597 16389460060801394648027099)
    ·
      refine ⟨24584190091202091972040649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16389460060801394648027099 24584190091202091972040649)
      ·
        refine ⟨18438142568401568979030487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24584190091202091972040649 18438142568401568979030487)
        ·
          refine ⟨27657213852602353468545731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18438142568401568979030487 27657213852602353468545731)
          ·
            refine ⟨41485820778903530202818597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27657213852602353468545731 41485820778903530202818597)
            ·
              refine ⟨7778591396044411913028487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41485820778903530202818597 7778591396044411913028487)
              ·
                refine ⟨11667887094066617869542731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7778591396044411913028487 11667887094066617869542731)
                ·
                  refine ⟨17501830641099926804314097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11667887094066617869542731 17501830641099926804314097)
                  ·
                    refine ⟨13126372980824945103235573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17501830641099926804314097 13126372980824945103235573)
                    ·
                      refine ⟨1230597466952338603428335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13126372980824945103235573 1230597466952338603428335)
                      ·
                        rfl

theorem cell23_2396580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_2396580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396580 prefixEnd_2396580 := by exact prefixLift 2396580
  have htrace : WordTrace (prefixWord ++ tailWord_2396580) baseStart_2396580 baseEnd_2396580 := by
    simpa [prefixWord, tailWord_2396580, baseEnd_2396580] using wordTrace_append hprefix tailTrace_2396580
  have hstable : (prefixWord ++ tailWord_2396580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396580).length < 2 ^ (prefixWord ++ tailWord_2396580).sum := by decide
  have hdescent : baseEnd_2396580 < baseStart_2396580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396584 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_2396584 : Nat := 118140960795 + 2396584 * 2 ^ 59
def prefixEnd_2396584 : Nat := 4983230072969 + 3 ^ 40 * 2396584 * 2
def baseEnd_2396584 : Nat := 1230599520874956587778317

theorem tailTrace_2396584 : CollatzResearch.WordTrace tailWord_2396584 prefixEnd_2396584 1230599520874956587778317 := by
  unfold tailWord_2396584
  simp only [CollatzResearch.WordTrace]
  refine ⟨43705299774796473402978403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58273733033061964537304537 43705299774796473402978403)
  ·
    refine ⟨65557949662194710104467605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43705299774796473402978403 65557949662194710104467605)
    ·
      refine ⟨3073028890415377036146919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65557949662194710104467605 3073028890415377036146919)
      ·
        refine ⟨4609543335623065554220379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3073028890415377036146919 4609543335623065554220379)
        ·
          refine ⟨6914315003434598331330569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4609543335623065554220379 6914315003434598331330569)
          ·
            refine ⟨5185736252575948748497927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6914315003434598331330569 5185736252575948748497927)
            ·
              refine ⟨7778604378863923122746891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5185736252575948748497927 7778604378863923122746891)
              ·
                refine ⟨11667906568295884684120337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7778604378863923122746891 11667906568295884684120337)
                ·
                  refine ⟨8750929926221913513090253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11667906568295884684120337 8750929926221913513090253)
                  ·
                    refine ⟨3281598722333217567408845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8750929926221913513090253 3281598722333217567408845)
                    ·
                      refine ⟨1230599520874956587778317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3281598722333217567408845 1230599520874956587778317)
                      ·
                        rfl

theorem cell23_2396584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_2396584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396584 prefixEnd_2396584 := by exact prefixLift 2396584
  have htrace : WordTrace (prefixWord ++ tailWord_2396584) baseStart_2396584 baseEnd_2396584 := by
    simpa [prefixWord, tailWord_2396584, baseEnd_2396584] using wordTrace_append hprefix tailTrace_2396584
  have hstable : (prefixWord ++ tailWord_2396584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396584).length < 2 ^ (prefixWord ++ tailWord_2396584).sum := by decide
  have hdescent : baseEnd_2396584 < baseStart_2396584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396604 : List Nat := [2, 2, 2, 4, 1, 3, 1, 1, 2, 5]
def baseStart_2396604 : Nat := 118140960795 + 2396604 * 2 ^ 59
def prefixEnd_2396604 : Nat := 4983230072969 + 3 ^ 40 * 2396604 * 2
def baseEnd_2396604 : Nat := 410203263496015503176075

theorem tailTrace_2396604 : CollatzResearch.WordTrace tailWord_2396604 prefixEnd_2396604 410203263496015503176075 := by
  unfold tailWord_2396604
  simp only [CollatzResearch.WordTrace]
  refine ⟨43705664504760245110842433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58274219339680326814456577 43705664504760245110842433)
  ·
    refine ⟨32779248378570183833131825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43705664504760245110842433 32779248378570183833131825)
    ·
      refine ⟨24584436283927637874848869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32779248378570183833131825 24584436283927637874848869)
      ·
        refine ⟨4609581803236432101534163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24584436283927637874848869 4609581803236432101534163)
        ·
          refine ⟨6914372704854648152301245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4609581803236432101534163 6914372704854648152301245)
          ·
            refine ⟨2592889764320493057112967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6914372704854648152301245 2592889764320493057112967)
            ·
              refine ⟨3889334646480739585669451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2592889764320493057112967 3889334646480739585669451)
              ·
                refine ⟨5834001969721109378504177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3889334646480739585669451 5834001969721109378504177)
                ·
                  refine ⟨4375501477290832033878133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5834001969721109378504177 4375501477290832033878133)
                  ·
                    refine ⟨410203263496015503176075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4375501477290832033878133 410203263496015503176075)
                    ·
                      rfl

theorem cell23_2396604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_2396604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396604 prefixEnd_2396604 := by exact prefixLift 2396604
  have htrace : WordTrace (prefixWord ++ tailWord_2396604) baseStart_2396604 baseEnd_2396604 := by
    simpa [prefixWord, tailWord_2396604, baseEnd_2396604] using wordTrace_append hprefix tailTrace_2396604
  have hstable : (prefixWord ++ tailWord_2396604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396604).length < 2 ^ (prefixWord ++ tailWord_2396604).sum := by decide
  have hdescent : baseEnd_2396604 < baseStart_2396604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396634 : List Nat := [3, 1, 1, 2, 3, 1, 1, 6, 1, 4]
def baseStart_2396634 : Nat := 118140960795 + 2396634 * 2 ^ 59
def prefixEnd_2396634 : Nat := 4983230072969 + 3 ^ 40 * 2396634 * 2
def baseEnd_2396634 : Nat := 410208398302560464051029

theorem tailTrace_2396634 : CollatzResearch.WordTrace tailWord_2396634 prefixEnd_2396634 410208398302560464051029 := by
  unfold tailWord_2396634
  simp only [CollatzResearch.WordTrace]
  refine ⟨21853105799852951336319239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58274948799607870230184637 21853105799852951336319239)
  ·
    refine ⟨32779658699779427004478859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21853105799852951336319239 32779658699779427004478859)
    ·
      refine ⟨49169488049669140506718289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32779658699779427004478859 49169488049669140506718289)
      ·
        refine ⟨36877116037251855380038717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49169488049669140506718289 36877116037251855380038717)
        ·
          refine ⟨13828918513969445767514519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36877116037251855380038717 13828918513969445767514519)
          ·
            refine ⟨20743377770954168651271779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13828918513969445767514519 20743377770954168651271779)
            ·
              refine ⟨31115066656431252976907669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20743377770954168651271779 31115066656431252976907669)
              ·
                refine ⟨1458518749520214983292547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31115066656431252976907669 1458518749520214983292547)
                ·
                  refine ⟨2187778124280322474938821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1458518749520214983292547 2187778124280322474938821)
                  ·
                    refine ⟨410208398302560464051029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2187778124280322474938821 410208398302560464051029)
                    ·
                      rfl

theorem cell23_2396634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 1, 4].length) (baseStart_2396634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396634 prefixEnd_2396634 := by exact prefixLift 2396634
  have htrace : WordTrace (prefixWord ++ tailWord_2396634) baseStart_2396634 baseEnd_2396634 := by
    simpa [prefixWord, tailWord_2396634, baseEnd_2396634] using wordTrace_append hprefix tailTrace_2396634
  have hstable : (prefixWord ++ tailWord_2396634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396634).length < 2 ^ (prefixWord ++ tailWord_2396634).sum := by decide
  have hdescent : baseEnd_2396634 < baseStart_2396634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396677 : List Nat := [1, 3, 1, 1, 2, 2, 4, 3, 1, 5]
def baseStart_2396677 : Nat := 118140960795 + 2396677 * 2 ^ 59
def prefixEnd_2396677 : Nat := 4983230072969 + 3 ^ 40 * 2396677 * 2
def baseEnd_2396677 : Nat := 410215758191941574638463

theorem tailTrace_2396677 : CollatzResearch.WordTrace tailWord_2396677 prefixEnd_2396677 410215758191941574638463 := by
  unfold tailWord_2396677
  simp only [CollatzResearch.WordTrace]
  refine ⟨87413991538256023689092285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58275994358837349126061523 87413991538256023689092285)
  ·
    refine ⟨32780246826846008883409607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87413991538256023689092285 32780246826846008883409607)
    ·
      refine ⟨49170370240269013325114411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32780246826846008883409607 49170370240269013325114411)
      ·
        refine ⟨73755555360403519987671617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49170370240269013325114411 73755555360403519987671617)
        ·
          refine ⟨55316666520302639990753713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73755555360403519987671617 55316666520302639990753713)
          ·
            refine ⟨41487499890226979993065285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55316666520302639990753713 41487499890226979993065285)
            ·
              refine ⟨7778906229417558748699741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41487499890226979993065285 7778906229417558748699741)
              ·
                refine ⟨2917089836031584530762403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7778906229417558748699741 2917089836031584530762403)
                ·
                  refine ⟨4375634754047376796143605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2917089836031584530762403 4375634754047376796143605)
                  ·
                    refine ⟨410215758191941574638463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4375634754047376796143605 410215758191941574638463)
                    ·
                      rfl

theorem cell23_2396677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 5].length) (baseStart_2396677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396677 prefixEnd_2396677 := by exact prefixLift 2396677
  have htrace : WordTrace (prefixWord ++ tailWord_2396677) baseStart_2396677 baseEnd_2396677 := by
    simpa [prefixWord, tailWord_2396677, baseEnd_2396677] using wordTrace_append hprefix tailTrace_2396677
  have hstable : (prefixWord ++ tailWord_2396677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396677).length < 2 ^ (prefixWord ++ tailWord_2396677).sum := by decide
  have hdescent : baseEnd_2396677 < baseStart_2396677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396678 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_2396678 : Nat := 118140960795 + 2396678 * 2 ^ 59
def prefixEnd_2396678 : Nat := 4983230072969 + 3 ^ 40 * 2396678 * 2
def baseEnd_2396678 : Nat := 1230647788056479220002885

theorem tailTrace_2396678 : CollatzResearch.WordTrace tailWord_2396678 prefixEnd_2396678 1230647788056479220002885 := by
  unfold tailWord_2396678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2731688375351637526871209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58276018674168267239919125 2731688375351637526871209)
  ·
    refine ⟨2048766281513728145153407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2731688375351637526871209 2048766281513728145153407)
    ·
      refine ⟨3073149422270592217730111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2048766281513728145153407 3073149422270592217730111)
      ·
        refine ⟨4609724133405888326595167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3073149422270592217730111 4609724133405888326595167)
        ·
          refine ⟨6914586200108832489892751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4609724133405888326595167 6914586200108832489892751)
          ·
            refine ⟨10371879300163248734839127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6914586200108832489892751 10371879300163248734839127)
            ·
              refine ⟨15557818950244873102258691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10371879300163248734839127 15557818950244873102258691)
              ·
                refine ⟨23336728425367309653388037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15557818950244873102258691 23336728425367309653388037)
                ·
                  refine ⟨4375636579756370560010257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23336728425367309653388037 4375636579756370560010257)
                  ·
                    refine ⟨3281727434817277920007693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4375636579756370560010257 3281727434817277920007693)
                    ·
                      refine ⟨1230647788056479220002885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3281727434817277920007693 1230647788056479220002885)
                      ·
                        rfl

theorem cell23_2396678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_2396678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396678 prefixEnd_2396678 := by exact prefixLift 2396678
  have htrace : WordTrace (prefixWord ++ tailWord_2396678) baseStart_2396678 baseEnd_2396678 := by
    simpa [prefixWord, tailWord_2396678, baseEnd_2396678] using wordTrace_append hprefix tailTrace_2396678
  have hstable : (prefixWord ++ tailWord_2396678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396678).length < 2 ^ (prefixWord ++ tailWord_2396678).sum := by decide
  have hdescent : baseEnd_2396678 < baseStart_2396678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396684 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 4, 3, 2]
def baseStart_2396684 : Nat := 118140960795 + 2396684 * 2 ^ 59
def prefixEnd_2396684 : Nat := 4983230072969 + 3 ^ 40 * 2396684 * 2
def baseEnd_2396684 : Nat := 1230650868940406196527857

theorem tailTrace_2396684 : CollatzResearch.WordTrace tailWord_2396684 prefixEnd_2396684 1230650868940406196527857 := by
  unfold tailWord_2396684
  simp only [CollatzResearch.WordTrace]
  refine ⟨43707123424615331942298553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58276164566153775923064737 43707123424615331942298553)
  ·
    refine ⟨32780342568461498956723915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43707123424615331942298553 32780342568461498956723915)
    ·
      refine ⟨49170513852692248435085873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32780342568461498956723915 49170513852692248435085873)
      ·
        refine ⟨36877885389519186326314405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49170513852692248435085873 36877885389519186326314405)
        ·
          refine ⟨6914603510534847436183951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36877885389519186326314405 6914603510534847436183951)
          ·
            refine ⟨10371905265802271154275927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6914603510534847436183951 10371905265802271154275927)
            ·
              refine ⟨15557857898703406731413891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10371905265802271154275927 15557857898703406731413891)
              ·
                refine ⟨23336786848055110097120837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15557857898703406731413891 23336786848055110097120837)
                ·
                  refine ⟨4375647534010333143210157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23336786848055110097120837 4375647534010333143210157)
                  ·
                    refine ⟨1640867825253874928703809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4375647534010333143210157 1640867825253874928703809)
                    ·
                      refine ⟨1230650868940406196527857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1640867825253874928703809 1230650868940406196527857)
                      ·
                        rfl

theorem cell23_2396684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 4, 3, 2].length) (baseStart_2396684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396684 prefixEnd_2396684 := by exact prefixLift 2396684
  have htrace : WordTrace (prefixWord ++ tailWord_2396684) baseStart_2396684 baseEnd_2396684 := by
    simpa [prefixWord, tailWord_2396684, baseEnd_2396684] using wordTrace_append hprefix tailTrace_2396684
  have hstable : (prefixWord ++ tailWord_2396684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396684).length < 2 ^ (prefixWord ++ tailWord_2396684).sum := by decide
  have hdescent : baseEnd_2396684 < baseStart_2396684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396711 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 3, 5]
def baseStart_2396711 : Nat := 118140960795 + 2396711 * 2 ^ 59
def prefixEnd_2396711 : Nat := 4983230072969 + 3 ^ 40 * 2396711 * 2
def baseEnd_2396711 : Nat := 410221577639359196963411

theorem tailTrace_2396711 : CollatzResearch.WordTrace tailWord_2396711 prefixEnd_2396711 410221577639359196963411 := by
  unfold tailWord_2396711
  simp only [CollatzResearch.WordTrace]
  refine ⟨87415231620132847495829987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58276821080088564997219991 87415231620132847495829987)
  ·
    refine ⟨131122847430199271243744981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87415231620132847495829987 131122847430199271243744981)
    ·
      refine ⟨3073191736645295419775273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 131122847430199271243744981 3073191736645295419775273)
      ·
        refine ⟨2304893802483971564831455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3073191736645295419775273 2304893802483971564831455)
        ·
          refine ⟨3457340703725957347247183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2304893802483971564831455 3457340703725957347247183)
          ·
            refine ⟨5186011055588936020870775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3457340703725957347247183 5186011055588936020870775)
            ·
              refine ⟨7779016583383404031306163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5186011055588936020870775 7779016583383404031306163)
              ·
                refine ⟨11668524875075106046959245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7779016583383404031306163 11668524875075106046959245)
                ·
                  refine ⟨4375696828153164767609717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11668524875075106046959245 4375696828153164767609717)
                  ·
                    refine ⟨410221577639359196963411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4375696828153164767609717 410221577639359196963411)
                    ·
                      rfl

theorem cell23_2396711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_2396711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396711 prefixEnd_2396711 := by exact prefixLift 2396711
  have htrace : WordTrace (prefixWord ++ tailWord_2396711) baseStart_2396711 baseEnd_2396711 := by
    simpa [prefixWord, tailWord_2396711, baseEnd_2396711] using wordTrace_append hprefix tailTrace_2396711
  have hstable : (prefixWord ++ tailWord_2396711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396711).length < 2 ^ (prefixWord ++ tailWord_2396711).sum := by decide
  have hdescent : baseEnd_2396711 < baseStart_2396711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396714 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_2396714 : Nat := 118140960795 + 2396714 * 2 ^ 59
def prefixEnd_2396714 : Nat := 4983230072969 + 3 ^ 40 * 2396714 * 2
def baseEnd_2396714 : Nat := 1230666273360041079152719

theorem tailTrace_2396714 : CollatzResearch.WordTrace tailWord_2396714 prefixEnd_2396714 1230666273360041079152719 := by
  unfold tailWord_2396714
  simp only [CollatzResearch.WordTrace]
  refine ⟨21853835259780494752047299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58276894026081319338792797 21853835259780494752047299)
  ·
    refine ⟨32780752889670742128070949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21853835259780494752047299 32780752889670742128070949)
    ·
      refine ⟨6146391166813264149013303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32780752889670742128070949 6146391166813264149013303)
      ·
        refine ⟨9219586750219896223519955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6146391166813264149013303 9219586750219896223519955)
        ·
          refine ⟨13829380125329844335279933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9219586750219896223519955 13829380125329844335279933)
          ·
            refine ⟨5186017546998691625729975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13829380125329844335279933 5186017546998691625729975)
            ·
              refine ⟨7779026320498037438594963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5186017546998691625729975 7779026320498037438594963)
              ·
                refine ⟨11668539480747056157892445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7779026320498037438594963 11668539480747056157892445)
                ·
                  refine ⟨4375702305280146059209667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11668539480747056157892445 4375702305280146059209667)
                  ·
                    refine ⟨6563553457920219088814501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4375702305280146059209667 6563553457920219088814501)
                    ·
                      refine ⟨1230666273360041079152719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6563553457920219088814501 1230666273360041079152719)
                      ·
                        rfl

theorem cell23_2396714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_2396714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396714 prefixEnd_2396714 := by exact prefixLift 2396714
  have htrace : WordTrace (prefixWord ++ tailWord_2396714) baseStart_2396714 baseEnd_2396714 := by
    simpa [prefixWord, tailWord_2396714, baseEnd_2396714] using wordTrace_append hprefix tailTrace_2396714
  have hstable : (prefixWord ++ tailWord_2396714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396714).length < 2 ^ (prefixWord ++ tailWord_2396714).sum := by decide
  have hdescent : baseEnd_2396714 < baseStart_2396714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396718 : List Nat := [4, 1, 3, 1, 3, 1, 2, 1, 2, 3, 2]
def baseStart_2396718 : Nat := 118140960795 + 2396718 * 2 ^ 59
def prefixEnd_2396718 : Nat := 4983230072969 + 3 ^ 40 * 2396718 * 2
def baseEnd_2396718 : Nat := 1230668327282659063502701

theorem tailTrace_2396718 : CollatzResearch.WordTrace tailWord_2396718 prefixEnd_2396718 1230668327282659063502701 := by
  unfold tailWord_2396718
  simp only [CollatzResearch.WordTrace]
  refine ⟨10926935866388435961416851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58276991287404991794223205 10926935866388435961416851)
  ·
    refine ⟨16390403799582653942125277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10926935866388435961416851 16390403799582653942125277)
    ·
      refine ⟨6146401424843495228296979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16390403799582653942125277 6146401424843495228296979)
      ·
        refine ⟨9219602137265242842445469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6146401424843495228296979 9219602137265242842445469)
        ·
          refine ⟨3457350801474466065917051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9219602137265242842445469 3457350801474466065917051)
          ·
            refine ⟨5186026202211699098875577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3457350801474466065917051 5186026202211699098875577)
            ·
              refine ⟨3889519651658774324156683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5186026202211699098875577 3889519651658774324156683)
              ·
                refine ⟨5834279477488161486235025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3889519651658774324156683 5834279477488161486235025)
                ·
                  refine ⟨4375709608116121114676269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5834279477488161486235025 4375709608116121114676269)
                  ·
                    refine ⟨1640891103043545418003601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4375709608116121114676269 1640891103043545418003601)
                    ·
                      refine ⟨1230668327282659063502701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1640891103043545418003601 1230668327282659063502701)
                      ·
                        rfl

theorem cell23_2396718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_2396718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396718 prefixEnd_2396718 := by exact prefixLift 2396718
  have htrace : WordTrace (prefixWord ++ tailWord_2396718) baseStart_2396718 baseEnd_2396718 := by
    simpa [prefixWord, tailWord_2396718, baseEnd_2396718] using wordTrace_append hprefix tailTrace_2396718
  have hstable : (prefixWord ++ tailWord_2396718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396718).length < 2 ^ (prefixWord ++ tailWord_2396718).sum := by decide
  have hdescent : baseEnd_2396718 < baseStart_2396718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396720 : List Nat := [2, 1, 1, 1, 2, 3, 4, 9]
def baseStart_2396720 : Nat := 118140960795 + 2396720 * 2 ^ 59
def prefixEnd_2396720 : Nat := 4983230072969 + 3 ^ 40 * 2396720 * 2
def baseEnd_2396720 : Nat := 45580346453480298358433

theorem tailTrace_2396720 : CollatzResearch.WordTrace tailWord_2396720 prefixEnd_2396720 45580346453480298358433 := by
  unfold tailWord_2396720
  simp only [CollatzResearch.WordTrace]
  refine ⟨43707779938550121016453807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58277039918066828021938409 43707779938550121016453807)
  ·
    refine ⟨65561669907825181524680711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43707779938550121016453807 65561669907825181524680711)
    ·
      refine ⟨98342504861737772287021067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65561669907825181524680711 98342504861737772287021067)
      ·
        refine ⟨147513757292606658430531601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98342504861737772287021067 147513757292606658430531601)
        ·
          refine ⟨110635317969454993822898701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147513757292606658430531601 110635317969454993822898701)
          ·
            refine ⟨41488244238545622683587013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110635317969454993822898701 41488244238545622683587013)
            ·
              refine ⟨7779045794727304253172565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41488244238545622683587013 7779045794727304253172565)
              ·
                refine ⟨45580346453480298358433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7779045794727304253172565 45580346453480298358433)
                ·
                  rfl

theorem cell23_2396720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 9].length) (baseStart_2396720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396720 prefixEnd_2396720 := by exact prefixLift 2396720
  have htrace : WordTrace (prefixWord ++ tailWord_2396720) baseStart_2396720 baseEnd_2396720 := by
    simpa [prefixWord, tailWord_2396720, baseEnd_2396720] using wordTrace_append hprefix tailTrace_2396720
  have hstable : (prefixWord ++ tailWord_2396720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396720).length < 2 ^ (prefixWord ++ tailWord_2396720).sum := by decide
  have hdescent : baseEnd_2396720 < baseStart_2396720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396727 : List Nat := [1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 4]
def baseStart_2396727 : Nat := 118140960795 + 2396727 * 2 ^ 59
def prefixEnd_2396727 : Nat := 4983230072969 + 3 ^ 40 * 2396727 * 2
def baseEnd_2396727 : Nat := 1230672948608549528290159

theorem tailTrace_2396727 : CollatzResearch.WordTrace tailWord_2396727 prefixEnd_2396727 1230672948608549528290159 := by
  unfold tailWord_2396727
  simp only [CollatzResearch.WordTrace]
  refine ⟨87415815188074882228412435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58277210125383254818941623 87415815188074882228412435)
  ·
    refine ⟨131123722782112323342618653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87415815188074882228412435 131123722782112323342618653)
    ·
      refine ⟨49171396043292121253481995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131123722782112323342618653 49171396043292121253481995)
      ·
        refine ⟨73757094064938181880222993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49171396043292121253481995 73757094064938181880222993)
        ·
          refine ⟨55317820548703636410167245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73757094064938181880222993 55317820548703636410167245)
          ·
            refine ⟨20744182705763863653812717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55317820548703636410167245 20744182705763863653812717)
            ·
              refine ⟨7779068514661448870179769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20744182705763863653812717 7779068514661448870179769)
              ·
                refine ⟨5834301385996086652634827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7779068514661448870179769 5834301385996086652634827)
                ·
                  refine ⟨8751452078994129978952241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5834301385996086652634827 8751452078994129978952241)
                  ·
                    refine ⟨6563589059245597484214181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8751452078994129978952241 6563589059245597484214181)
                    ·
                      refine ⟨1230672948608549528290159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6563589059245597484214181 1230672948608549528290159)
                      ·
                        rfl

theorem cell23_2396727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_2396727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396727 prefixEnd_2396727 := by exact prefixLift 2396727
  have htrace : WordTrace (prefixWord ++ tailWord_2396727) baseStart_2396727 baseEnd_2396727 := by
    simpa [prefixWord, tailWord_2396727, baseEnd_2396727] using wordTrace_append hprefix tailTrace_2396727
  have hstable : (prefixWord ++ tailWord_2396727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396727).length < 2 ^ (prefixWord ++ tailWord_2396727).sum := by decide
  have hdescent : baseEnd_2396727 < baseStart_2396727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396742 : List Nat := [6, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3]
def baseStart_2396742 : Nat := 118140960795 + 2396742 * 2 ^ 59
def prefixEnd_2396742 : Nat := 4983230072969 + 3 ^ 40 * 2396742 * 2
def baseEnd_2396742 : Nat := 1230680650818366969602591

theorem tailTrace_2396742 : CollatzResearch.WordTrace tailWord_2396742 prefixEnd_2396742 1230680650818366969602591 := by
  unfold tailWord_2396742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2731761321344391868444015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58277574855347026526805653 2731761321344391868444015)
  ·
    refine ⟨4097641982016587802666023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2731761321344391868444015 4097641982016587802666023)
    ·
      refine ⟨6146462973024881703999035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4097641982016587802666023 6146462973024881703999035)
      ·
        refine ⟨9219694459537322555998553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6146462973024881703999035 9219694459537322555998553)
        ·
          refine ⟨6914770844652991916998915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9219694459537322555998553 6914770844652991916998915)
          ·
            refine ⟨10372156266979487875498373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6914770844652991916998915 10372156266979487875498373)
            ·
              refine ⟨1944779300058653976655945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10372156266979487875498373 1944779300058653976655945)
              ·
                refine ⟨1458584475043990482491959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1944779300058653976655945 1458584475043990482491959)
                ·
                  refine ⟨2187876712565985723737939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1458584475043990482491959 2187876712565985723737939)
                  ·
                    refine ⟨3281815068848978585606909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2187876712565985723737939 3281815068848978585606909)
                    ·
                      refine ⟨1230680650818366969602591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3281815068848978585606909 1230680650818366969602591)
                      ·
                        rfl

theorem cell23_2396742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_2396742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396742 prefixEnd_2396742 := by exact prefixLift 2396742
  have htrace : WordTrace (prefixWord ++ tailWord_2396742) baseStart_2396742 baseEnd_2396742 := by
    simpa [prefixWord, tailWord_2396742, baseEnd_2396742] using wordTrace_append hprefix tailTrace_2396742
  have hstable : (prefixWord ++ tailWord_2396742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396742).length < 2 ^ (prefixWord ++ tailWord_2396742).sum := by decide
  have hdescent : baseEnd_2396742 < baseStart_2396742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396748 : List Nat := [2, 2, 1, 3, 1, 2, 3, 4, 1, 2, 2]
def baseStart_2396748 : Nat := 118140960795 + 2396748 * 2 ^ 59
def prefixEnd_2396748 : Nat := 4983230072969 + 3 ^ 40 * 2396748 * 2
def baseEnd_2396748 : Nat := 1230683731702293946127563

theorem tailTrace_2396748 : CollatzResearch.WordTrace tailWord_2396748 prefixEnd_2396748 1230683731702293946127563 := by
  unfold tailWord_2396748
  simp only [CollatzResearch.WordTrace]
  refine ⟨43708290560499401407463449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58277720747332535209951265 43708290560499401407463449)
  ·
    refine ⟨32781217920374551055597587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43708290560499401407463449 32781217920374551055597587)
    ·
      refine ⟨49171826880561826583396381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32781217920374551055597587 49171826880561826583396381)
      ·
        refine ⟨18439435080210684968773643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49171826880561826583396381 18439435080210684968773643)
        ·
          refine ⟨27659152620316027453160465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18439435080210684968773643 27659152620316027453160465)
          ·
            refine ⟨20744364465237020589870349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27659152620316027453160465 20744364465237020589870349)
            ·
              refine ⟨7779136674463882721201381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20744364465237020589870349 7779136674463882721201381)
              ·
                refine ⟨1458588126461978010225259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7779136674463882721201381 1458588126461978010225259)
                ·
                  refine ⟨2187882189692967015337889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1458588126461978010225259 2187882189692967015337889)
                  ·
                    refine ⟨1640911642269725261503417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2187882189692967015337889 1640911642269725261503417)
                    ·
                      refine ⟨1230683731702293946127563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1640911642269725261503417 1230683731702293946127563)
                      ·
                        rfl

theorem cell23_2396748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_2396748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396748 prefixEnd_2396748 := by exact prefixLift 2396748
  have htrace : WordTrace (prefixWord ++ tailWord_2396748) baseStart_2396748 baseEnd_2396748 := by
    simpa [prefixWord, tailWord_2396748, baseEnd_2396748] using wordTrace_append hprefix tailTrace_2396748
  have hstable : (prefixWord ++ tailWord_2396748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396748).length < 2 ^ (prefixWord ++ tailWord_2396748).sum := by decide
  have hdescent : baseEnd_2396748 < baseStart_2396748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396907 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 6]
def baseStart_2396907 : Nat := 118140960795 + 2396907 * 2 ^ 59
def prefixEnd_2396907 : Nat := 4983230072969 + 3 ^ 40 * 2396907 * 2
def baseEnd_2396907 : Nat := 1230765375126358824039331

theorem tailTrace_2396907 : CollatzResearch.WordTrace tailWord_2396907 prefixEnd_2396907 1230765375126358824039331 := by
  unfold tailWord_2396907
  simp only [CollatzResearch.WordTrace]
  refine ⟨87422380327422772969964975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58281586884948515313309983 87422380327422772969964975)
  ·
    refine ⟨131133570491134159454947463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87422380327422772969964975 131133570491134159454947463)
    ·
      refine ⟨196700355736701239182421195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131133570491134159454947463 196700355736701239182421195)
      ·
        refine ⟨295050533605051858773631793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196700355736701239182421195 295050533605051858773631793)
        ·
          refine ⟨221287900203788894080223845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295050533605051858773631793 221287900203788894080223845)
          ·
            refine ⟨41491481288210417640041971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 221287900203788894080223845 41491481288210417640041971)
            ·
              refine ⟨62237221932315626460062957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41491481288210417640041971 62237221932315626460062957)
              ·
                refine ⟨23338958224618359922523609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62237221932315626460062957 23338958224618359922523609)
                ·
                  refine ⟨17504218668463769941892707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23338958224618359922523609 17504218668463769941892707)
                  ·
                    refine ⟨26256328002695654912839061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17504218668463769941892707 26256328002695654912839061)
                    ·
                      refine ⟨1230765375126358824039331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26256328002695654912839061 1230765375126358824039331)
                      ·
                        rfl

theorem cell23_2396907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 6].length) (baseStart_2396907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396907 prefixEnd_2396907 := by exact prefixLift 2396907
  have htrace : WordTrace (prefixWord ++ tailWord_2396907) baseStart_2396907 baseEnd_2396907 := by
    simpa [prefixWord, tailWord_2396907, baseEnd_2396907] using wordTrace_append hprefix tailTrace_2396907
  have hstable : (prefixWord ++ tailWord_2396907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396907).length < 2 ^ (prefixWord ++ tailWord_2396907).sum := by decide
  have hdescent : baseEnd_2396907 < baseStart_2396907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396961 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 5, 1, 3]
def baseStart_2396961 : Nat := 118140960795 + 2396961 * 2 ^ 59
def prefixEnd_2396961 : Nat := 4983230072969 + 3 ^ 40 * 2396961 * 2
def baseEnd_2396961 : Nat := 1230793103081701612764083

theorem tailTrace_2396961 : CollatzResearch.WordTrace tailWord_2396961 prefixEnd_2396961 1230793103081701612764083 := by
  unfold tailWord_2396961
  simp only [CollatzResearch.WordTrace]
  refine ⟨87424349869227140192430737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58282899912818093461620491 87424349869227140192430737)
  ·
    refine ⟨65568262401920355144323053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87424349869227140192430737 65568262401920355144323053)
    ·
      refine ⟨24588098400720133179121145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65568262401920355144323053 24588098400720133179121145)
      ·
        refine ⟨18441073800540099884340859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24588098400720133179121145 18441073800540099884340859)
        ·
          refine ⟨27661610700810149826511289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18441073800540099884340859 27661610700810149826511289)
          ·
            refine ⟨20746208025607612369883467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27661610700810149826511289 20746208025607612369883467)
            ·
              refine ⟨31119312038411418554825201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20746208025607612369883467 31119312038411418554825201)
              ·
                refine ⟨23339484028808563916118901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31119312038411418554825201 23339484028808563916118901)
                ·
                  refine ⟨2188076627700802867136147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23339484028808563916118901 2188076627700802867136147)
                  ·
                    refine ⟨3282114941551204300704221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2188076627700802867136147 3282114941551204300704221)
                    ·
                      refine ⟨1230793103081701612764083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3282114941551204300704221 1230793103081701612764083)
                      ·
                        rfl

theorem cell23_2396961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_2396961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396961 prefixEnd_2396961 := by exact prefixLift 2396961
  have htrace : WordTrace (prefixWord ++ tailWord_2396961) baseStart_2396961 baseEnd_2396961 := by
    simpa [prefixWord, tailWord_2396961, baseEnd_2396961] using wordTrace_append hprefix tailTrace_2396961
  have hstable : (prefixWord ++ tailWord_2396961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396961).length < 2 ^ (prefixWord ++ tailWord_2396961).sum := by decide
  have hdescent : baseEnd_2396961 < baseStart_2396961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2396978 : List Nat := [3, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3]
def baseStart_2396978 : Nat := 118140960795 + 2396978 * 2 ^ 59
def prefixEnd_2396978 : Nat := 4983230072969 + 3 ^ 40 * 2396978 * 2
def baseEnd_2396978 : Nat := 1230801832252828046251505

theorem tailTrace_2396978 : CollatzResearch.WordTrace tailWord_2396978 prefixEnd_2396978 1230801832252828046251505 := by
  unfold tailWord_2396978
  simp only [CollatzResearch.WordTrace]
  refine ⟨21856242477541388023949897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58283313273443701397199725 21856242477541388023949897)
  ·
    refine ⟨16392181858156041017962423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21856242477541388023949897 16392181858156041017962423)
    ·
      refine ⟨24588272787234061526943635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16392181858156041017962423 24588272787234061526943635)
      ·
        refine ⟨36882409180851092290415453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24588272787234061526943635 36882409180851092290415453)
        ·
          refine ⟨13830903442819159608905795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36882409180851092290415453 13830903442819159608905795)
          ·
            refine ⟨20746355164228739413358693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13830903442819159608905795 20746355164228739413358693)
            ·
              refine ⟨3889941593292888640004755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20746355164228739413358693 3889941593292888640004755)
              ·
                refine ⟨5834912389939332960007133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3889941593292888640004755 5834912389939332960007133)
                ·
                  refine ⟨2188092146227249860002675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5834912389939332960007133 2188092146227249860002675)
                  ·
                    refine ⟨3282138219340874790004013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2188092146227249860002675 3282138219340874790004013)
                    ·
                      refine ⟨1230801832252828046251505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3282138219340874790004013 1230801832252828046251505)
                      ·
                        rfl

theorem cell23_2396978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_2396978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2396978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2396978 prefixEnd_2396978 := by exact prefixLift 2396978
  have htrace : WordTrace (prefixWord ++ tailWord_2396978) baseStart_2396978 baseEnd_2396978 := by
    simpa [prefixWord, tailWord_2396978, baseEnd_2396978] using wordTrace_append hprefix tailTrace_2396978
  have hstable : (prefixWord ++ tailWord_2396978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2396978).length < 2 ^ (prefixWord ++ tailWord_2396978).sum := by decide
  have hdescent : baseEnd_2396978 < baseStart_2396978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2396978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397001 : List Nat := [1, 2, 1, 1, 2, 5, 1, 4, 1, 1, 4]
def baseStart_2397001 : Nat := 118140960795 + 2397001 * 2 ^ 59
def prefixEnd_2397001 : Nat := 4983230072969 + 3 ^ 40 * 2397001 * 2
def baseEnd_2397001 : Nat := 1230813642307881456263899

theorem tailTrace_2397001 : CollatzResearch.WordTrace tailWord_2397001 prefixEnd_2397001 1230813642307881456263899 := by
  unfold tailWord_2397001
  simp only [CollatzResearch.WordTrace]
  refine ⟨87425808789082227023886857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58283872526054818015924571 87425808789082227023886857)
  ·
    refine ⟨65569356591811670267915143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87425808789082227023886857 65569356591811670267915143)
    ·
      refine ⟨98354034887717505401872715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65569356591811670267915143 98354034887717505401872715)
      ·
        refine ⟨147531052331576258102809073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98354034887717505401872715 147531052331576258102809073)
        ·
          refine ⟨110648289248682193577106805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147531052331576258102809073 110648289248682193577106805)
          ·
            refine ⟨10373277117063955647853763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110648289248682193577106805 10373277117063955647853763)
            ·
              refine ⟨15559915675595933471780645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10373277117063955647853763 15559915675595933471780645)
              ·
                refine ⟨2917484189174237525958871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15559915675595933471780645 2917484189174237525958871)
                ·
                  refine ⟨4376226283761356288938307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2917484189174237525958871 4376226283761356288938307)
                  ·
                    refine ⟨6564339425642034433407461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4376226283761356288938307 6564339425642034433407461)
                    ·
                      refine ⟨1230813642307881456263899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6564339425642034433407461 1230813642307881456263899)
                      ·
                        rfl

theorem cell23_2397001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 1, 4].length) (baseStart_2397001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397001 prefixEnd_2397001 := by exact prefixLift 2397001
  have htrace : WordTrace (prefixWord ++ tailWord_2397001) baseStart_2397001 baseEnd_2397001 := by
    simpa [prefixWord, tailWord_2397001, baseEnd_2397001] using wordTrace_append hprefix tailTrace_2397001
  have hstable : (prefixWord ++ tailWord_2397001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397001).length < 2 ^ (prefixWord ++ tailWord_2397001).sum := by decide
  have hdescent : baseEnd_2397001 < baseStart_2397001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397035 : List Nat := [1, 1, 1, 1, 2, 2, 4, 6, 1, 2, 2]
def baseStart_2397035 : Nat := 118140960795 + 2397035 * 2 ^ 59
def prefixEnd_2397035 : Nat := 4983230072969 + 3 ^ 40 * 2397035 * 2
def baseEnd_2397035 : Nat := 1230831100650134323238743

theorem tailTrace_2397035 : CollatzResearch.WordTrace tailWord_2397035 prefixEnd_2397035 1230831100650134323238743 := by
  unfold tailWord_2397035
  simp only [CollatzResearch.WordTrace]
  refine ⟨87427048870959050830624559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58284699247306033887083039 87427048870959050830624559)
  ·
    refine ⟨131140573306438576245936839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87427048870959050830624559 131140573306438576245936839)
    ·
      refine ⟨196710859959657864368905259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131140573306438576245936839 196710859959657864368905259)
      ·
        refine ⟨295066289939486796553357889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196710859959657864368905259 295066289939486796553357889)
        ·
          refine ⟨221299717454615097415018417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295066289939486796553357889 221299717454615097415018417)
          ·
            refine ⟨165974788090961323061263813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221299717454615097415018417 165974788090961323061263813)
            ·
              refine ⟨31120272767055248073986965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 165974788090961323061263813 31120272767055248073986965)
              ·
                refine ⟨1458762785955714753468139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31120272767055248073986965 1458762785955714753468139)
                ·
                  refine ⟨2188144178933572130202209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1458762785955714753468139 2188144178933572130202209)
                  ·
                    refine ⟨1641108134200179097651657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2188144178933572130202209 1641108134200179097651657)
                    ·
                      refine ⟨1230831100650134323238743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1641108134200179097651657 1230831100650134323238743)
                      ·
                        rfl

theorem cell23_2397035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 1, 2, 2].length) (baseStart_2397035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397035 prefixEnd_2397035 := by exact prefixLift 2397035
  have htrace : WordTrace (prefixWord ++ tailWord_2397035) baseStart_2397035 baseEnd_2397035 := by
    simpa [prefixWord, tailWord_2397035, baseEnd_2397035] using wordTrace_append hprefix tailTrace_2397035
  have hstable : (prefixWord ++ tailWord_2397035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397035).length < 2 ^ (prefixWord ++ tailWord_2397035).sum := by decide
  have hdescent : baseEnd_2397035 < baseStart_2397035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397045 : List Nat := [1, 3, 4, 1, 1, 2, 4, 1, 2, 4]
def baseStart_2397045 : Nat := 118140960795 + 2397045 * 2 ^ 59
def prefixEnd_2397045 : Nat := 4983230072969 + 3 ^ 40 * 2397045 * 2
def baseEnd_2397045 : Nat := 410278745152226428037899

theorem tailTrace_2397045 : CollatzResearch.WordTrace tailWord_2397045 prefixEnd_2397045 410278745152226428037899 := by
  unfold tailWord_2397045
  simp only [CollatzResearch.WordTrace]
  refine ⟨87427413600922822538488589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58284942400615215025659059 87427413600922822538488589)
  ·
    refine ⟨32785280100346058451933221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87427413600922822538488589 32785280100346058451933221)
    ·
      refine ⟨6147240018814885959737479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32785280100346058451933221 6147240018814885959737479)
      ·
        refine ⟨9220860028222328939606219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6147240018814885959737479 9220860028222328939606219)
        ·
          refine ⟨13831290042333493409409329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9220860028222328939606219 13831290042333493409409329)
          ·
            refine ⟨10373467531750120057056997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13831290042333493409409329 10373467531750120057056997)
            ·
              refine ⟨1945025162203147510698187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10373467531750120057056997 1945025162203147510698187)
              ·
                refine ⟨2917537743304721266047281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1945025162203147510698187 2917537743304721266047281)
                ·
                  refine ⟨2188153307478540949535461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2917537743304721266047281 2188153307478540949535461)
                  ·
                    refine ⟨410278745152226428037899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2188153307478540949535461 410278745152226428037899)
                    ·
                      rfl

theorem cell23_2397045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_2397045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397045 prefixEnd_2397045 := by exact prefixLift 2397045
  have htrace : WordTrace (prefixWord ++ tailWord_2397045) baseStart_2397045 baseEnd_2397045 := by
    simpa [prefixWord, tailWord_2397045, baseEnd_2397045] using wordTrace_append hprefix tailTrace_2397045
  have hstable : (prefixWord ++ tailWord_2397045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397045).length < 2 ^ (prefixWord ++ tailWord_2397045).sum := by decide
  have hdescent : baseEnd_2397045 < baseStart_2397045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397085 : List Nat := [1, 4, 2, 1, 2, 1, 4, 2, 2, 1, 3]
def baseStart_2397085 : Nat := 118140960795 + 2397085 * 2 ^ 59
def prefixEnd_2397085 : Nat := 4983230072969 + 3 ^ 40 * 2397085 * 2
def baseEnd_2397085 : Nat := 1230856774682859127613513

theorem tailTrace_2397085 : CollatzResearch.WordTrace tailWord_2397085 prefixEnd_2397085 1230856774682859127613513 := by
  unfold tailWord_2397085
  simp only [CollatzResearch.WordTrace]
  refine ⟨87428872520777909369944709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58285915013851939579963139 87428872520777909369944709)
  ·
    refine ⟨16392913597645858006864633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87428872520777909369944709 16392913597645858006864633)
    ·
      refine ⟨12294685198234393505148475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16392913597645858006864633 12294685198234393505148475)
      ·
        refine ⟨18442027797351590257722713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12294685198234393505148475 18442027797351590257722713)
        ·
          refine ⟨13831520848013692693292035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18442027797351590257722713 13831520848013692693292035)
          ·
            refine ⟨20747281272020539039938053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13831520848013692693292035 20747281272020539039938053)
            ·
              refine ⟨3890115238503851069988385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20747281272020539039938053 3890115238503851069988385)
              ·
                refine ⟨2917586428877888302491289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3890115238503851069988385 2917586428877888302491289)
                ·
                  refine ⟨2188189821658416226868467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2917586428877888302491289 2188189821658416226868467)
                  ·
                    refine ⟨3282284732487624340302701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2188189821658416226868467 3282284732487624340302701)
                    ·
                      refine ⟨1230856774682859127613513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3282284732487624340302701 1230856774682859127613513)
                      ·
                        rfl

theorem cell23_2397085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_2397085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397085 prefixEnd_2397085 := by exact prefixLift 2397085
  have htrace : WordTrace (prefixWord ++ tailWord_2397085) baseStart_2397085 baseEnd_2397085 := by
    simpa [prefixWord, tailWord_2397085, baseEnd_2397085] using wordTrace_append hprefix tailTrace_2397085
  have hstable : (prefixWord ++ tailWord_2397085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397085).length < 2 ^ (prefixWord ++ tailWord_2397085).sum := by decide
  have hdescent : baseEnd_2397085 < baseStart_2397085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397138 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_2397138 : Nat := 118140960795 + 2397138 * 2 ^ 59
def prefixEnd_2397138 : Nat := 4983230072969 + 3 ^ 40 * 2397138 * 2
def baseEnd_2397138 : Nat := 1230883989157547420250769

theorem tailTrace_2397138 : CollatzResearch.WordTrace tailWord_2397138 prefixEnd_2397138 1230883989157547420250769 := by
  unfold tailWord_2397138
  simp only [CollatzResearch.WordTrace]
  refine ⟨21857701397396474855406017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58287203726390599614416045 21857701397396474855406017)
  ·
    refine ⟨16393276048047356141554513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21857701397396474855406017 16393276048047356141554513)
    ·
      refine ⟨12294957036035517106165885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16393276048047356141554513 12294957036035517106165885)
      ·
        refine ⟨4610608888513318914812207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12294957036035517106165885 4610608888513318914812207)
        ·
          refine ⟨6915913332769978372218311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4610608888513318914812207 6915913332769978372218311)
          ·
            refine ⟨10373869999154967558327467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6915913332769978372218311 10373869999154967558327467)
            ·
              refine ⟨15560804998732451337491201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10373869999154967558327467 15560804998732451337491201)
              ·
                refine ⟨11670603749049338503118401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15560804998732451337491201 11670603749049338503118401)
                ·
                  refine ⟨8752952811787003877338801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11670603749049338503118401 8752952811787003877338801)
                  ·
                    refine ⟨6564714608840252908004101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8752952811787003877338801 6564714608840252908004101)
                    ·
                      refine ⟨1230883989157547420250769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6564714608840252908004101 1230883989157547420250769)
                      ·
                        rfl

theorem cell23_2397138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_2397138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397138 prefixEnd_2397138 := by exact prefixLift 2397138
  have htrace : WordTrace (prefixWord ++ tailWord_2397138) baseStart_2397138 baseEnd_2397138 := by
    simpa [prefixWord, tailWord_2397138, baseEnd_2397138] using wordTrace_append hprefix tailTrace_2397138
  have hstable : (prefixWord ++ tailWord_2397138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397138).length < 2 ^ (prefixWord ++ tailWord_2397138).sum := by decide
  have hdescent : baseEnd_2397138 < baseStart_2397138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397159 : List Nat := [1, 1, 5, 2, 2, 2, 3, 1, 2, 2, 2]
def baseStart_2397159 : Nat := 118140960795 + 2397159 * 2 ^ 59
def prefixEnd_2397159 : Nat := 4983230072969 + 3 ^ 40 * 2397159 * 2
def baseEnd_2397159 : Nat := 1230894772251291838088173

theorem tailTrace_2397159 : CollatzResearch.WordTrace tailWord_2397159 prefixEnd_2397159 1230894772251291838088173 := by
  unfold tailWord_2397159
  simp only [CollatzResearch.WordTrace]
  refine ⟨87431571522509820008138531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58287714348339880005425687 87431571522509820008138531)
  ·
    refine ⟨131147357283764730012207797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87431571522509820008138531 131147357283764730012207797)
    ·
      refine ⟨12295064745352943438644481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131147357283764730012207797 12295064745352943438644481)
      ·
        refine ⟨9221298559014707578983361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12295064745352943438644481 9221298559014707578983361)
        ·
          refine ⟨6915973919261030684237521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9221298559014707578983361 6915973919261030684237521)
          ·
            refine ⟨5186980439445773013178141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6915973919261030684237521 5186980439445773013178141)
            ·
              refine ⟨1945117664792164879941803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5186980439445773013178141 1945117664792164879941803)
              ·
                refine ⟨2917676497188247319912705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1945117664792164879941803 2917676497188247319912705)
                ·
                  refine ⟨2188257372891185489934529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2917676497188247319912705 2188257372891185489934529)
                  ·
                    refine ⟨1641193029668389117450897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2188257372891185489934529 1641193029668389117450897)
                    ·
                      refine ⟨1230894772251291838088173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1641193029668389117450897 1230894772251291838088173)
                      ·
                        rfl

theorem cell23_2397159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_2397159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397159 prefixEnd_2397159 := by exact prefixLift 2397159
  have htrace : WordTrace (prefixWord ++ tailWord_2397159) baseStart_2397159 baseEnd_2397159 := by
    simpa [prefixWord, tailWord_2397159, baseEnd_2397159] using wordTrace_append hprefix tailTrace_2397159
  have hstable : (prefixWord ++ tailWord_2397159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397159).length < 2 ^ (prefixWord ++ tailWord_2397159).sum := by decide
  have hdescent : baseEnd_2397159 < baseStart_2397159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397198 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4]
def baseStart_2397198 : Nat := 118140960795 + 2397198 * 2 ^ 59
def prefixEnd_2397198 : Nat := 4983230072969 + 3 ^ 40 * 2397198 * 2
def baseEnd_2397198 : Nat := 1230914797996817185500493

theorem tailTrace_2397198 : CollatzResearch.WordTrace tailWord_2397198 prefixEnd_2397198 1230914797996817185500493 := by
  unfold tailWord_2397198
  simp only [CollatzResearch.WordTrace]
  refine ⟨10929124246171066208601031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58288662646245686445872165 10929124246171066208601031)
  ·
    refine ⟨16393686369256599312901547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10929124246171066208601031 16393686369256599312901547)
    ·
      refine ⟨24590529553884898969352321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16393686369256599312901547 24590529553884898969352321)
      ·
        refine ⟨18442897165413674227014241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24590529553884898969352321 18442897165413674227014241)
        ·
          refine ⟨13832172874060255670260681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18442897165413674227014241 13832172874060255670260681)
          ·
            refine ⟨10374129655545191752695511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13832172874060255670260681 10374129655545191752695511)
            ·
              refine ⟨15561194483317787629043267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10374129655545191752695511 15561194483317787629043267)
              ·
                refine ⟨23341791724976681443564901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15561194483317787629043267 23341791724976681443564901)
                ·
                  refine ⟨4376585948433127770668419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23341791724976681443564901 4376585948433127770668419)
                  ·
                    refine ⟨6564878922649691656002629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4376585948433127770668419 6564878922649691656002629)
                    ·
                      refine ⟨1230914797996817185500493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6564878922649691656002629 1230914797996817185500493)
                      ·
                        rfl

theorem cell23_2397198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_2397198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397198 prefixEnd_2397198 := by exact prefixLift 2397198
  have htrace : WordTrace (prefixWord ++ tailWord_2397198) baseStart_2397198 baseEnd_2397198 := by
    simpa [prefixWord, tailWord_2397198, baseEnd_2397198] using wordTrace_append hprefix tailTrace_2397198
  have hstable : (prefixWord ++ tailWord_2397198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397198).length < 2 ^ (prefixWord ++ tailWord_2397198).sum := by decide
  have hdescent : baseEnd_2397198 < baseStart_2397198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397268 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 3, 5]
def baseStart_2397268 : Nat := 118140960795 + 2397268 * 2 ^ 59
def prefixEnd_2397268 : Nat := 4983230072969 + 3 ^ 40 * 2397268 * 2
def baseEnd_2397268 : Nat := 410316913880877303875057

theorem tailTrace_2397268 : CollatzResearch.WordTrace tailWord_2397268 prefixEnd_2397268 410316913880877303875057 := by
  unfold tailWord_2397268
  simp only [CollatzResearch.WordTrace]
  refine ⟨43717773539557465811928229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58290364719409954415904305 43717773539557465811928229)
  ·
    refine ⟨8197082538667024839736543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43717773539557465811928229 8197082538667024839736543)
    ·
      refine ⟨12295623808000537259604815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8197082538667024839736543 12295623808000537259604815)
      ·
        refine ⟨18443435712000805889407223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12295623808000537259604815 18443435712000805889407223)
        ·
          refine ⟨27665153568001208834110835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18443435712000805889407223 27665153568001208834110835)
          ·
            refine ⟨41497730352001813251166253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27665153568001208834110835 41497730352001813251166253)
            ·
              refine ⟨15561648882000679969187345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41497730352001813251166253 15561648882000679969187345)
              ·
                refine ⟨11671236661500509976890509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15561648882000679969187345 11671236661500509976890509)
                ·
                  refine ⟨4376713748062691241333941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11671236661500509976890509 4376713748062691241333941)
                  ·
                    refine ⟨410316913880877303875057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4376713748062691241333941 410316913880877303875057)
                    ·
                      rfl

theorem cell23_2397268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_2397268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397268 prefixEnd_2397268 := by exact prefixLift 2397268
  have htrace : WordTrace (prefixWord ++ tailWord_2397268) baseStart_2397268 baseEnd_2397268 := by
    simpa [prefixWord, tailWord_2397268, baseEnd_2397268] using wordTrace_append hprefix tailTrace_2397268
  have hstable : (prefixWord ++ tailWord_2397268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397268).length < 2 ^ (prefixWord ++ tailWord_2397268).sum := by decide
  have hdescent : baseEnd_2397268 < baseStart_2397268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397282 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_2397282 : Nat := 118140960795 + 2397282 * 2 ^ 59
def prefixEnd_2397282 : Nat := 4983230072969 + 3 ^ 40 * 2397282 * 2
def baseEnd_2397282 : Nat := 1230957930371794856850107

theorem tailTrace_2397282 : CollatzResearch.WordTrace tailWord_2397282 prefixEnd_2397282 1230957930371794856850107 := by
  unfold tailWord_2397282
  simp only [CollatzResearch.WordTrace]
  refine ⟨21859014425266053003716525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58290705134042808009910733 21859014425266053003716525)
  ·
    refine ⟨8197130409474769876393697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21859014425266053003716525 8197130409474769876393697)
    ·
      refine ⟨6147847807106077407295273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8197130409474769876393697 6147847807106077407295273)
      ·
        refine ⟨4610885855329558055471455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6147847807106077407295273 4610885855329558055471455)
        ·
          refine ⟨6916328782994337083207183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4610885855329558055471455 6916328782994337083207183)
          ·
            refine ⟨10374493174491505624810775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6916328782994337083207183 10374493174491505624810775)
            ·
              refine ⟨15561739761737258437216163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10374493174491505624810775 15561739761737258437216163)
              ·
                refine ⟨23342609642605887655824245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15561739761737258437216163 23342609642605887655824245)
                ·
                  refine ⟨2188369653994301967733523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23342609642605887655824245 2188369653994301967733523)
                  ·
                    refine ⟨3282554480991452951600285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2188369653994301967733523 3282554480991452951600285)
                    ·
                      refine ⟨1230957930371794856850107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3282554480991452951600285 1230957930371794856850107)
                      ·
                        rfl

theorem cell23_2397282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_2397282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397282 prefixEnd_2397282 := by exact prefixLift 2397282
  have htrace : WordTrace (prefixWord ++ tailWord_2397282) baseStart_2397282 baseEnd_2397282 := by
    simpa [prefixWord, tailWord_2397282, baseEnd_2397282] using wordTrace_append hprefix tailTrace_2397282
  have hstable : (prefixWord ++ tailWord_2397282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397282).length < 2 ^ (prefixWord ++ tailWord_2397282).sum := by decide
  have hdescent : baseEnd_2397282 < baseStart_2397282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397298 : List Nat := [3, 2, 1, 2, 2, 1, 1, 4, 1, 6]
def baseStart_2397298 : Nat := 118140960795 + 2397298 * 2 ^ 59
def prefixEnd_2397298 : Nat := 4983230072969 + 3 ^ 40 * 2397298 * 2
def baseEnd_2397298 : Nat := 410322048687422264750011

theorem tailTrace_2397298 : CollatzResearch.WordTrace tailWord_2397298 prefixEnd_2397298 410322048687422264750011 := by
  unfold tailWord_2397298
  simp only [CollatzResearch.WordTrace]
  refine ⟨21859160317251561686862137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58291094179337497831632365 21859160317251561686862137)
  ·
    refine ⟨16394370237938671265146603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21859160317251561686862137 16394370237938671265146603)
    ·
      refine ⟨24591555356908006897719905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16394370237938671265146603 24591555356908006897719905)
      ·
        refine ⟨18443666517681005173289929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24591555356908006897719905 18443666517681005173289929)
        ·
          refine ⟨13832749888260753879967447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18443666517681005173289929 13832749888260753879967447)
          ·
            refine ⟨20749124832391130819951171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13832749888260753879967447 20749124832391130819951171)
            ·
              refine ⟨31123687248586696229926757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20749124832391130819951171 31123687248586696229926757)
              ·
                refine ⟨5835691359110005543111267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31123687248586696229926757 5835691359110005543111267)
                ·
                  refine ⟨8753537038665008314666901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5835691359110005543111267 8753537038665008314666901)
                  ·
                    refine ⟨410322048687422264750011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8753537038665008314666901 410322048687422264750011)
                    ·
                      rfl

theorem cell23_2397298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_2397298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397298 prefixEnd_2397298 := by exact prefixLift 2397298
  have htrace : WordTrace (prefixWord ++ tailWord_2397298) baseStart_2397298 baseEnd_2397298 := by
    simpa [prefixWord, tailWord_2397298, baseEnd_2397298] using wordTrace_append hprefix tailTrace_2397298
  have hstable : (prefixWord ++ tailWord_2397298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397298).length < 2 ^ (prefixWord ++ tailWord_2397298).sum := by decide
  have hdescent : baseEnd_2397298 < baseStart_2397298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397308 : List Nat := [2, 2, 2, 1, 1, 3, 2, 3, 1, 1, 5]
def baseStart_2397308 : Nat := 118140960795 + 2397308 * 2 ^ 59
def prefixEnd_2397308 : Nat := 4983230072969 + 3 ^ 40 * 2397308 * 2
def baseEnd_2397308 : Nat := 1230971280868811755124987

theorem tailTrace_2397308 : CollatzResearch.WordTrace tailWord_2397308 prefixEnd_2397308 1230971280868811755124987 := by
  unfold tailWord_2397308
  simp only [CollatzResearch.WordTrace]
  refine ⟨43718502999485009227656289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58291337332646678970208385 43718502999485009227656289)
  ·
    refine ⟨32788877249613756920742217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43718502999485009227656289 32788877249613756920742217)
    ·
      refine ⟨24591657937210317690556663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32788877249613756920742217 24591657937210317690556663)
      ·
        refine ⟨36887486905815476535834995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24591657937210317690556663 36887486905815476535834995)
        ·
          refine ⟨55331230358723214803752493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36887486905815476535834995 55331230358723214803752493)
          ·
            refine ⟨20749211384521205551407185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55331230358723214803752493 20749211384521205551407185)
            ·
              refine ⟨15561908538390904163555389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20749211384521205551407185 15561908538390904163555389)
              ·
                refine ⟨5835715701896589061333271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15561908538390904163555389 5835715701896589061333271)
                ·
                  refine ⟨8753573552844883591999907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5835715701896589061333271 8753573552844883591999907)
                  ·
                    refine ⟨13130360329267325387999861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8753573552844883591999907 13130360329267325387999861)
                    ·
                      refine ⟨1230971280868811755124987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13130360329267325387999861 1230971280868811755124987)
                      ·
                        rfl

theorem cell23_2397308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_2397308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397308 prefixEnd_2397308 := by exact prefixLift 2397308
  have htrace : WordTrace (prefixWord ++ tailWord_2397308) baseStart_2397308 baseEnd_2397308 := by
    simpa [prefixWord, tailWord_2397308, baseEnd_2397308] using wordTrace_append hprefix tailTrace_2397308
  have hstable : (prefixWord ++ tailWord_2397308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397308).length < 2 ^ (prefixWord ++ tailWord_2397308).sum := by decide
  have hdescent : baseEnd_2397308 < baseStart_2397308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397335 : List Nat := [1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 4]
def baseStart_2397335 : Nat := 118140960795 + 2397335 * 2 ^ 59
def prefixEnd_2397335 : Nat := 4983230072969 + 3 ^ 40 * 2397335 * 2
def baseEnd_2397335 : Nat := 1230985144846483149487363

theorem tailTrace_2397335 : CollatzResearch.WordTrace tailWord_2397335 prefixEnd_2397335 1230985144846483149487363 := by
  unfold tailWord_2397335
  simp only [CollatzResearch.WordTrace]
  refine ⟨87437990769872202066545459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58291993846581468044363639 87437990769872202066545459)
  ·
    refine ⟨131156986154808303099818189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87437990769872202066545459 131156986154808303099818189)
    ·
      refine ⟨49183869808053113662431821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131156986154808303099818189 49183869808053113662431821)
      ·
        refine ⟨18443951178019917623411933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49183869808053113662431821 18443951178019917623411933)
        ·
          refine ⟨6916481691757469108779475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18443951178019917623411933 6916481691757469108779475)
          ·
            refine ⟨10374722537636203663169213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6916481691757469108779475 10374722537636203663169213)
            ·
              refine ⟨3890520951613576373688455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10374722537636203663169213 3890520951613576373688455)
              ·
                refine ⟨5835781427420364560532683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3890520951613576373688455 5835781427420364560532683)
                ·
                  refine ⟨8753672141130546840799025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5835781427420364560532683 8753672141130546840799025)
                  ·
                    refine ⟨6565254105847910130599269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8753672141130546840799025 6565254105847910130599269)
                    ·
                      refine ⟨1230985144846483149487363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6565254105847910130599269 1230985144846483149487363)
                      ·
                        rfl

theorem cell23_2397335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_2397335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397335 prefixEnd_2397335 := by exact prefixLift 2397335
  have htrace : WordTrace (prefixWord ++ tailWord_2397335) baseStart_2397335 baseEnd_2397335 := by
    simpa [prefixWord, tailWord_2397335, baseEnd_2397335] using wordTrace_append hprefix tailTrace_2397335
  have hstable : (prefixWord ++ tailWord_2397335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397335).length < 2 ^ (prefixWord ++ tailWord_2397335).sum := by decide
  have hdescent : baseEnd_2397335 < baseStart_2397335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397372 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 4, 1, 3]
def baseStart_2397372 : Nat := 118140960795 + 2397372 * 2 ^ 59
def prefixEnd_2397372 : Nat := 4983230072969 + 3 ^ 40 * 2397372 * 2
def baseEnd_2397372 : Nat := 1231004143630699504724693

theorem tailTrace_2397372 : CollatzResearch.WordTrace tailWord_2397372 prefixEnd_2397372 1231004143630699504724693 := by
  unfold tailWord_2397372
  simp only [CollatzResearch.WordTrace]
  refine ⟨43719670135369078692821185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58292893513825438257094913 43719670135369078692821185)
  ·
    refine ⟨32789752601526809019615889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43719670135369078692821185 32789752601526809019615889)
    ·
      refine ⟨24592314451145106764711917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32789752601526809019615889 24592314451145106764711917)
      ·
        refine ⟨9222117919179415036766969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24592314451145106764711917 9222117919179415036766969)
        ·
          refine ⟨6916588439384561277575227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9222117919179415036766969 6916588439384561277575227)
          ·
            refine ⟨10374882659076841916362841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6916588439384561277575227 10374882659076841916362841)
            ·
              refine ⟨7781161994307631437272131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10374882659076841916362841 7781161994307631437272131)
              ·
                refine ⟨11671742991461447155908197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7781161994307631437272131 11671742991461447155908197)
                ·
                  refine ⟨2188451810899021341732787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11671742991461447155908197 2188451810899021341732787)
                  ·
                    refine ⟨3282677716348532012599181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2188451810899021341732787 3282677716348532012599181)
                    ·
                      refine ⟨1231004143630699504724693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3282677716348532012599181 1231004143630699504724693)
                      ·
                        rfl

theorem cell23_2397372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_2397372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397372 prefixEnd_2397372 := by exact prefixLift 2397372
  have htrace : WordTrace (prefixWord ++ tailWord_2397372) baseStart_2397372 baseEnd_2397372 := by
    simpa [prefixWord, tailWord_2397372, baseEnd_2397372] using wordTrace_append hprefix tailTrace_2397372
  have hstable : (prefixWord ++ tailWord_2397372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397372).length < 2 ^ (prefixWord ++ tailWord_2397372).sum := by decide
  have hdescent : baseEnd_2397372 < baseStart_2397372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397412 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 6, 2, 2]
def baseStart_2397412 : Nat := 118140960795 + 2397412 * 2 ^ 59
def prefixEnd_2397412 : Nat := 4983230072969 + 3 ^ 40 * 2397412 * 2
def baseEnd_2397412 : Nat := 1231024682856879348224509

theorem tailTrace_2397412 : CollatzResearch.WordTrace tailWord_2397412 prefixEnd_2397412 1231024682856879348224509 := by
  unfold tailWord_2397412
  simp only [CollatzResearch.WordTrace]
  refine ⟨43720399595296622108549245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58293866127062162811398993 43720399595296622108549245)
  ·
    refine ⟨16395149848236233290705967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43720399595296622108549245 16395149848236233290705967)
    ·
      refine ⟨24592724772354349936058951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16395149848236233290705967 24592724772354349936058951)
      ·
        refine ⟨36889087158531524904088427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24592724772354349936058951 36889087158531524904088427)
        ·
          refine ⟨55333630737797287356132641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36889087158531524904088427 55333630737797287356132641)
          ·
            refine ⟨41500223053347965517099481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55333630737797287356132641 41500223053347965517099481)
            ·
              refine ⟨31125167290010974137824611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41500223053347965517099481 31125167290010974137824611)
              ·
                refine ⟨46687750935016461206736917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31125167290010974137824611 46687750935016461206736917)
                ·
                  refine ⟨2188488325078896619065793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46687750935016461206736917 2188488325078896619065793)
                  ·
                    refine ⟨1641366243809172464299345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2188488325078896619065793 1641366243809172464299345)
                    ·
                      refine ⟨1231024682856879348224509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1641366243809172464299345 1231024682856879348224509)
                      ·
                        rfl

theorem cell23_2397412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 6, 2, 2].length) (baseStart_2397412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397412 prefixEnd_2397412 := by exact prefixLift 2397412
  have htrace : WordTrace (prefixWord ++ tailWord_2397412) baseStart_2397412 baseEnd_2397412 := by
    simpa [prefixWord, tailWord_2397412, baseEnd_2397412] using wordTrace_append hprefix tailTrace_2397412
  have hstable : (prefixWord ++ tailWord_2397412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397412).length < 2 ^ (prefixWord ++ tailWord_2397412).sum := by decide
  have hdescent : baseEnd_2397412 < baseStart_2397412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397445 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 2, 3, 3]
def baseStart_2397445 : Nat := 118140960795 + 2397445 * 2 ^ 59
def prefixEnd_2397445 : Nat := 4983230072969 + 3 ^ 40 * 2397445 * 2
def baseEnd_2397445 : Nat := 1231041627718477719111857

theorem tailTrace_2397445 : CollatzResearch.WordTrace tailWord_2397445 prefixEnd_2397445 1231041627718477719111857 := by
  unfold tailWord_2397445
  simp only [CollatzResearch.WordTrace]
  refine ⟨87442002799473690853049789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58294668532982460568699859 87442002799473690853049789)
  ·
    refine ⟨32790751049802634069893671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87442002799473690853049789 32790751049802634069893671)
    ·
      refine ⟨49186126574703951104840507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32790751049802634069893671 49186126574703951104840507)
      ·
        refine ⟨73779189862055926657260761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49186126574703951104840507 73779189862055926657260761)
        ·
          refine ⟨55334392396541944992945571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73779189862055926657260761 55334392396541944992945571)
          ·
            refine ⟨83001588594812917489418357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55334392396541944992945571 83001588594812917489418357)
            ·
              refine ⟨7781398930763711014632971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83001588594812917489418357 7781398930763711014632971)
              ·
                refine ⟨11672098396145566521949457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7781398930763711014632971 11672098396145566521949457)
                ·
                  refine ⟨8754073797109174891462093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11672098396145566521949457 8754073797109174891462093)
                  ·
                    refine ⟨3282777673915940584298285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8754073797109174891462093 3282777673915940584298285)
                    ·
                      refine ⟨1231041627718477719111857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3282777673915940584298285 1231041627718477719111857)
                      ·
                        rfl

theorem cell23_2397445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 3, 3].length) (baseStart_2397445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397445 prefixEnd_2397445 := by exact prefixLift 2397445
  have htrace : WordTrace (prefixWord ++ tailWord_2397445) baseStart_2397445 baseEnd_2397445 := by
    simpa [prefixWord, tailWord_2397445, baseEnd_2397445] using wordTrace_append hprefix tailTrace_2397445
  have hstable : (prefixWord ++ tailWord_2397445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397445).length < 2 ^ (prefixWord ++ tailWord_2397445).sum := by decide
  have hdescent : baseEnd_2397445 < baseStart_2397445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397469 : List Nat := [1, 4, 2, 3, 1, 2, 2, 3, 5]
def baseStart_2397469 : Nat := 118140960795 + 2397469 * 2 ^ 59
def prefixEnd_2397469 : Nat := 4983230072969 + 3 ^ 40 * 2397469 * 2
def baseEnd_2397469 : Nat := 136783772361576180579083

theorem tailTrace_2397469 : CollatzResearch.WordTrace tailWord_2397469 prefixEnd_2397469 136783772361576180579083 := by
  unfold tailWord_2397469
  simp only [CollatzResearch.WordTrace]
  refine ⟨87442878151386742951923461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58295252100924495301282307 87442878151386742951923461)
  ·
    refine ⟨16395539653385014303485649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87442878151386742951923461 16395539653385014303485649)
    ·
      refine ⟨12296654740038760727614237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16395539653385014303485649 12296654740038760727614237)
      ·
        refine ⟨4611245527514535272855339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12296654740038760727614237 4611245527514535272855339)
        ·
          refine ⟨6916868291271802909283009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4611245527514535272855339 6916868291271802909283009)
          ·
            refine ⟨5187651218453852181962257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6916868291271802909283009 5187651218453852181962257)
            ·
              refine ⟨3890738413840389136471693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5187651218453852181962257 3890738413840389136471693)
              ·
                refine ⟨1459026905190145926176885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3890738413840389136471693 1459026905190145926176885)
                ·
                  refine ⟨136783772361576180579083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1459026905190145926176885 136783772361576180579083)
                  ·
                    rfl

theorem cell23_2397469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_2397469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397469 prefixEnd_2397469 := by exact prefixLift 2397469
  have htrace : WordTrace (prefixWord ++ tailWord_2397469) baseStart_2397469 baseEnd_2397469 := by
    simpa [prefixWord, tailWord_2397469, baseEnd_2397469] using wordTrace_append hprefix tailTrace_2397469
  have hstable : (prefixWord ++ tailWord_2397469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397469).length < 2 ^ (prefixWord ++ tailWord_2397469).sum := by decide
  have hdescent : baseEnd_2397469 < baseStart_2397469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397522 : List Nat := [3, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3]
def baseStart_2397522 : Nat := 118140960795 + 2397522 * 2 ^ 59
def prefixEnd_2397522 : Nat := 4983230072969 + 3 ^ 40 * 2397522 * 2
def baseEnd_2397522 : Nat := 1231081165728873917849003

theorem tailTrace_2397522 : CollatzResearch.WordTrace tailWord_2397522 prefixEnd_2397522 1231081165728873917849003 := by
  unfold tailWord_2397522
  simp only [CollatzResearch.WordTrace]
  refine ⟨21861202805048683250900705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58296540813463155335735213 21861202805048683250900705)
  ·
    refine ⟨16395902103786512438175529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21861202805048683250900705 16395902103786512438175529)
    ·
      refine ⟨12296926577839884328631647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16395902103786512438175529 12296926577839884328631647)
      ·
        refine ⟨18445389866759826492947471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12296926577839884328631647 18445389866759826492947471)
        ·
          refine ⟨27668084800139739739421207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18445389866759826492947471 27668084800139739739421207)
          ·
            refine ⟨41502127200209609609131811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27668084800139739739421207 41502127200209609609131811)
            ·
              refine ⟨62253190800314414413697717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41502127200209609609131811 62253190800314414413697717)
              ·
                refine ⟨5836236637529476351284161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62253190800314414413697717 5836236637529476351284161)
                ·
                  refine ⟨4377177478147107263463121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5836236637529476351284161 4377177478147107263463121)
                  ·
                    refine ⟨3282883108610330447597341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4377177478147107263463121 3282883108610330447597341)
                    ·
                      refine ⟨1231081165728873917849003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3282883108610330447597341 1231081165728873917849003)
                      ·
                        rfl

theorem cell23_2397522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_2397522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397522 prefixEnd_2397522 := by exact prefixLift 2397522
  have htrace : WordTrace (prefixWord ++ tailWord_2397522) baseStart_2397522 baseEnd_2397522 := by
    simpa [prefixWord, tailWord_2397522, baseEnd_2397522] using wordTrace_append hprefix tailTrace_2397522
  have hstable : (prefixWord ++ tailWord_2397522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397522).length < 2 ^ (prefixWord ++ tailWord_2397522).sum := by decide
  have hdescent : baseEnd_2397522 < baseStart_2397522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397525 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 8]
def baseStart_2397525 : Nat := 118140960795 + 2397525 * 2 ^ 59
def prefixEnd_2397525 : Nat := 4983230072969 + 3 ^ 40 * 2397525 * 2
def baseEnd_2397525 : Nat := 136786967352315267345721

theorem tailTrace_2397525 : CollatzResearch.WordTrace tailWord_2397525 prefixEnd_2397525 136786967352315267345721 := by
  unfold tailWord_2397525
  simp only [CollatzResearch.WordTrace]
  refine ⟨87444920639183864515962029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58296613759455909677308019 87444920639183864515962029)
  ·
    refine ⟨32791845239693949193485761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87444920639183864515962029 32791845239693949193485761)
    ·
      refine ⟨24593883929770461895114321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32791845239693949193485761 24593883929770461895114321)
      ·
        refine ⟨18445412947327846421335741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24593883929770461895114321 18445412947327846421335741)
        ·
          refine ⟨6917029855247942408000903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18445412947327846421335741 6917029855247942408000903)
          ·
            refine ⟨10375544782871913612001355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6917029855247942408000903 10375544782871913612001355)
            ·
              refine ⟨15563317174307870418002033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10375544782871913612001355 15563317174307870418002033)
              ·
                refine ⟨11672487880730902813501525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15563317174307870418002033 11672487880730902813501525)
                ·
                  refine ⟨136786967352315267345721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11672487880730902813501525 136786967352315267345721)
                  ·
                    rfl

theorem cell23_2397525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 8].length) (baseStart_2397525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397525 prefixEnd_2397525 := by exact prefixLift 2397525
  have htrace : WordTrace (prefixWord ++ tailWord_2397525) baseStart_2397525 baseEnd_2397525 := by
    simpa [prefixWord, tailWord_2397525, baseEnd_2397525] using wordTrace_append hprefix tailTrace_2397525
  have hstable : (prefixWord ++ tailWord_2397525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397525).length < 2 ^ (prefixWord ++ tailWord_2397525).sum := by decide
  have hdescent : baseEnd_2397525 < baseStart_2397525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397529 : List Nat := [1, 2, 1, 2, 2, 2, 5, 3, 1, 4]
def baseStart_2397529 : Nat := 118140960795 + 2397529 * 2 ^ 59
def prefixEnd_2397529 : Nat := 4983230072969 + 3 ^ 40 * 2397529 * 2
def baseEnd_2397529 : Nat := 410361586697818463487157

theorem tailTrace_2397529 : CollatzResearch.WordTrace tailWord_2397529 prefixEnd_2397529 410361586697818463487157 := by
  unfold tailWord_2397529
  simp only [CollatzResearch.WordTrace]
  refine ⟨87445066531169373199107641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58296711020779582132738427 87445066531169373199107641)
  ·
    refine ⟨65583799898377029899330731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87445066531169373199107641 65583799898377029899330731)
    ·
      refine ⟨98375699847565544848996097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65583799898377029899330731 98375699847565544848996097)
      ·
        refine ⟨73781774885674158636747073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98375699847565544848996097 73781774885674158636747073)
        ·
          refine ⟨55336331164255618977560305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73781774885674158636747073 55336331164255618977560305)
          ·
            refine ⟨41502248373191714233170229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55336331164255618977560305 41502248373191714233170229)
            ·
              refine ⟨3890835784986723209359709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41502248373191714233170229 3890835784986723209359709)
              ·
                refine ⟨1459063419370021203509891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3890835784986723209359709 1459063419370021203509891)
                ·
                  refine ⟨2188595129055031805264837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1459063419370021203509891 2188595129055031805264837)
                  ·
                    refine ⟨410361586697818463487157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2188595129055031805264837 410361586697818463487157)
                    ·
                      rfl

theorem cell23_2397529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 1, 4].length) (baseStart_2397529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397529 prefixEnd_2397529 := by exact prefixLift 2397529
  have htrace : WordTrace (prefixWord ++ tailWord_2397529) baseStart_2397529 baseEnd_2397529 := by
    simpa [prefixWord, tailWord_2397529, baseEnd_2397529] using wordTrace_append hprefix tailTrace_2397529
  have hstable : (prefixWord ++ tailWord_2397529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397529).length < 2 ^ (prefixWord ++ tailWord_2397529).sum := by decide
  have hdescent : baseEnd_2397529 < baseStart_2397529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397546 : List Nat := [3, 1, 3, 3, 2, 2, 1, 1, 3, 4]
def baseStart_2397546 : Nat := 118140960795 + 2397546 * 2 ^ 59
def prefixEnd_2397546 : Nat := 4983230072969 + 3 ^ 40 * 2397546 * 2
def baseEnd_2397546 : Nat := 410364496421527274649631

theorem tailTrace_2397546 : CollatzResearch.WordTrace tailWord_2397546 prefixEnd_2397546 410364496421527274649631 := by
  unfold tailWord_2397546
  simp only [CollatzResearch.WordTrace]
  refine ⟨21861421643026946275619123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58297124381405190068317661 21861421643026946275619123)
  ·
    refine ⟨32792132464540419413428685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21861421643026946275619123 32792132464540419413428685)
    ·
      refine ⟨12297049674202657280035757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32792132464540419413428685 12297049674202657280035757)
      ·
        refine ⟨4611393627825996480013409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12297049674202657280035757 4611393627825996480013409)
        ·
          refine ⟨3458545220869497360010057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4611393627825996480013409 3458545220869497360010057)
          ·
            refine ⟨2593908915652123020007543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3458545220869497360010057 2593908915652123020007543)
            ·
              refine ⟨3890863373478184530011315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2593908915652123020007543 3890863373478184530011315)
              ·
                refine ⟨5836295060217276795016973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3890863373478184530011315 5836295060217276795016973)
                ·
                  refine ⟨2188610647581478798131365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5836295060217276795016973 2188610647581478798131365)
                  ·
                    refine ⟨410364496421527274649631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2188610647581478798131365 410364496421527274649631)
                    ·
                      rfl

theorem cell23_2397546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_2397546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397546 prefixEnd_2397546 := by exact prefixLift 2397546
  have htrace : WordTrace (prefixWord ++ tailWord_2397546) baseStart_2397546 baseEnd_2397546 := by
    simpa [prefixWord, tailWord_2397546, baseEnd_2397546] using wordTrace_append hprefix tailTrace_2397546
  have hstable : (prefixWord ++ tailWord_2397546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397546).length < 2 ^ (prefixWord ++ tailWord_2397546).sum := by decide
  have hdescent : baseEnd_2397546 < baseStart_2397546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397572 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 3, 5]
def baseStart_2397572 : Nat := 118140960795 + 2397572 * 2 ^ 59
def prefixEnd_2397572 : Nat := 4983230072969 + 3 ^ 40 * 2397572 * 2
def baseEnd_2397572 : Nat := 410368946587199574074591

theorem tailTrace_2397572 : CollatzResearch.WordTrace tailWord_2397572 prefixEnd_2397572 410368946587199574074591 := by
  unfold tailWord_2397572
  simp only [CollatzResearch.WordTrace]
  refine ⟨43723317435006795771461485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58297756580009061028615313 43723317435006795771461485)
  ·
    refine ⟨16396244038127548414298057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43723317435006795771461485 16396244038127548414298057)
    ·
      refine ⟨12297183028595661310723543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16396244038127548414298057 12297183028595661310723543)
      ·
        refine ⟨18445774542893491966085315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12297183028595661310723543 18445774542893491966085315)
        ·
          refine ⟨27668661814340237949127973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18445774542893491966085315 27668661814340237949127973)
          ·
            refine ⟨5187874090188794615461495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27668661814340237949127973 5187874090188794615461495)
            ·
              refine ⟨7781811135283191923192243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5187874090188794615461495 7781811135283191923192243)
              ·
                refine ⟨11672716702924787884788365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7781811135283191923192243 11672716702924787884788365)
                ·
                  refine ⟨4377268763596795456795637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11672716702924787884788365 4377268763596795456795637)
                  ·
                    refine ⟨410368946587199574074591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4377268763596795456795637 410368946587199574074591)
                    ·
                      rfl

theorem cell23_2397572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_2397572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397572 prefixEnd_2397572 := by exact prefixLift 2397572
  have htrace : WordTrace (prefixWord ++ tailWord_2397572) baseStart_2397572 baseEnd_2397572 := by
    simpa [prefixWord, tailWord_2397572, baseEnd_2397572] using wordTrace_append hprefix tailTrace_2397572
  have hstable : (prefixWord ++ tailWord_2397572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397572).length < 2 ^ (prefixWord ++ tailWord_2397572).sum := by decide
  have hdescent : baseEnd_2397572 < baseStart_2397572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397579 : List Nat := [1, 1, 1, 1, 4, 3, 4, 1, 2, 3, 2]
def baseStart_2397579 : Nat := 118140960795 + 2397579 * 2 ^ 59
def prefixEnd_2397579 : Nat := 4983230072969 + 3 ^ 40 * 2397579 * 2
def baseEnd_2397579 : Nat := 1231110434126180194836241

theorem tailTrace_2397579 : CollatzResearch.WordTrace tailWord_2397579 prefixEnd_2397579 1231110434126180194836241 := by
  unfold tailWord_2397579
  simp only [CollatzResearch.WordTrace]
  refine ⟨87446890180988231738427791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58297926787325487825618527 87446890180988231738427791)
  ·
    refine ⟨131170335271482347607641687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87446890180988231738427791 131170335271482347607641687)
    ·
      refine ⟨196755502907223521411462531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131170335271482347607641687 196755502907223521411462531)
      ·
        refine ⟨295133254360835282117193797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196755502907223521411462531 295133254360835282117193797)
        ·
          refine ⟨55337485192656615396973837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 295133254360835282117193797 55337485192656615396973837)
          ·
            refine ⟨20751556947246230773865189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55337485192656615396973837 20751556947246230773865189)
            ·
              refine ⟨3890916927608668270099723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20751556947246230773865189 3890916927608668270099723)
              ·
                refine ⟨5836375391413002405149585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3890916927608668270099723 5836375391413002405149585)
                ·
                  refine ⟨4377281543559751803862189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5836375391413002405149585 4377281543559751803862189)
                  ·
                    refine ⟨1641480578834906926448321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4377281543559751803862189 1641480578834906926448321)
                    ·
                      refine ⟨1231110434126180194836241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1641480578834906926448321 1231110434126180194836241)
                      ·
                        rfl

theorem cell23_2397579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 3, 2].length) (baseStart_2397579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397579 prefixEnd_2397579 := by exact prefixLift 2397579
  have htrace : WordTrace (prefixWord ++ tailWord_2397579) baseStart_2397579 baseEnd_2397579 := by
    simpa [prefixWord, tailWord_2397579, baseEnd_2397579] using wordTrace_append hprefix tailTrace_2397579
  have hstable : (prefixWord ++ tailWord_2397579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397579).length < 2 ^ (prefixWord ++ tailWord_2397579).sum := by decide
  have hdescent : baseEnd_2397579 < baseStart_2397579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397585 : List Nat := [1, 2, 2, 1, 1, 1, 2, 6, 1, 6]
def baseStart_2397585 : Nat := 118140960795 + 2397585 * 2 ^ 59
def prefixEnd_2397585 : Nat := 4983230072969 + 3 ^ 40 * 2397585 * 2
def baseEnd_2397585 : Nat := 410371171670035723787071

theorem tailTrace_2397585 : CollatzResearch.WordTrace tailWord_2397585 prefixEnd_2397585 410371171670035723787071 := by
  unfold tailWord_2397585
  simp only [CollatzResearch.WordTrace]
  refine ⟨87447109018966494763146209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58298072679310996508764139 87447109018966494763146209)
  ·
    refine ⟨65585331764224871072359657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87447109018966494763146209 65585331764224871072359657)
    ·
      refine ⟨49188998823168653304269743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65585331764224871072359657 49188998823168653304269743)
      ·
        refine ⟨73783498234752979956404615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49188998823168653304269743 73783498234752979956404615)
        ·
          refine ⟨110675247352129469934606923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73783498234752979956404615 110675247352129469934606923)
          ·
            refine ⟨166012871028194204901910385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110675247352129469934606923 166012871028194204901910385)
            ·
              refine ⟨124509653271145653676432789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166012871028194204901910385 124509653271145653676432789)
              ·
                refine ⟨5836389997084952516082787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 124509653271145653676432789 5836389997084952516082787)
                ·
                  refine ⟨8754584995627428774124181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5836389997084952516082787 8754584995627428774124181)
                  ·
                    refine ⟨410371171670035723787071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8754584995627428774124181 410371171670035723787071)
                    ·
                      rfl

theorem cell23_2397585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_2397585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397585 prefixEnd_2397585 := by exact prefixLift 2397585
  have htrace : WordTrace (prefixWord ++ tailWord_2397585) baseStart_2397585 baseEnd_2397585 := by
    simpa [prefixWord, tailWord_2397585, baseEnd_2397585] using wordTrace_append hprefix tailTrace_2397585
  have hstable : (prefixWord ++ tailWord_2397585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397585).length < 2 ^ (prefixWord ++ tailWord_2397585).sum := by decide
  have hdescent : baseEnd_2397585 < baseStart_2397585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397595 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 3]
def baseStart_2397595 : Nat := 118140960795 + 2397595 * 2 ^ 59
def prefixEnd_2397595 : Nat := 4983230072969 + 3 ^ 40 * 2397595 * 2
def baseEnd_2397595 : Nat := 1231118649816652132236167

theorem tailTrace_2397595 : CollatzResearch.WordTrace tailWord_2397595 prefixEnd_2397595 1231118649816652132236167 := by
  unfold tailWord_2397595
  simp only [CollatzResearch.WordTrace]
  refine ⟨87447473748930266471010239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58298315832620177647340159 87447473748930266471010239)
  ·
    refine ⟨131171210623395399706515359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87447473748930266471010239 131171210623395399706515359)
    ·
      refine ⟨196756815935093099559773039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131171210623395399706515359 196756815935093099559773039)
      ·
        refine ⟨295135223902639649339659559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196756815935093099559773039 295135223902639649339659559)
        ·
          refine ⟨442702835853959474009489339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295135223902639649339659559 442702835853959474009489339)
          ·
            refine ⟨664054253780939211014234009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442702835853959474009489339 664054253780939211014234009)
            ·
              refine ⟨498040690335704408260675507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 664054253780939211014234009 498040690335704408260675507)
              ·
                refine ⟨747061035503556612391013261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498040690335704408260675507 747061035503556612391013261)
                ·
                  refine ⟨280147888313833729646629973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 747061035503556612391013261 280147888313833729646629973)
                  ·
                    refine ⟨3282983066177739019296445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 280147888313833729646629973 3282983066177739019296445)
                    ·
                      refine ⟨1231118649816652132236167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3282983066177739019296445 1231118649816652132236167)
                      ·
                        rfl

theorem cell23_2397595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 3].length) (baseStart_2397595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397595 prefixEnd_2397595 := by exact prefixLift 2397595
  have htrace : WordTrace (prefixWord ++ tailWord_2397595) baseStart_2397595 baseEnd_2397595 := by
    simpa [prefixWord, tailWord_2397595, baseEnd_2397595] using wordTrace_append hprefix tailTrace_2397595
  have hstable : (prefixWord ++ tailWord_2397595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397595).length < 2 ^ (prefixWord ++ tailWord_2397595).sum := by decide
  have hdescent : baseEnd_2397595 < baseStart_2397595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397605 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 1, 1, 6]
def baseStart_2397605 : Nat := 118140960795 + 2397605 * 2 ^ 59
def prefixEnd_2397605 : Nat := 4983230072969 + 3 ^ 40 * 2397605 * 2
def baseEnd_2397605 : Nat := 1231123784623197093111121

theorem tailTrace_2397605 : CollatzResearch.WordTrace tailWord_2397605 prefixEnd_2397605 1231123784623197093111121 := by
  unfold tailWord_2397605
  simp only [CollatzResearch.WordTrace]
  refine ⟨87447838478894038178874269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58298558985929358785916179 87447838478894038178874269)
  ·
    refine ⟨32792939429585264317077851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87447838478894038178874269 32792939429585264317077851)
    ·
      refine ⟨49189409144377896475616777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32792939429585264317077851 49189409144377896475616777)
      ·
        refine ⟨36892056858283422356712583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49189409144377896475616777 36892056858283422356712583)
        ·
          refine ⟨55338085287425133535068875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36892056858283422356712583 55338085287425133535068875)
          ·
            refine ⟨83007127931137700302603313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55338085287425133535068875 83007127931137700302603313)
            ·
              refine ⟨62255345948353275226952485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83007127931137700302603313 62255345948353275226952485)
              ·
                refine ⟨11672877365316239105053591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62255345948353275226952485 11672877365316239105053591)
                ·
                  refine ⟨17509316047974358657580387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11672877365316239105053591 17509316047974358657580387)
                  ·
                    refine ⟨26263974071961537986370581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17509316047974358657580387 26263974071961537986370581)
                    ·
                      refine ⟨1231123784623197093111121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26263974071961537986370581 1231123784623197093111121)
                      ·
                        rfl

theorem cell23_2397605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_2397605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397605 prefixEnd_2397605 := by exact prefixLift 2397605
  have htrace : WordTrace (prefixWord ++ tailWord_2397605) baseStart_2397605 baseEnd_2397605 := by
    simpa [prefixWord, tailWord_2397605, baseEnd_2397605] using wordTrace_append hprefix tailTrace_2397605
  have hstable : (prefixWord ++ tailWord_2397605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397605).length < 2 ^ (prefixWord ++ tailWord_2397605).sum := by decide
  have hdescent : baseEnd_2397605 < baseStart_2397605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397612 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 3]
def baseStart_2397612 : Nat := 118140960795 + 2397612 * 2 ^ 59
def prefixEnd_2397612 : Nat := 4983230072969 + 3 ^ 40 * 2397612 * 2
def baseEnd_2397612 : Nat := 1231127378987778565723589

theorem tailTrace_2397612 : CollatzResearch.WordTrace tailWord_2397612 prefixEnd_2397612 1231127378987778565723589 := by
  unfold tailWord_2397612
  simp only [CollatzResearch.WordTrace]
  refine ⟨43724046894934339187189545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58298729193245785582919393 43724046894934339187189545)
  ·
    refine ⟨32793035171200754390392159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43724046894934339187189545 32793035171200754390392159)
    ·
      refine ⟨49189552756801131585588239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32793035171200754390392159 49189552756801131585588239)
      ·
        refine ⟨73784329135201697378382359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49189552756801131585588239 73784329135201697378382359)
        ·
          refine ⟨110676493702802546067573539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73784329135201697378382359 110676493702802546067573539)
          ·
            refine ⟨166014740554203819101360309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110676493702802546067573539 166014740554203819101360309)
            ·
              refine ⟨15563881926956608040752529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 166014740554203819101360309 15563881926956608040752529)
              ·
                refine ⟨11672911445217456030564397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15563881926956608040752529 11672911445217456030564397)
                ·
                  refine ⟨4377341791956546011461649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11672911445217456030564397 4377341791956546011461649)
                  ·
                    refine ⟨3283006343967409508596237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4377341791956546011461649 3283006343967409508596237)
                    ·
                      refine ⟨1231127378987778565723589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3283006343967409508596237 1231127378987778565723589)
                      ·
                        rfl

theorem cell23_2397612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 3].length) (baseStart_2397612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397612 prefixEnd_2397612 := by exact prefixLift 2397612
  have htrace : WordTrace (prefixWord ++ tailWord_2397612) baseStart_2397612 baseEnd_2397612 := by
    simpa [prefixWord, tailWord_2397612, baseEnd_2397612] using wordTrace_append hprefix tailTrace_2397612
  have hstable : (prefixWord ++ tailWord_2397612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397612).length < 2 ^ (prefixWord ++ tailWord_2397612).sum := by decide
  have hdescent : baseEnd_2397612 < baseStart_2397612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397629 : List Nat := [1, 4, 1, 2, 2, 1, 2, 4, 1, 2, 3]
def baseStart_2397629 : Nat := 118140960795 + 2397629 * 2 ^ 59
def prefixEnd_2397629 : Nat := 4983230072969 + 3 ^ 40 * 2397629 * 2
def baseEnd_2397629 : Nat := 1231136108158904999211011

theorem tailTrace_2397629 : CollatzResearch.WordTrace tailWord_2397629 prefixEnd_2397629 1231136108158904999211011 := by
  unfold tailWord_2397629
  simp only [CollatzResearch.WordTrace]
  refine ⟨87448713830807090277747941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58299142553871393518498627 87448713830807090277747941)
  ·
    refine ⟨16396633843276329427077739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87448713830807090277747941 16396633843276329427077739)
    ·
      refine ⟨24594950764914494140616609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16396633843276329427077739 24594950764914494140616609)
      ·
        refine ⟨18446213073685870605462457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24594950764914494140616609 18446213073685870605462457)
        ·
          refine ⟨13834659805264402954096843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18446213073685870605462457 13834659805264402954096843)
          ·
            refine ⟨20751989707896604431145265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13834659805264402954096843 20751989707896604431145265)
            ·
              refine ⟨15563992280922453323358949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20751989707896604431145265 15563992280922453323358949)
              ·
                refine ⟨2918248552672959998129803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15563992280922453323358949 2918248552672959998129803)
                ·
                  refine ⟨4377372829009439997194705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2918248552672959998129803 4377372829009439997194705)
                  ·
                    refine ⟨3283029621757079997896029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4377372829009439997194705 3283029621757079997896029)
                    ·
                      refine ⟨1231136108158904999211011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3283029621757079997896029 1231136108158904999211011)
                      ·
                        rfl

theorem cell23_2397629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_2397629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397629 prefixEnd_2397629 := by exact prefixLift 2397629
  have htrace : WordTrace (prefixWord ++ tailWord_2397629) baseStart_2397629 baseEnd_2397629 := by
    simpa [prefixWord, tailWord_2397629, baseEnd_2397629] using wordTrace_append hprefix tailTrace_2397629
  have hstable : (prefixWord ++ tailWord_2397629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397629).length < 2 ^ (prefixWord ++ tailWord_2397629).sum := by decide
  have hdescent : baseEnd_2397629 < baseStart_2397629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397646 : List Nat := [4, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3]
def baseStart_2397646 : Nat := 118140960795 + 2397646 * 2 ^ 59
def prefixEnd_2397646 : Nat := 4983230072969 + 3 ^ 40 * 2397646 * 2
def baseEnd_2397646 : Nat := 1231144837330031432698433

theorem tailTrace_2397646 : CollatzResearch.WordTrace tailWord_2397646 prefixEnd_2397646 1231144837330031432698433 := by
  unfold tailWord_2397646
  simp only [CollatzResearch.WordTrace]
  refine ⟨10931166733968187772639599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58299555914497001454077861 10931166733968187772639599)
  ·
    refine ⟨16396750100952281658959399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10931166733968187772639599 16396750100952281658959399)
    ·
      refine ⟨24595125151428422488439099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16396750100952281658959399 24595125151428422488439099)
      ·
        refine ⟨36892687727142633732658649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24595125151428422488439099 36892687727142633732658649)
        ·
          refine ⟨27669515795356975299493987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36892687727142633732658649 27669515795356975299493987)
          ·
            refine ⟨41504273693035462949240981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27669515795356975299493987 41504273693035462949240981)
            ·
              refine ⟨1945512829361037325745671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41504273693035462949240981 1945512829361037325745671)
              ·
                refine ⟨2918269244041555988618507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1945512829361037325745671 2918269244041555988618507)
                ·
                  refine ⟨4377403866062333982927761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2918269244041555988618507 4377403866062333982927761)
                  ·
                    refine ⟨3283052899546750487195821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4377403866062333982927761 3283052899546750487195821)
                    ·
                      refine ⟨1231144837330031432698433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3283052899546750487195821 1231144837330031432698433)
                      ·
                        rfl

theorem cell23_2397646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3].length) (baseStart_2397646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397646 prefixEnd_2397646 := by exact prefixLift 2397646
  have htrace : WordTrace (prefixWord ++ tailWord_2397646) baseStart_2397646 baseEnd_2397646 := by
    simpa [prefixWord, tailWord_2397646, baseEnd_2397646] using wordTrace_append hprefix tailTrace_2397646
  have hstable : (prefixWord ++ tailWord_2397646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397646).length < 2 ^ (prefixWord ++ tailWord_2397646).sum := by decide
  have hdescent : baseEnd_2397646 < baseStart_2397646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397675 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 1, 8]
def baseStart_2397675 : Nat := 118140960795 + 2397675 * 2 ^ 59
def prefixEnd_2397675 : Nat := 4983230072969 + 3 ^ 40 * 2397675 * 2
def baseEnd_2397675 : Nat := 410386576089670606411933

theorem tailTrace_2397675 : CollatzResearch.WordTrace tailWord_2397675 prefixEnd_2397675 410386576089670606411933 := by
  unfold tailWord_2397675
  simp only [CollatzResearch.WordTrace]
  refine ⟨87450391588640440133922479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58300261059093626755948319 87450391588640440133922479)
  ·
    refine ⟨131175587382960660200883719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87450391588640440133922479 131175587382960660200883719)
    ·
      refine ⟨196763381074440990301325579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131175587382960660200883719 196763381074440990301325579)
      ·
        refine ⟨295145071611661485451988369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196763381074440990301325579 295145071611661485451988369)
        ·
          refine ⟨221358803708746114088991277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295145071611661485451988369 221358803708746114088991277)
          ·
            refine ⟨83009551390779792783371729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221358803708746114088991277 83009551390779792783371729)
            ·
              refine ⟨62257163543084844587528797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83009551390779792783371729 62257163543084844587528797)
              ·
                refine ⟨23346436328656816720323299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62257163543084844587528797 23346436328656816720323299)
                ·
                  refine ⟨35019654492985225080484949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23346436328656816720323299 35019654492985225080484949)
                  ·
                    refine ⟨410386576089670606411933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35019654492985225080484949 410386576089670606411933)
                    ·
                      rfl

theorem cell23_2397675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 8].length) (baseStart_2397675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397675 prefixEnd_2397675 := by exact prefixLift 2397675
  have htrace : WordTrace (prefixWord ++ tailWord_2397675) baseStart_2397675 baseEnd_2397675 := by
    simpa [prefixWord, tailWord_2397675, baseEnd_2397675] using wordTrace_append hprefix tailTrace_2397675
  have hstable : (prefixWord ++ tailWord_2397675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397675).length < 2 ^ (prefixWord ++ tailWord_2397675).sum := by decide
  have hdescent : baseEnd_2397675 < baseStart_2397675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397694 : List Nat := [4, 2, 2, 3, 1, 2, 1, 3, 1, 2, 2]
def baseStart_2397694 : Nat := 118140960795 + 2397694 * 2 ^ 59
def prefixEnd_2397694 : Nat := 4983230072969 + 3 ^ 40 * 2397694 * 2
def baseEnd_2397694 : Nat := 1231169484401447244898213

theorem tailTrace_2397694 : CollatzResearch.WordTrace tailWord_2397694 prefixEnd_2397694 1231169484401447244898213 := by
  unfold tailWord_2397694
  simp only [CollatzResearch.WordTrace]
  refine ⟨10931385571946450797358017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58300723050381070919242757 10931385571946450797358017)
  ·
    refine ⟨8198539178959838098018513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10931385571946450797358017 8198539178959838098018513)
    ·
      refine ⟨6148904384219878573513885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8198539178959838098018513 6148904384219878573513885)
      ·
        refine ⟨2305839144082454465067707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6148904384219878573513885 2305839144082454465067707)
        ·
          refine ⟨3458758716123681697601561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2305839144082454465067707 3458758716123681697601561)
          ·
            refine ⟨2594069037092761273201171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3458758716123681697601561 2594069037092761273201171)
            ·
              refine ⟨3891103555639141909801757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2594069037092761273201171 3891103555639141909801757)
              ·
                refine ⟨1459163833364678216175659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3891103555639141909801757 1459163833364678216175659)
                ·
                  refine ⟨2188745750047017324263489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1459163833364678216175659 2188745750047017324263489)
                  ·
                    refine ⟨1641559312535262993197617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2188745750047017324263489 1641559312535262993197617)
                    ·
                      refine ⟨1231169484401447244898213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1641559312535262993197617 1231169484401447244898213)
                      ·
                        rfl

theorem cell23_2397694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_2397694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397694 prefixEnd_2397694 := by exact prefixLift 2397694
  have htrace : WordTrace (prefixWord ++ tailWord_2397694) baseStart_2397694 baseEnd_2397694 := by
    simpa [prefixWord, tailWord_2397694, baseEnd_2397694] using wordTrace_append hprefix tailTrace_2397694
  have hstable : (prefixWord ++ tailWord_2397694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397694).length < 2 ^ (prefixWord ++ tailWord_2397694).sum := by decide
  have hdescent : baseEnd_2397694 < baseStart_2397694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397773 : List Nat := [1, 6, 1, 1, 3, 1, 1, 4, 5]
def baseStart_2397773 : Nat := 118140960795 + 2397773 * 2 ^ 59
def prefixEnd_2397773 : Nat := 4983230072969 + 3 ^ 40 * 2397773 * 2
def baseEnd_2397773 : Nat := 136801116597016937312261

theorem tailTrace_2397773 : CollatzResearch.WordTrace tailWord_2397773 prefixEnd_2397773 136801116597016937312261 := by
  unfold tailWord_2397773
  simp only [CollatzResearch.WordTrace]
  refine ⟨87453965942285402870989973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58302643961523601913993315 87453965942285402870989973)
  ·
    refine ⟨4099404653544628259577655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 87453965942285402870989973 4099404653544628259577655)
    ·
      refine ⟨6149106980316942389366483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4099404653544628259577655 6149106980316942389366483)
      ·
        refine ⟨9223660470475413584049725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6149106980316942389366483 9223660470475413584049725)
        ·
          refine ⟨3458872676428280094018647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9223660470475413584049725 3458872676428280094018647)
          ·
            refine ⟨5188309014642420141027971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3458872676428280094018647 5188309014642420141027971)
            ·
              refine ⟨7782463521963630211541957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5188309014642420141027971 7782463521963630211541957)
              ·
                refine ⟨1459211910368180664664117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7782463521963630211541957 1459211910368180664664117)
                ·
                  refine ⟨136801116597016937312261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1459211910368180664664117 136801116597016937312261)
                  ·
                    rfl

theorem cell23_2397773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_2397773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397773 prefixEnd_2397773 := by exact prefixLift 2397773
  have htrace : WordTrace (prefixWord ++ tailWord_2397773) baseStart_2397773 baseEnd_2397773 := by
    simpa [prefixWord, tailWord_2397773, baseEnd_2397773] using wordTrace_append hprefix tailTrace_2397773
  have hstable : (prefixWord ++ tailWord_2397773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397773).length < 2 ^ (prefixWord ++ tailWord_2397773).sum := by decide
  have hdescent : baseEnd_2397773 < baseStart_2397773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397799 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 5, 4]
def baseStart_2397799 : Nat := 118140960795 + 2397799 * 2 ^ 59
def prefixEnd_2397799 : Nat := 4983230072969 + 3 ^ 40 * 2397799 * 2
def baseEnd_2397799 : Nat := 410407799956723111361743

theorem tailTrace_2397799 : CollatzResearch.WordTrace tailWord_2397799 prefixEnd_2397799 410407799956723111361743 := by
  unfold tailWord_2397799
  simp only [CollatzResearch.WordTrace]
  refine ⟨87454914240191209311436451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58303276160127472874290967 87454914240191209311436451)
  ·
    refine ⟨131182371360286813967154677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87454914240191209311436451 131182371360286813967154677)
    ·
      refine ⟨12298347315026888809420751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131182371360286813967154677 12298347315026888809420751)
      ·
        refine ⟨18447520972540333214131127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12298347315026888809420751 18447520972540333214131127)
        ·
          refine ⟨27671281458810499821196691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18447520972540333214131127 27671281458810499821196691)
          ·
            refine ⟨41506922188215749731795037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27671281458810499821196691 41506922188215749731795037)
            ·
              refine ⟨15565095820580906149423139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41506922188215749731795037 15565095820580906149423139)
              ·
                refine ⟨23347643730871359224134709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15565095820580906149423139 23347643730871359224134709)
                ·
                  refine ⟨2188841599769189927262629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23347643730871359224134709 2188841599769189927262629)
                  ·
                    refine ⟨410407799956723111361743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2188841599769189927262629 410407799956723111361743)
                    ·
                      rfl

theorem cell23_2397799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_2397799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397799 prefixEnd_2397799 := by exact prefixLift 2397799
  have htrace : WordTrace (prefixWord ++ tailWord_2397799) baseStart_2397799 baseEnd_2397799 := by
    simpa [prefixWord, tailWord_2397799, baseEnd_2397799] using wordTrace_append hprefix tailTrace_2397799
  have hstable : (prefixWord ++ tailWord_2397799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397799).length < 2 ^ (prefixWord ++ tailWord_2397799).sum := by decide
  have hdescent : baseEnd_2397799 < baseStart_2397799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397806 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 1, 3, 4]
def baseStart_2397806 : Nat := 118140960795 + 2397806 * 2 ^ 59
def prefixEnd_2397806 : Nat := 4983230072969 + 3 ^ 40 * 2397806 * 2
def baseEnd_2397806 : Nat := 1231226994234750806697697

theorem tailTrace_2397806 : CollatzResearch.WordTrace tailWord_2397806 prefixEnd_2397806 1231226994234750806697697 := by
  unfold tailWord_2397806
  simp only [CollatzResearch.WordTrace]
  refine ⟨10931896193895731188367659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58303446367443899671294181 10931896193895731188367659)
  ·
    refine ⟨16397844290843596782551489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10931896193895731188367659 16397844290843596782551489)
    ·
      refine ⟨12298383218132697586913617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16397844290843596782551489 12298383218132697586913617)
      ·
        refine ⟨9223787413599523190185213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12298383218132697586913617 9223787413599523190185213)
        ·
          refine ⟨3458920280099821196319455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9223787413599523190185213 3458920280099821196319455)
          ·
            refine ⟨5188380420149731794479183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3458920280099821196319455 5188380420149731794479183)
            ·
              refine ⟨7782570630224597691718775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5188380420149731794479183 7782570630224597691718775)
              ·
                refine ⟨11673855945336896537578163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7782570630224597691718775 11673855945336896537578163)
                ·
                  refine ⟨17510783918005344806367245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11673855945336896537578163 17510783918005344806367245)
                  ·
                    refine ⟨6566543969252004302387717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17510783918005344806367245 6566543969252004302387717)
                    ·
                      refine ⟨1231226994234750806697697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6566543969252004302387717 1231226994234750806697697)
                      ·
                        rfl

theorem cell23_2397806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_2397806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397806 prefixEnd_2397806 := by exact prefixLift 2397806
  have htrace : WordTrace (prefixWord ++ tailWord_2397806) baseStart_2397806 baseEnd_2397806 := by
    simpa [prefixWord, tailWord_2397806, baseEnd_2397806] using wordTrace_append hprefix tailTrace_2397806
  have hstable : (prefixWord ++ tailWord_2397806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397806).length < 2 ^ (prefixWord ++ tailWord_2397806).sum := by decide
  have hdescent : baseEnd_2397806 < baseStart_2397806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397910 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_2397910 : Nat := 118140960795 + 2397910 * 2 ^ 59
def prefixEnd_2397910 : Nat := 4983230072969 + 3 ^ 40 * 2397910 * 2
def baseEnd_2397910 : Nat := 410426798740939466599073

theorem tailTrace_2397910 : CollatzResearch.WordTrace tailWord_2397910 prefixEnd_2397910 410426798740939466599073 := by
  unfold tailWord_2397910
  simp only [CollatzResearch.WordTrace]
  refine ⟨5466185171424317204295449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58305975161859383512484789 5466185171424317204295449)
  ·
    refine ⟨4099638878568237903221587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5466185171424317204295449 4099638878568237903221587)
    ·
      refine ⟨6149458317852356854832381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4099638878568237903221587 6149458317852356854832381)
      ·
        refine ⟨2306046869194633820562143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6149458317852356854832381 2306046869194633820562143)
        ·
          refine ⟨3459070303791950730843215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2306046869194633820562143 3459070303791950730843215)
          ·
            refine ⟨5188605455687926096264823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3459070303791950730843215 5188605455687926096264823)
            ·
              refine ⟨7782908183531889144397235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5188605455687926096264823 7782908183531889144397235)
              ·
                refine ⟨11674362275297833716595853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7782908183531889144397235 11674362275297833716595853)
                ·
                  refine ⟨4377885853236687643723445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11674362275297833716595853 4377885853236687643723445)
                  ·
                    refine ⟨410426798740939466599073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4377885853236687643723445 410426798740939466599073)
                    ·
                      rfl

theorem cell23_2397910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_2397910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397910 prefixEnd_2397910 := by exact prefixLift 2397910
  have htrace : WordTrace (prefixWord ++ tailWord_2397910) baseStart_2397910 baseEnd_2397910 := by
    simpa [prefixWord, tailWord_2397910, baseEnd_2397910] using wordTrace_append hprefix tailTrace_2397910
  have hstable : (prefixWord ++ tailWord_2397910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397910).length < 2 ^ (prefixWord ++ tailWord_2397910).sum := by decide
  have hdescent : baseEnd_2397910 < baseStart_2397910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397913 : List Nat := [1, 2, 1, 2, 3, 5, 1, 2, 1, 1, 4]
def baseStart_2397913 : Nat := 118140960795 + 2397913 * 2 ^ 59
def prefixEnd_2397913 : Nat := 4983230072969 + 3 ^ 40 * 2397913 * 2
def baseEnd_2397913 : Nat := 1231281936664781888059705

theorem tailTrace_2397913 : CollatzResearch.WordTrace tailWord_2397913 prefixEnd_2397913 1231281936664781888059705 := by
  unfold tailWord_2397913
  simp only [CollatzResearch.WordTrace]
  refine ⟨87459072161778206781086393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58306048107852137854057595 87459072161778206781086393)
  ·
    refine ⟨65594304121333655085814795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87459072161778206781086393 65594304121333655085814795)
    ·
      refine ⟨98391456182000482628722193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65594304121333655085814795 98391456182000482628722193)
      ·
        refine ⟨73793592136500361971541645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98391456182000482628722193 73793592136500361971541645)
        ·
          refine ⟨27672597051187635739328117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73793592136500361971541645 27672597051187635739328117)
          ·
            refine ⟨2594305973548840850562011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27672597051187635739328117 2594305973548840850562011)
            ·
              refine ⟨3891458960323261275843017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2594305973548840850562011 3891458960323261275843017)
              ·
                refine ⟨2918594220242445956882263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3891458960323261275843017 2918594220242445956882263)
                ·
                  refine ⟨4377891330363668935323395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2918594220242445956882263 4377891330363668935323395)
                  ·
                    refine ⟨6566836995545503402985093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4377891330363668935323395 6566836995545503402985093)
                    ·
                      refine ⟨1231281936664781888059705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6566836995545503402985093 1231281936664781888059705)
                      ·
                        rfl

theorem cell23_2397913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 1, 4].length) (baseStart_2397913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397913 prefixEnd_2397913 := by exact prefixLift 2397913
  have htrace : WordTrace (prefixWord ++ tailWord_2397913) baseStart_2397913 baseEnd_2397913 := by
    simpa [prefixWord, tailWord_2397913, baseEnd_2397913] using wordTrace_append hprefix tailTrace_2397913
  have hstable : (prefixWord ++ tailWord_2397913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397913).length < 2 ^ (prefixWord ++ tailWord_2397913).sum := by decide
  have hdescent : baseEnd_2397913 < baseStart_2397913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397917 : List Nat := [1, 4, 3, 3, 1, 1, 2, 1, 2, 3, 2]
def baseStart_2397917 : Nat := 118140960795 + 2397917 * 2 ^ 59
def prefixEnd_2397917 : Nat := 4983230072969 + 3 ^ 40 * 2397917 * 2
def baseEnd_2397917 : Nat := 1231283990587399872409687

theorem tailTrace_2397917 : CollatzResearch.WordTrace tailWord_2397917 prefixEnd_2397917 1231283990587399872409687 := by
  unfold tailWord_2397917
  simp only [CollatzResearch.WordTrace]
  refine ⟨87459218053763715464232005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58306145369175810309488003 87459218053763715464232005)
  ·
    refine ⟨16398603385080696649543501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87459218053763715464232005 16398603385080696649543501)
    ·
      refine ⟨6149476269405261243578813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16398603385080696649543501 6149476269405261243578813)
      ·
        refine ⟨2306053601026972966342055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6149476269405261243578813 2306053601026972966342055)
        ·
          refine ⟨3459080401540459449513083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2306053601026972966342055 3459080401540459449513083)
          ·
            refine ⟨5188620602310689174269625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3459080401540459449513083 5188620602310689174269625)
            ·
              refine ⟨3891465451733016880702219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5188620602310689174269625 3891465451733016880702219)
              ·
                refine ⟨5837198177599525321053329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3891465451733016880702219 5837198177599525321053329)
                ·
                  refine ⟨4377898633199643990789997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5837198177599525321053329 4377898633199643990789997)
                  ·
                    refine ⟨1641711987449866496546249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4377898633199643990789997 1641711987449866496546249)
                    ·
                      refine ⟨1231283990587399872409687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1641711987449866496546249 1231283990587399872409687)
                      ·
                        rfl

theorem cell23_2397917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_2397917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397917 prefixEnd_2397917 := by exact prefixLift 2397917
  have htrace : WordTrace (prefixWord ++ tailWord_2397917) baseStart_2397917 baseEnd_2397917 := by
    simpa [prefixWord, tailWord_2397917, baseEnd_2397917] using wordTrace_append hprefix tailTrace_2397917
  have hstable : (prefixWord ++ tailWord_2397917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397917).length < 2 ^ (prefixWord ++ tailWord_2397917).sum := by decide
  have hdescent : baseEnd_2397917 < baseStart_2397917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397933 : List Nat := [1, 5, 1, 2, 1, 4, 1, 1, 1, 1, 5]
def baseStart_2397933 : Nat := 118140960795 + 2397933 * 2 ^ 59
def prefixEnd_2397933 : Nat := 4983230072969 + 3 ^ 40 * 2397933 * 2
def baseEnd_2397933 : Nat := 1231292206277871809809613

theorem tailTrace_2397933 : CollatzResearch.WordTrace tailWord_2397933 prefixEnd_2397933 1231292206277871809809613 := by
  unfold tailWord_2397933
  simp only [CollatzResearch.WordTrace]
  refine ⟨87459801621705750196814453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58306534414470500131209635 87459801621705750196814453)
  ·
    refine ⟨8199356402034914080951355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87459801621705750196814453 8199356402034914080951355)
    ·
      refine ⟨12299034603052371121427033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8199356402034914080951355 12299034603052371121427033)
      ·
        refine ⟨9224275952289278341070275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12299034603052371121427033 9224275952289278341070275)
        ·
          refine ⟨13836413928433917511605413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9224275952289278341070275 13836413928433917511605413)
          ·
            refine ⟨2594327611581359533426015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13836413928433917511605413 2594327611581359533426015)
            ·
              refine ⟨3891491417372039300139023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2594327611581359533426015 3891491417372039300139023)
              ·
                refine ⟨5837237126058058950208535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3891491417372039300139023 5837237126058058950208535)
                ·
                  refine ⟨8755855689087088425312803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5837237126058058950208535 8755855689087088425312803)
                  ·
                    refine ⟨13133783533630632637969205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8755855689087088425312803 13133783533630632637969205)
                    ·
                      refine ⟨1231292206277871809809613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13133783533630632637969205 1231292206277871809809613)
                      ·
                        rfl

theorem cell23_2397933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_2397933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397933 prefixEnd_2397933 := by exact prefixLift 2397933
  have htrace : WordTrace (prefixWord ++ tailWord_2397933) baseStart_2397933 baseEnd_2397933 := by
    simpa [prefixWord, tailWord_2397933, baseEnd_2397933] using wordTrace_append hprefix tailTrace_2397933
  have hstable : (prefixWord ++ tailWord_2397933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397933).length < 2 ^ (prefixWord ++ tailWord_2397933).sum := by decide
  have hdescent : baseEnd_2397933 < baseStart_2397933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397963 : List Nat := [1, 1, 1, 1, 5, 1, 4, 3, 2, 1, 3]
def baseStart_2397963 : Nat := 118140960795 + 2397963 * 2 ^ 59
def prefixEnd_2397963 : Nat := 4983230072969 + 3 ^ 40 * 2397963 * 2
def baseEnd_2397963 : Nat := 1231307610697506692434475

theorem tailTrace_2397963 : CollatzResearch.WordTrace tailWord_2397963 prefixEnd_2397963 1231307610697506692434475 := by
  unfold tailWord_2397963
  simp only [CollatzResearch.WordTrace]
  refine ⟨87460895811597065320406543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58307263874398043546937695 87460895811597065320406543)
  ·
    refine ⟨131191343717395597980609815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87460895811597065320406543 131191343717395597980609815)
    ·
      refine ⟨196787015576093396970914723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131191343717395597980609815 196787015576093396970914723)
      ·
        refine ⟨295180523364140095456372085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196787015576093396970914723 295180523364140095456372085)
        ·
          refine ⟨27673174065388133949034883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 295180523364140095456372085 27673174065388133949034883)
          ·
            refine ⟨41509761098082200923552325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27673174065388133949034883 41509761098082200923552325)
            ·
              refine ⟨7783080205890412673166061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41509761098082200923552325 7783080205890412673166061)
              ·
                refine ⟨2918655077208904752437273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7783080205890412673166061 2918655077208904752437273)
                ·
                  refine ⟨2188991307906678564327955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2918655077208904752437273 2188991307906678564327955)
                  ·
                    refine ⟨3283486961860017846491933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2188991307906678564327955 3283486961860017846491933)
                    ·
                      refine ⟨1231307610697506692434475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3283486961860017846491933 1231307610697506692434475)
                      ·
                        rfl

theorem cell23_2397963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 1, 3].length) (baseStart_2397963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397963 prefixEnd_2397963 := by exact prefixLift 2397963
  have htrace : WordTrace (prefixWord ++ tailWord_2397963) baseStart_2397963 baseEnd_2397963 := by
    simpa [prefixWord, tailWord_2397963, baseEnd_2397963] using wordTrace_append hprefix tailTrace_2397963
  have hstable : (prefixWord ++ tailWord_2397963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397963).length < 2 ^ (prefixWord ++ tailWord_2397963).sum := by decide
  have hdescent : baseEnd_2397963 < baseStart_2397963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397969 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 4]
def baseStart_2397969 : Nat := 118140960795 + 2397969 * 2 ^ 59
def prefixEnd_2397969 : Nat := 4983230072969 + 3 ^ 40 * 2397969 * 2
def baseEnd_2397969 : Nat := 1231310691581433668959447

theorem tailTrace_2397969 : CollatzResearch.WordTrace tailWord_2397969 prefixEnd_2397969 1231310691581433668959447 := by
  unfold tailWord_2397969
  simp only [CollatzResearch.WordTrace]
  refine ⟨87461114649575328345124961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58307409766383552230083307 87461114649575328345124961)
  ·
    refine ⟨65595835987181496258843721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87461114649575328345124961 65595835987181496258843721)
    ·
      refine ⟨49196876990386122194132791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65595835987181496258843721 49196876990386122194132791)
      ·
        refine ⟨73795315485579183291199187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49196876990386122194132791 73795315485579183291199187)
        ·
          refine ⟨110692973228368774936798781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73795315485579183291199187 110692973228368774936798781)
          ·
            refine ⟨41509864960638290601299543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110692973228368774936798781 41509864960638290601299543)
            ·
              refine ⟨62264797440957435901949315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41509864960638290601299543 62264797440957435901949315)
              ·
                refine ⟨93397196161436153852923973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62264797440957435901949315 93397196161436153852923973)
                ·
                  refine ⟨17511974280269278847423245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93397196161436153852923973 17511974280269278847423245)
                  ·
                    refine ⟨6566990355100979567783717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17511974280269278847423245 6566990355100979567783717)
                    ·
                      refine ⟨1231310691581433668959447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6566990355100979567783717 1231310691581433668959447)
                      ·
                        rfl

theorem cell23_2397969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_2397969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397969 prefixEnd_2397969 := by exact prefixLift 2397969
  have htrace : WordTrace (prefixWord ++ tailWord_2397969) baseStart_2397969 baseEnd_2397969 := by
    simpa [prefixWord, tailWord_2397969, baseEnd_2397969] using wordTrace_append hprefix tailTrace_2397969
  have hstable : (prefixWord ++ tailWord_2397969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397969).length < 2 ^ (prefixWord ++ tailWord_2397969).sum := by decide
  have hdescent : baseEnd_2397969 < baseStart_2397969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397973 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 3, 3, 2]
def baseStart_2397973 : Nat := 118140960795 + 2397973 * 2 ^ 59
def prefixEnd_2397973 : Nat := 4983230072969 + 3 ^ 40 * 2397973 * 2
def baseEnd_2397973 : Nat := 1231312745504051653309429

theorem tailTrace_2397973 : CollatzResearch.WordTrace tailWord_2397973 prefixEnd_2397973 1231312745504051653309429 := by
  unfold tailWord_2397973
  simp only [CollatzResearch.WordTrace]
  refine ⟨87461260541560837028270573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58307507027707224685513715 87461260541560837028270573)
  ·
    refine ⟨32797972703085313885601465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87461260541560837028270573 32797972703085313885601465)
    ·
      refine ⟨24598479527313985414201099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32797972703085313885601465 24598479527313985414201099)
      ·
        refine ⟨36897719290970978121301649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24598479527313985414201099 36897719290970978121301649)
        ·
          refine ⟨27673289468228233590976237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36897719290970978121301649 27673289468228233590976237)
          ·
            refine ⟨10377483550585587596616089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27673289468228233590976237 10377483550585587596616089)
            ·
              refine ⟨7783112662939190697462067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10377483550585587596616089 7783112662939190697462067)
              ·
                refine ⟨11674668994408786046193101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7783112662939190697462067 11674668994408786046193101)
                ·
                  refine ⟨4378000872903294767322413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11674668994408786046193101 4378000872903294767322413)
                  ·
                    refine ⟨1641750327338735537745905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4378000872903294767322413 1641750327338735537745905)
                    ·
                      refine ⟨1231312745504051653309429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1641750327338735537745905 1231312745504051653309429)
                      ·
                        rfl

theorem cell23_2397973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 3, 2].length) (baseStart_2397973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397973 prefixEnd_2397973 := by exact prefixLift 2397973
  have htrace : WordTrace (prefixWord ++ tailWord_2397973) baseStart_2397973 baseEnd_2397973 := by
    simpa [prefixWord, tailWord_2397973, baseEnd_2397973] using wordTrace_append hprefix tailTrace_2397973
  have hstable : (prefixWord ++ tailWord_2397973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397973).length < 2 ^ (prefixWord ++ tailWord_2397973).sum := by decide
  have hdescent : baseEnd_2397973 < baseStart_2397973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397999 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 4]
def baseStart_2397999 : Nat := 118140960795 + 2397999 * 2 ^ 59
def prefixEnd_2397999 : Nat := 4983230072969 + 3 ^ 40 * 2397999 * 2
def baseEnd_2397999 : Nat := 1231326096001068551584309

theorem tailTrace_2397999 : CollatzResearch.WordTrace tailWord_2397999 prefixEnd_2397999 1231326096001068551584309 := by
  unfold tailWord_2397999
  simp only [CollatzResearch.WordTrace]
  refine ⟨87462208839466643468717051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58308139226311095645811367 87462208839466643468717051)
  ·
    refine ⟨131193313259199965203075577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87462208839466643468717051 131193313259199965203075577)
    ·
      refine ⟨98394984944399973902306683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131193313259199965203075577 98394984944399973902306683)
      ·
        refine ⟨147592477416599960853460025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98394984944399973902306683 147592477416599960853460025)
        ·
          refine ⟨110694358062449970640095019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147592477416599960853460025 110694358062449970640095019)
          ·
            refine ⟨166041537093674955960142529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110694358062449970640095019 166041537093674955960142529)
            ·
              refine ⟨124531152820256216970106897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166041537093674955960142529 124531152820256216970106897)
              ·
                refine ⟨93398364615192162727580173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124531152820256216970106897 93398364615192162727580173)
                ·
                  refine ⟨35024386730697061022842565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93398364615192162727580173 35024386730697061022842565)
                  ·
                    refine ⟨6567072512005698941782981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35024386730697061022842565 6567072512005698941782981)
                    ·
                      refine ⟨1231326096001068551584309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6567072512005698941782981 1231326096001068551584309)
                      ·
                        rfl

theorem cell23_2397999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 4].length) (baseStart_2397999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2397999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2397999 prefixEnd_2397999 := by exact prefixLift 2397999
  have htrace : WordTrace (prefixWord ++ tailWord_2397999) baseStart_2397999 baseEnd_2397999 := by
    simpa [prefixWord, tailWord_2397999, baseEnd_2397999] using wordTrace_append hprefix tailTrace_2397999
  have hstable : (prefixWord ++ tailWord_2397999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397999).length < 2 ^ (prefixWord ++ tailWord_2397999).sum := by decide
  have hdescent : baseEnd_2397999 < baseStart_2397999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398060 : List Nat := [2, 2, 1, 1, 4, 3, 3, 2, 5]
def baseStart_2398060 : Nat := 118140960795 + 2398060 * 2 ^ 59
def prefixEnd_2398060 : Nat := 4983230072969 + 3 ^ 40 * 2398060 * 2
def baseEnd_2398060 : Nat := 136817490924554756991281

theorem tailTrace_2398060 : CollatzResearch.WordTrace tailWord_2398060 prefixEnd_2398060 136817490924554756991281 := by
  unfold tailWord_2398060
  simp only [CollatzResearch.WordTrace]
  refine ⟨43732216846122825443343817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58309622461497100591125089 43732216846122825443343817)
  ·
    refine ⟨32799162634592119082507863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43732216846122825443343817 32799162634592119082507863)
    ·
      refine ⟨49198743951888178623761795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32799162634592119082507863 49198743951888178623761795)
      ·
        refine ⟨73798115927832267935642693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49198743951888178623761795 73798115927832267935642693)
        ·
          refine ⟨13837146736468550237933005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73798115927832267935642693 13837146736468550237933005)
          ·
            refine ⟨5188930026175706339224877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13837146736468550237933005 5188930026175706339224877)
            ·
              refine ⟨1945848759815889877209329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5188930026175706339224877 1945848759815889877209329)
              ·
                refine ⟨1459386569861917407906997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1945848759815889877209329 1459386569861917407906997)
                ·
                  refine ⟨136817490924554756991281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1459386569861917407906997 136817490924554756991281)
                  ·
                    rfl

theorem cell23_2398060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 5].length) (baseStart_2398060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398060 prefixEnd_2398060 := by exact prefixLift 2398060
  have htrace : WordTrace (prefixWord ++ tailWord_2398060) baseStart_2398060 baseEnd_2398060 := by
    simpa [prefixWord, tailWord_2398060, baseEnd_2398060] using wordTrace_append hprefix tailTrace_2398060
  have hstable : (prefixWord ++ tailWord_2398060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398060).length < 2 ^ (prefixWord ++ tailWord_2398060).sum := by decide
  have hdescent : baseEnd_2398060 < baseStart_2398060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398090 : List Nat := [3, 1, 2, 4, 2, 1, 2, 1, 2, 5]
def baseStart_2398090 : Nat := 118140960795 + 2398090 * 2 ^ 59
def prefixEnd_2398090 : Nat := 4983230072969 + 3 ^ 40 * 2398090 * 2
def baseEnd_2398090 : Nat := 410457607580209231848797

theorem tailTrace_2398090 : CollatzResearch.WordTrace tailWord_2398090 prefixEnd_2398090 410457607580209231848797 := by
  unfold tailWord_2398090
  simp only [CollatzResearch.WordTrace]
  refine ⟨21866381970534241502569931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58310351921424644006853149 21866381970534241502569931)
  ·
    refine ⟨32799572955801362253854897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21866381970534241502569931 32799572955801362253854897)
    ·
      refine ⟨24599679716851021690391173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32799572955801362253854897 24599679716851021690391173)
      ·
        refine ⟨4612439946909566566948345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24599679716851021690391173 4612439946909566566948345)
        ·
          refine ⟨3459329960182174925211259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4612439946909566566948345 3459329960182174925211259)
          ·
            refine ⟨5188994940273262387816889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3459329960182174925211259 5188994940273262387816889)
            ·
              refine ⟨3891746205204946790862667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5188994940273262387816889 3891746205204946790862667)
              ·
                refine ⟨5837619307807420186294001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3891746205204946790862667 5837619307807420186294001)
                ·
                  refine ⟨4378214480855565139720501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5837619307807420186294001 4378214480855565139720501)
                  ·
                    refine ⟨410457607580209231848797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4378214480855565139720501 410457607580209231848797)
                    ·
                      rfl

theorem cell23_2398090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_2398090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398090 prefixEnd_2398090 := by exact prefixLift 2398090
  have htrace : WordTrace (prefixWord ++ tailWord_2398090) baseStart_2398090 baseEnd_2398090 := by
    simpa [prefixWord, tailWord_2398090, baseEnd_2398090] using wordTrace_append hprefix tailTrace_2398090
  have hstable : (prefixWord ++ tailWord_2398090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398090).length < 2 ^ (prefixWord ++ tailWord_2398090).sum := by decide
  have hdescent : baseEnd_2398090 < baseStart_2398090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398133 : List Nat := [1, 3, 3, 2, 1, 2, 2, 3, 6]
def baseStart_2398133 : Nat := 118140960795 + 2398133 * 2 ^ 59
def prefixEnd_2398133 : Nat := 4983230072969 + 3 ^ 40 * 2398133 * 2
def baseEnd_2398133 : Nat := 136821655823196780812077

theorem tailTrace_2398133 : CollatzResearch.WordTrace tailWord_2398133 prefixEnd_2398133 136821655823196780812077 := by
  unfold tailWord_2398133
  simp only [CollatzResearch.WordTrace]
  refine ⟨87467096220981184354095053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58311397480654122902730035 87467096220981184354095053)
  ·
    refine ⟨32800161082867944132785645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87467096220981184354095053 32800161082867944132785645)
    ·
      refine ⟨12300060406075479049794617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32800161082867944132785645 12300060406075479049794617)
      ·
        refine ⟨9225045304556609287345963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12300060406075479049794617 9225045304556609287345963)
        ·
          refine ⟨13837567956834913931018945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9225045304556609287345963 13837567956834913931018945)
          ·
            refine ⟨10378175967626185448264209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13837567956834913931018945 10378175967626185448264209)
            ·
              refine ⟨7783631975719639086198157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10378175967626185448264209 7783631975719639086198157)
              ·
                refine ⟨2918861990894864657324309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7783631975719639086198157 2918861990894864657324309)
                ·
                  refine ⟨136821655823196780812077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2918861990894864657324309 136821655823196780812077)
                  ·
                    rfl

theorem cell23_2398133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 6].length) (baseStart_2398133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398133 prefixEnd_2398133 := by exact prefixLift 2398133
  have htrace : WordTrace (prefixWord ++ tailWord_2398133) baseStart_2398133 baseEnd_2398133 := by
    simpa [prefixWord, tailWord_2398133, baseEnd_2398133] using wordTrace_append hprefix tailTrace_2398133
  have hstable : (prefixWord ++ tailWord_2398133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398133).length < 2 ^ (prefixWord ++ tailWord_2398133).sum := by decide
  have hdescent : baseEnd_2398133 < baseStart_2398133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398153 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 1, 5, 2]
def baseStart_2398153 : Nat := 118140960795 + 2398153 * 2 ^ 59
def prefixEnd_2398153 : Nat := 4983230072969 + 3 ^ 40 * 2398153 * 2
def baseEnd_2398153 : Nat := 1231405172021860949058601

theorem tailTrace_2398153 : CollatzResearch.WordTrace tailWord_2398153 prefixEnd_2398153 1231405172021860949058601 := by
  unfold tailWord_2398153
  simp only [CollatzResearch.WordTrace]
  refine ⟨87467825680908727769823113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58311883787272485179882075 87467825680908727769823113)
  ·
    refine ⟨65600869260681545827367335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87467825680908727769823113 65600869260681545827367335)
    ·
      refine ⟨98401303891022318741051003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65600869260681545827367335 98401303891022318741051003)
      ·
        refine ⟨147601955836533478111576505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98401303891022318741051003 147601955836533478111576505)
        ·
          refine ⟨110701466877400108583682379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147601955836533478111576505 110701466877400108583682379)
          ·
            refine ⟨166052200316100162875523569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110701466877400108583682379 166052200316100162875523569)
            ·
              refine ⟨124539150237075122156642677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166052200316100162875523569 124539150237075122156642677)
              ·
                refine ⟨11675545334725792702185251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 124539150237075122156642677 11675545334725792702185251)
                ·
                  refine ⟨17513318002088689053277877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11675545334725792702185251 17513318002088689053277877)
                  ·
                    refine ⟨1641873562695814598744801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17513318002088689053277877 1641873562695814598744801)
                    ·
                      refine ⟨1231405172021860949058601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1641873562695814598744801 1231405172021860949058601)
                      ·
                        rfl

theorem cell23_2398153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 5, 2].length) (baseStart_2398153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398153 prefixEnd_2398153 := by exact prefixLift 2398153
  have htrace : WordTrace (prefixWord ++ tailWord_2398153) baseStart_2398153 baseEnd_2398153 := by
    simpa [prefixWord, tailWord_2398153, baseEnd_2398153] using wordTrace_append hprefix tailTrace_2398153
  have hstable : (prefixWord ++ tailWord_2398153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398153).length < 2 ^ (prefixWord ++ tailWord_2398153).sum := by decide
  have hdescent : baseEnd_2398153 < baseStart_2398153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398176 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 3, 6]
def baseStart_2398176 : Nat := 118140960795 + 2398176 * 2 ^ 59
def prefixEnd_2398176 : Nat := 4983230072969 + 3 ^ 40 * 2398176 * 2
def baseEnd_2398176 : Nat := 410472327358971453023665

theorem tailTrace_2398176 : CollatzResearch.WordTrace tailWord_2398176 prefixEnd_2398176 410472327358971453023665 := by
  unfold tailWord_2398176
  simp only [CollatzResearch.WordTrace]
  refine ⟨43734332279912701348955191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58312443039883601798606921 43734332279912701348955191)
  ·
    refine ⟨65601498419869052023432787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43734332279912701348955191 65601498419869052023432787)
    ·
      refine ⟨98402247629803578035149181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65601498419869052023432787 98402247629803578035149181)
      ·
        refine ⟨36900842861176341763180943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98402247629803578035149181 36900842861176341763180943)
        ·
          refine ⟨55351264291764512644771415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36900842861176341763180943 55351264291764512644771415)
          ·
            refine ⟨83026896437646768967157123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55351264291764512644771415 83026896437646768967157123)
            ·
              refine ⟨124540344656470153450735685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83026896437646768967157123 124540344656470153450735685)
              ·
                refine ⟨23351314623088153772012941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124540344656470153450735685 23351314623088153772012941)
                ·
                  refine ⟨8756742983658057664504853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23351314623088153772012941 8756742983658057664504853)
                  ·
                    refine ⟨410472327358971453023665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8756742983658057664504853 410472327358971453023665)
                    ·
                      rfl

theorem cell23_2398176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 3, 6].length) (baseStart_2398176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398176 prefixEnd_2398176 := by exact prefixLift 2398176
  have htrace : WordTrace (prefixWord ++ tailWord_2398176) baseStart_2398176 baseEnd_2398176 := by
    simpa [prefixWord, tailWord_2398176, baseEnd_2398176] using wordTrace_append hprefix tailTrace_2398176
  have hstable : (prefixWord ++ tailWord_2398176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398176).length < 2 ^ (prefixWord ++ tailWord_2398176).sum := by decide
  have hdescent : baseEnd_2398176 < baseStart_2398176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398177 : List Nat := [1, 2, 3, 1, 2, 1, 4, 4, 1, 1, 3]
def baseStart_2398177 : Nat := 118140960795 + 2398177 * 2 ^ 59
def prefixEnd_2398177 : Nat := 4983230072969 + 3 ^ 40 * 2398177 * 2
def baseEnd_2398177 : Nat := 1231417495557568855158491

theorem tailTrace_2398177 : CollatzResearch.WordTrace tailWord_2398177 prefixEnd_2398177 1231417495557568855158491 := by
  unfold tailWord_2398177
  simp only [CollatzResearch.WordTrace]
  refine ⟨87468701032821779868696785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58312467355214519912464523 87468701032821779868696785)
  ·
    refine ⟨65601525774616334901522589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87468701032821779868696785 65601525774616334901522589)
    ·
      refine ⟨24600572165481125588070971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65601525774616334901522589 24600572165481125588070971)
      ·
        refine ⟨36900858248221688382106457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24600572165481125588070971 36900858248221688382106457)
        ·
          refine ⟨27675643686166266286579843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36900858248221688382106457 27675643686166266286579843)
          ·
            refine ⟨41513465529249399429869765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27675643686166266286579843 41513465529249399429869765)
            ·
              refine ⟨7783774786734262393100581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41513465529249399429869765 7783774786734262393100581)
              ·
                refine ⟨1459457772512674198706359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7783774786734262393100581 1459457772512674198706359)
                ·
                  refine ⟨2189186658769011298059539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1459457772512674198706359 2189186658769011298059539)
                  ·
                    refine ⟨3283779988153516947089309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2189186658769011298059539 3283779988153516947089309)
                    ·
                      refine ⟨1231417495557568855158491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3283779988153516947089309 1231417495557568855158491)
                      ·
                        rfl

theorem cell23_2398177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 1, 1, 3].length) (baseStart_2398177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398177 prefixEnd_2398177 := by exact prefixLift 2398177
  have htrace : WordTrace (prefixWord ++ tailWord_2398177) baseStart_2398177 baseEnd_2398177 := by
    simpa [prefixWord, tailWord_2398177, baseEnd_2398177] using wordTrace_append hprefix tailTrace_2398177
  have hstable : (prefixWord ++ tailWord_2398177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398177).length < 2 ^ (prefixWord ++ tailWord_2398177).sum := by decide
  have hdescent : baseEnd_2398177 < baseStart_2398177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398203 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 3]
def baseStart_2398203 : Nat := 118140960795 + 2398203 * 2 ^ 59
def prefixEnd_2398203 : Nat := 4983230072969 + 3 ^ 40 * 2398203 * 2
def baseEnd_2398203 : Nat := 1231430846054585753433371

theorem tailTrace_2398203 : CollatzResearch.WordTrace tailWord_2398203 prefixEnd_2398203 1231430846054585753433371 := by
  unfold tailWord_2398203
  simp only [CollatzResearch.WordTrace]
  refine ⟨87469649330727586309143263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58313099553818390872762175 87469649330727586309143263)
  ·
    refine ⟨131204473996091379463714895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87469649330727586309143263 131204473996091379463714895)
    ·
      refine ⟨196806710994137069195572343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131204473996091379463714895 196806710994137069195572343)
      ·
        refine ⟨295210066491205603793358515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196806710994137069195572343 295210066491205603793358515)
        ·
          refine ⟨442815099736808405690037773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295210066491205603793358515 442815099736808405690037773)
          ·
            refine ⟨166055662401303152133764165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 442815099736808405690037773 166055662401303152133764165)
            ·
              refine ⟨31135436700244341025080781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 166055662401303152133764165 31135436700244341025080781)
              ·
                refine ⟨11675788762591627884405293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31135436700244341025080781 11675788762591627884405293)
                ·
                  refine ⟨4378420785971860456651985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11675788762591627884405293 4378420785971860456651985)
                  ·
                    refine ⟨3283815589478895342488989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4378420785971860456651985 3283815589478895342488989)
                    ·
                      refine ⟨1231430846054585753433371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3283815589478895342488989 1231430846054585753433371)
                      ·
                        rfl

theorem cell23_2398203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 3].length) (baseStart_2398203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398203 prefixEnd_2398203 := by exact prefixLift 2398203
  have htrace : WordTrace (prefixWord ++ tailWord_2398203) baseStart_2398203 baseEnd_2398203 := by
    simpa [prefixWord, tailWord_2398203, baseEnd_2398203] using wordTrace_append hprefix tailTrace_2398203
  have hstable : (prefixWord ++ tailWord_2398203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398203).length < 2 ^ (prefixWord ++ tailWord_2398203).sum := by decide
  have hdescent : baseEnd_2398203 < baseStart_2398203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398220 : List Nat := [2, 2, 1, 2, 3, 1, 1, 5, 1, 2, 3]
def baseStart_2398220 : Nat := 118140960795 + 2398220 * 2 ^ 59
def prefixEnd_2398220 : Nat := 4983230072969 + 3 ^ 40 * 2398220 * 2
def baseEnd_2398220 : Nat := 1231439575225712186920793

theorem tailTrace_2398220 : CollatzResearch.WordTrace tailWord_2398220 prefixEnd_2398220 1231439575225712186920793 := by
  unfold tailWord_2398220
  simp only [CollatzResearch.WordTrace]
  refine ⟨43735134685832999106256057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58313512914443998808341409 43735134685832999106256057)
  ·
    refine ⟨32801351014374749329692043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43735134685832999106256057 32801351014374749329692043)
    ·
      refine ⟨49202026521562123994538065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32801351014374749329692043 49202026521562123994538065)
      ·
        refine ⟨36901519891171592995903549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49202026521562123994538065 36901519891171592995903549)
        ·
          refine ⟨13838069959189347373463831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36901519891171592995903549 13838069959189347373463831)
          ·
            refine ⟨20757104938784021060195747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13838069959189347373463831 20757104938784021060195747)
            ·
              refine ⟨31135657408176031590293621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20757104938784021060195747 31135657408176031590293621)
              ·
                refine ⟨2918967882016502961590027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31135657408176031590293621 2918967882016502961590027)
                ·
                  refine ⟨4378451823024754442385041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2918967882016502961590027 4378451823024754442385041)
                  ·
                    refine ⟨3283838867268565831788781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4378451823024754442385041 3283838867268565831788781)
                    ·
                      refine ⟨1231439575225712186920793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3283838867268565831788781 1231439575225712186920793)
                      ·
                        rfl

theorem cell23_2398220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_2398220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398220 prefixEnd_2398220 := by exact prefixLift 2398220
  have htrace : WordTrace (prefixWord ++ tailWord_2398220) baseStart_2398220 baseEnd_2398220 := by
    simpa [prefixWord, tailWord_2398220, baseEnd_2398220] using wordTrace_append hprefix tailTrace_2398220
  have hstable : (prefixWord ++ tailWord_2398220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398220).length < 2 ^ (prefixWord ++ tailWord_2398220).sum := by decide
  have hdescent : baseEnd_2398220 < baseStart_2398220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398228 : List Nat := [2, 4, 3, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_2398228 : Nat := 118140960795 + 2398228 * 2 ^ 59
def prefixEnd_2398228 : Nat := 4983230072969 + 3 ^ 40 * 2398228 * 2
def baseEnd_2398228 : Nat := 1231443683070948155620757

theorem tailTrace_2398228 : CollatzResearch.WordTrace tailWord_2398228 prefixEnd_2398228 1231443683070948155620757 := by
  unfold tailWord_2398228
  simp only [CollatzResearch.WordTrace]
  refine ⟨43735280577818507789401669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58313707437091343719202225 43735280577818507789401669)
  ·
    refine ⟨8200365108340970210512813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43735280577818507789401669 8200365108340970210512813)
    ·
      refine ⟨3075136915627863828942305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8200365108340970210512813 3075136915627863828942305)
      ·
        refine ⟨2306352686720897871706729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3075136915627863828942305 2306352686720897871706729)
        ·
          refine ⟨1729764515040673403780047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2306352686720897871706729 1729764515040673403780047)
          ·
            refine ⟨2594646772561010105670071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1729764515040673403780047 2594646772561010105670071)
            ·
              refine ⟨3891970158841515158505107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2594646772561010105670071 3891970158841515158505107)
              ·
                refine ⟨5837955238262272737757661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3891970158841515158505107 5837955238262272737757661)
                ·
                  refine ⟨2189233214348352276659123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5837955238262272737757661 2189233214348352276659123)
                  ·
                    refine ⟨3283849821522528414988685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2189233214348352276659123 3283849821522528414988685)
                    ·
                      refine ⟨1231443683070948155620757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3283849821522528414988685 1231443683070948155620757)
                      ·
                        rfl

theorem cell23_2398228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_2398228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398228 prefixEnd_2398228 := by exact prefixLift 2398228
  have htrace : WordTrace (prefixWord ++ tailWord_2398228) baseStart_2398228 baseEnd_2398228 := by
    simpa [prefixWord, tailWord_2398228, baseEnd_2398228] using wordTrace_append hprefix tailTrace_2398228
  have hstable : (prefixWord ++ tailWord_2398228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398228).length < 2 ^ (prefixWord ++ tailWord_2398228).sum := by decide
  have hdescent : baseEnd_2398228 < baseStart_2398228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398234 : List Nat := [3, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2]
def baseStart_2398234 : Nat := 118140960795 + 2398234 * 2 ^ 59
def prefixEnd_2398234 : Nat := 4983230072969 + 3 ^ 40 * 2398234 * 2
def baseEnd_2398234 : Nat := 1231446763954875132145729

theorem tailTrace_2398234 : CollatzResearch.WordTrace tailWord_2398234 prefixEnd_2398234 1231446763954875132145729 := by
  unfold tailWord_2398234
  simp only [CollatzResearch.WordTrace]
  refine ⟨21867694998403819650880439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58313853329076852402347837 21867694998403819650880439)
  ·
    refine ⟨32801542497605729476320659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21867694998403819650880439 32801542497605729476320659)
    ·
      refine ⟨49202313746408594214480989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32801542497605729476320659 49202313746408594214480989)
      ·
        refine ⟨18450867654903222830430371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49202313746408594214480989 18450867654903222830430371)
        ·
          refine ⟨27676301482354834245645557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18450867654903222830430371 27676301482354834245645557)
          ·
            refine ⟨2594653263970765710529271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27676301482354834245645557 2594653263970765710529271)
            ·
              refine ⟨3891979895956148565793907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2594653263970765710529271 3891979895956148565793907)
              ·
                refine ⟨5837969843934222848690861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3891979895956148565793907 5837969843934222848690861)
                ·
                  refine ⟨2189238691475333568259073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5837969843934222848690861 2189238691475333568259073)
                  ·
                    refine ⟨1641929018606500176194305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2189238691475333568259073 1641929018606500176194305)
                    ·
                      refine ⟨1231446763954875132145729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1641929018606500176194305 1231446763954875132145729)
                      ·
                        rfl

theorem cell23_2398234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_2398234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398234 prefixEnd_2398234 := by exact prefixLift 2398234
  have htrace : WordTrace (prefixWord ++ tailWord_2398234) baseStart_2398234 baseEnd_2398234 := by
    simpa [prefixWord, tailWord_2398234, baseEnd_2398234] using wordTrace_append hprefix tailTrace_2398234
  have hstable : (prefixWord ++ tailWord_2398234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398234).length < 2 ^ (prefixWord ++ tailWord_2398234).sum := by decide
  have hdescent : baseEnd_2398234 < baseStart_2398234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398254 : List Nat := [4, 1, 3, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_2398254 : Nat := 118140960795 + 2398254 * 2 ^ 59
def prefixEnd_2398254 : Nat := 4983230072969 + 3 ^ 40 * 2398254 * 2
def baseEnd_2398254 : Nat := 1231457033567965053895637

theorem tailTrace_2398254 : CollatzResearch.WordTrace tailWord_2398254 prefixEnd_2398254 1231457033567965053895637 := by
  unfold tailWord_2398254
  simp only [CollatzResearch.WordTrace]
  refine ⟨10933938681692852752406227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58314339635695214679499877 10933938681692852752406227)
  ·
    refine ⟨16400908022539279128609341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10933938681692852752406227 16400908022539279128609341)
    ·
      refine ⟨6150340508452229673228503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16400908022539279128609341 6150340508452229673228503)
      ·
        refine ⟨9225510762678344509842755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6150340508452229673228503 9225510762678344509842755)
        ·
          refine ⟨13838266144017516764764133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9225510762678344509842755 13838266144017516764764133)
          ·
            refine ⟨2594674902003284393393275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13838266144017516764764133 2594674902003284393393275)
            ·
              refine ⟨3892012353004926590089913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2594674902003284393393275 3892012353004926590089913)
              ·
                refine ⟨2919009264753694942567435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3892012353004926590089913 2919009264753694942567435)
                ·
                  refine ⟨4378513897130542413851153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2919009264753694942567435 4378513897130542413851153)
                  ·
                    refine ⟨3283885422847906810388365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4378513897130542413851153 3283885422847906810388365)
                    ·
                      refine ⟨1231457033567965053895637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3283885422847906810388365 1231457033567965053895637)
                      ·
                        rfl

theorem cell23_2398254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_2398254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398254 prefixEnd_2398254 := by exact prefixLift 2398254
  have htrace : WordTrace (prefixWord ++ tailWord_2398254) baseStart_2398254 baseEnd_2398254 := by
    simpa [prefixWord, tailWord_2398254, baseEnd_2398254] using wordTrace_append hprefix tailTrace_2398254
  have hstable : (prefixWord ++ tailWord_2398254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398254).length < 2 ^ (prefixWord ++ tailWord_2398254).sum := by decide
  have hdescent : baseEnd_2398254 < baseStart_2398254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398300 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 2, 6]
def baseStart_2398300 : Nat := 118140960795 + 2398300 * 2 ^ 59
def prefixEnd_2398300 : Nat := 4983230072969 + 3 ^ 40 * 2398300 * 2
def baseEnd_2398300 : Nat := 410493551226023957973475

theorem tailTrace_2398300 : CollatzResearch.WordTrace tailWord_2398300 prefixEnd_2398300 410493551226023957973475 := by
  unfold tailWord_2398300
  simp only [CollatzResearch.WordTrace]
  refine ⟨43736593605688085937712177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58315458140917447916949569 43736593605688085937712177)
  ·
    refine ⟨32802445204266064453284133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43736593605688085937712177 32802445204266064453284133)
    ·
      refine ⟨6150458475799887084990775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32802445204266064453284133 6150458475799887084990775)
      ·
        refine ⟨9225687713699830627486163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6150458475799887084990775 9225687713699830627486163)
        ·
          refine ⟨13838531570549745941229245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9225687713699830627486163 13838531570549745941229245)
          ·
            refine ⟨5189449338956154727960967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13838531570549745941229245 5189449338956154727960967)
            ·
              refine ⟨7784174008434232091941451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5189449338956154727960967 7784174008434232091941451)
              ·
                refine ⟨11676261012651348137912177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7784174008434232091941451 11676261012651348137912177)
                ·
                  refine ⟨8757195759488511103434133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11676261012651348137912177 8757195759488511103434133)
                  ·
                    refine ⟨410493551226023957973475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8757195759488511103434133 410493551226023957973475)
                    ·
                      rfl

theorem cell23_2398300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_2398300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398300 prefixEnd_2398300 := by exact prefixLift 2398300
  have htrace : WordTrace (prefixWord ++ tailWord_2398300) baseStart_2398300 baseEnd_2398300 := by
    simpa [prefixWord, tailWord_2398300, baseEnd_2398300] using wordTrace_append hprefix tailTrace_2398300
  have hstable : (prefixWord ++ tailWord_2398300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398300).length < 2 ^ (prefixWord ++ tailWord_2398300).sum := by decide
  have hdescent : baseEnd_2398300 < baseStart_2398300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398313 : List Nat := [1, 2, 1, 1, 1, 5, 3, 2, 7]
def baseStart_2398313 : Nat := 118140960795 + 2398313 * 2 ^ 59
def prefixEnd_2398313 : Nat := 4983230072969 + 3 ^ 40 * 2398313 * 2
def baseEnd_2398313 : Nat := 136831925436286702561985

theorem tailTrace_2398313 : CollatzResearch.WordTrace tailWord_2398313 prefixEnd_2398313 136831925436286702561985 := by
  unfold tailWord_2398313
  simp only [CollatzResearch.WordTrace]
  refine ⟨87473661360329075095647593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58315774240219383397098395 87473661360329075095647593)
  ·
    refine ⟨65605246020246806321735695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87473661360329075095647593 65605246020246806321735695)
    ·
      refine ⟨98407869030370209482603543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65605246020246806321735695 98407869030370209482603543)
      ·
        refine ⟨147611803545555314223905315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98407869030370209482603543 147611803545555314223905315)
        ·
          refine ⟨221417705318332971335857973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147611803545555314223905315 221417705318332971335857973)
          ·
            refine ⟨20757909873593716062736685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 221417705318332971335857973 20757909873593716062736685)
            ·
              refine ⟨7784216202597643523526257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20757909873593716062736685 7784216202597643523526257)
              ·
                refine ⟨5838162151948232642644693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7784216202597643523526257 5838162151948232642644693)
                ·
                  refine ⟨136831925436286702561985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5838162151948232642644693 136831925436286702561985)
                  ·
                    rfl

theorem cell23_2398313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 7].length) (baseStart_2398313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398313 prefixEnd_2398313 := by exact prefixLift 2398313
  have htrace : WordTrace (prefixWord ++ tailWord_2398313) baseStart_2398313 baseEnd_2398313 := by
    simpa [prefixWord, tailWord_2398313, baseEnd_2398313] using wordTrace_append hprefix tailTrace_2398313
  have hstable : (prefixWord ++ tailWord_2398313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398313).length < 2 ^ (prefixWord ++ tailWord_2398313).sum := by decide
  have hdescent : baseEnd_2398313 < baseStart_2398313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398340 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 4, 3, 3]
def baseStart_2398340 : Nat := 118140960795 + 2398340 * 2 ^ 59
def prefixEnd_2398340 : Nat := 4983230072969 + 3 ^ 40 * 2398340 * 2
def baseEnd_2398340 : Nat := 1231501192904251717420241

theorem tailTrace_2398340 : CollatzResearch.WordTrace tailWord_2398340 prefixEnd_2398340 1231501192904251717420241 := by
  unfold tailWord_2398340
  simp only [CollatzResearch.WordTrace]
  refine ⟨43737323065615629353440237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58316430754154172471253649 43737323065615629353440237)
  ·
    refine ⟨16401496149605861007540089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43737323065615629353440237 16401496149605861007540089)
    ·
      refine ⟨12301122112204395755655067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16401496149605861007540089 12301122112204395755655067)
      ·
        refine ⟨18451683168306593633482601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12301122112204395755655067 18451683168306593633482601)
        ·
          refine ⟨13838762376229945225111951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18451683168306593633482601 13838762376229945225111951)
          ·
            refine ⟨20758143564344917837667927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13838762376229945225111951 20758143564344917837667927)
            ·
              refine ⟨31137215346517376756501891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20758143564344917837667927 31137215346517376756501891)
              ·
                refine ⟨46705823019776065134752837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31137215346517376756501891 46705823019776065134752837)
                ·
                  refine ⟨8757341816208012212766157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46705823019776065134752837 8757341816208012212766157)
                  ·
                    refine ⟨3284003181078004579787309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8757341816208012212766157 3284003181078004579787309)
                    ·
                      refine ⟨1231501192904251717420241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3284003181078004579787309 1231501192904251717420241)
                      ·
                        rfl

theorem cell23_2398340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_2398340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398340 prefixEnd_2398340 := by exact prefixLift 2398340
  have htrace : WordTrace (prefixWord ++ tailWord_2398340) baseStart_2398340 baseEnd_2398340 := by
    simpa [prefixWord, tailWord_2398340, baseEnd_2398340] using wordTrace_append hprefix tailTrace_2398340
  have hstable : (prefixWord ++ tailWord_2398340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398340).length < 2 ^ (prefixWord ++ tailWord_2398340).sum := by decide
  have hdescent : baseEnd_2398340 < baseStart_2398340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398341 : List Nat := [1, 3, 1, 1, 5, 3, 1, 2, 2, 2, 2]
def baseStart_2398341 : Nat := 118140960795 + 2398341 * 2 ^ 59
def prefixEnd_2398341 : Nat := 4983230072969 + 3 ^ 40 * 2398341 * 2
def baseEnd_2398341 : Nat := 1231501706384906213507737

theorem tailTrace_2398341 : CollatzResearch.WordTrace tailWord_2398341 prefixEnd_2398341 1231501706384906213507737 := by
  unfold tailWord_2398341
  simp only [CollatzResearch.WordTrace]
  refine ⟨87474682604227635877666877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58316455069485090585111251 87474682604227635877666877)
  ·
    refine ⟨32803005976585363454125079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87474682604227635877666877 32803005976585363454125079)
    ·
      refine ⟨49204508964878045181187619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32803005976585363454125079 49204508964878045181187619)
      ·
        refine ⟨73806763447317067771781429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49204508964878045181187619 73806763447317067771781429)
        ·
          refine ⟨6919384073185975103604509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73806763447317067771781429 6919384073185975103604509)
          ·
            refine ⟨2594769027444740663851691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6919384073185975103604509 2594769027444740663851691)
            ·
              refine ⟨3892153541167110995777537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2594769027444740663851691 3892153541167110995777537)
              ·
                refine ⟨2919115155875333246833153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3892153541167110995777537 2919115155875333246833153)
                ·
                  refine ⟨2189336366906499935124865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2919115155875333246833153 2189336366906499935124865)
                  ·
                    refine ⟨1642002275179874951343649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2189336366906499935124865 1642002275179874951343649)
                    ·
                      refine ⟨1231501706384906213507737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1642002275179874951343649 1231501706384906213507737)
                      ·
                        rfl

theorem cell23_2398341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 2, 2].length) (baseStart_2398341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398341 prefixEnd_2398341 := by exact prefixLift 2398341
  have htrace : WordTrace (prefixWord ++ tailWord_2398341) baseStart_2398341 baseEnd_2398341 := by
    simpa [prefixWord, tailWord_2398341, baseEnd_2398341] using wordTrace_append hprefix tailTrace_2398341
  have hstable : (prefixWord ++ tailWord_2398341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398341).length < 2 ^ (prefixWord ++ tailWord_2398341).sum := by decide
  have hdescent : baseEnd_2398341 < baseStart_2398341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398363 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 4]
def baseStart_2398363 : Nat := 118140960795 + 2398363 * 2 ^ 59
def prefixEnd_2398363 : Nat := 4983230072969 + 3 ^ 40 * 2398363 * 2
def baseEnd_2398363 : Nat := 1231513002959305127432635

theorem tailTrace_2398363 : CollatzResearch.WordTrace tailWord_2398363 prefixEnd_2398363 1231513002959305127432635 := by
  unfold tailWord_2398363
  simp only [CollatzResearch.WordTrace]
  refine ⟨87475485010147933634967743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58316990006765289089978495 87475485010147933634967743)
  ·
    refine ⟨131213227515221900452451615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87475485010147933634967743 131213227515221900452451615)
    ·
      refine ⟨196819841272832850678677423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131213227515221900452451615 196819841272832850678677423)
      ·
        refine ⟨295229761909249276018016135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196819841272832850678677423 295229761909249276018016135)
        ·
          refine ⟨442844642863873914027024203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295229761909249276018016135 442844642863873914027024203)
          ·
            refine ⟨664266964295810871040536305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442844642863873914027024203 664266964295810871040536305)
            ·
              refine ⟨498200223221858153280402229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 664266964295810871040536305 498200223221858153280402229)
              ·
                refine ⟨46706270927049201870037709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 498200223221858153280402229 46706270927049201870037709)
                ·
                  refine ⟨17514851597643450701264141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46706270927049201870037709 17514851597643450701264141)
                  ·
                    refine ⟨6568069349116294012974053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17514851597643450701264141 6568069349116294012974053)
                    ·
                      refine ⟨1231513002959305127432635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6568069349116294012974053 1231513002959305127432635)
                      ·
                        rfl

theorem cell23_2398363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 4].length) (baseStart_2398363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398363 prefixEnd_2398363 := by exact prefixLift 2398363
  have htrace : WordTrace (prefixWord ++ tailWord_2398363) baseStart_2398363 baseEnd_2398363 := by
    simpa [prefixWord, tailWord_2398363, baseEnd_2398363] using wordTrace_append hprefix tailTrace_2398363
  have hstable : (prefixWord ++ tailWord_2398363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398363).length < 2 ^ (prefixWord ++ tailWord_2398363).sum := by decide
  have hdescent : baseEnd_2398363 < baseStart_2398363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398373 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 2, 8]
def baseStart_2398373 : Nat := 118140960795 + 2398373 * 2 ^ 59
def prefixEnd_2398373 : Nat := 4983230072969 + 3 ^ 40 * 2398373 * 2
def baseEnd_2398373 : Nat := 410506045921950029435863

theorem tailTrace_2398373 : CollatzResearch.WordTrace tailWord_2398373 prefixEnd_2398373 410506045921950029435863 := by
  unfold tailWord_2398373
  simp only [CollatzResearch.WordTrace]
  refine ⟨87475849740111705342831773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58317233160074470228554515 87475849740111705342831773)
  ·
    refine ⟨32803443652541889503561915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87475849740111705342831773 32803443652541889503561915)
    ·
      refine ⟨49205165478812834255342873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32803443652541889503561915 49205165478812834255342873)
      ·
        refine ⟨36903874109109625691507155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49205165478812834255342873 36903874109109625691507155)
        ·
          refine ⟨55355811163664438537260733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36903874109109625691507155 55355811163664438537260733)
          ·
            refine ⟨20758429186374164451472775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55355811163664438537260733 20758429186374164451472775)
            ·
              refine ⟨31137643779561246677209163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20758429186374164451472775 31137643779561246677209163)
              ·
                refine ⟨46706465669341870015813745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31137643779561246677209163 46706465669341870015813745)
                ·
                  refine ⟨35029849252006402511860309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46706465669341870015813745 35029849252006402511860309)
                  ·
                    refine ⟨410506045921950029435863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35029849252006402511860309 410506045921950029435863)
                    ·
                      rfl

theorem cell23_2398373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_2398373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398373 prefixEnd_2398373 := by exact prefixLift 2398373
  have htrace : WordTrace (prefixWord ++ tailWord_2398373) baseStart_2398373 baseEnd_2398373 := by
    simpa [prefixWord, tailWord_2398373, baseEnd_2398373] using wordTrace_append hprefix tailTrace_2398373
  have hstable : (prefixWord ++ tailWord_2398373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398373).length < 2 ^ (prefixWord ++ tailWord_2398373).sum := by decide
  have hdescent : baseEnd_2398373 < baseStart_2398373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398383 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 5]
def baseStart_2398383 : Nat := 118140960795 + 2398383 * 2 ^ 59
def prefixEnd_2398383 : Nat := 4983230072969 + 3 ^ 40 * 2398383 * 2
def baseEnd_2398383 : Nat := 1231523272572395049182543

theorem tailTrace_2398383 : CollatzResearch.WordTrace tailWord_2398383 prefixEnd_2398383 1231523272572395049182543 := by
  unfold tailWord_2398383
  simp only [CollatzResearch.WordTrace]
  refine ⟨87476214470075477050695803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58317476313383651367130535 87476214470075477050695803)
  ·
    refine ⟨131214321705113215576043705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87476214470075477050695803 131214321705113215576043705)
    ·
      refine ⟨98410741278834911682032779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131214321705113215576043705 98410741278834911682032779)
      ·
        refine ⟨147616111918252367523049169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98410741278834911682032779 147616111918252367523049169)
        ·
          refine ⟨110712083938689275642286877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147616111918252367523049169 110712083938689275642286877)
          ·
            refine ⟨41517031477008478365857579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110712083938689275642286877 41517031477008478365857579)
            ·
              refine ⟨62275547215512717548786369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41517031477008478365857579 62275547215512717548786369)
              ·
                refine ⟨46706660411634538161589777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62275547215512717548786369 46706660411634538161589777)
                ·
                  refine ⟨35029995308725903621192333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46706660411634538161589777 35029995308725903621192333)
                  ·
                    refine ⟨13136248240772213857947125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35029995308725903621192333 13136248240772213857947125)
                    ·
                      refine ⟨1231523272572395049182543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13136248240772213857947125 1231523272572395049182543)
                      ·
                        rfl

theorem cell23_2398383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_2398383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398383 prefixEnd_2398383 := by exact prefixLift 2398383
  have htrace : WordTrace (prefixWord ++ tailWord_2398383) baseStart_2398383 baseEnd_2398383 := by
    simpa [prefixWord, tailWord_2398383, baseEnd_2398383] using wordTrace_append hprefix tailTrace_2398383
  have hstable : (prefixWord ++ tailWord_2398383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398383).length < 2 ^ (prefixWord ++ tailWord_2398383).sum := by decide
  have hdescent : baseEnd_2398383 < baseStart_2398383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398457 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 4, 3, 2]
def baseStart_2398457 : Nat := 118140960795 + 2398457 * 2 ^ 59
def prefixEnd_2398457 : Nat := 4983230072969 + 3 ^ 40 * 2398457 * 2
def baseEnd_2398457 : Nat := 1231561270140827759657203

theorem tailTrace_2398457 : CollatzResearch.WordTrace tailWord_2398457 prefixEnd_2398457 1231561270140827759657203 := by
  unfold tailWord_2398457
  simp only [CollatzResearch.WordTrace]
  refine ⟨87478913471807387688889625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58319275647871591792593083 87478913471807387688889625)
  ·
    refine ⟨65609185103855540766667219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87478913471807387688889625 65609185103855540766667219)
    ·
      refine ⟨98413777655783311150000829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65609185103855540766667219 98413777655783311150000829)
      ·
        refine ⟨36905166620918741681250311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98413777655783311150000829 36905166620918741681250311)
        ·
          refine ⟨55357749931378112521875467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36905166620918741681250311 55357749931378112521875467)
          ·
            refine ⟨83036624897067168782813201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55357749931378112521875467 83036624897067168782813201)
            ·
              refine ⟨62277468672800376587109901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83036624897067168782813201 62277468672800376587109901)
              ·
                refine ⟨23354050752300141220166213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62277468672800376587109901 23354050752300141220166213)
                ·
                  refine ⟨4378884516056276478781165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23354050752300141220166213 4378884516056276478781165)
                  ·
                    refine ⟨1642081693521103679542937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4378884516056276478781165 1642081693521103679542937)
                    ·
                      refine ⟨1231561270140827759657203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1642081693521103679542937 1231561270140827759657203)
                      ·
                        rfl

theorem cell23_2398457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 3, 2].length) (baseStart_2398457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398457 prefixEnd_2398457 := by exact prefixLift 2398457
  have htrace : WordTrace (prefixWord ++ tailWord_2398457) baseStart_2398457 baseEnd_2398457 := by
    simpa [prefixWord, tailWord_2398457, baseEnd_2398457] using wordTrace_append hprefix tailTrace_2398457
  have hstable : (prefixWord ++ tailWord_2398457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398457).length < 2 ^ (prefixWord ++ tailWord_2398457).sum := by decide
  have hdescent : baseEnd_2398457 < baseStart_2398457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398487 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 4]
def baseStart_2398487 : Nat := 118140960795 + 2398487 * 2 ^ 59
def prefixEnd_2398487 : Nat := 4983230072969 + 3 ^ 40 * 2398487 * 2
def baseEnd_2398487 : Nat := 1231576674560462642282065

theorem tailTrace_2398487 : CollatzResearch.WordTrace tailWord_2398487 prefixEnd_2398487 1231576674560462642282065 := by
  unfold tailWord_2398487
  simp only [CollatzResearch.WordTrace]
  refine ⟨87480007661698702812481715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58320005107799135208321143 87480007661698702812481715)
  ·
    refine ⟨131220011492548054218722573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87480007661698702812481715 131220011492548054218722573)
    ·
      refine ⟨49207504309705520332020965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131220011492548054218722573 49207504309705520332020965)
      ·
        refine ⟨9226407058069785062253931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49207504309705520332020965 9226407058069785062253931)
        ·
          refine ⟨13839610587104677593380897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9226407058069785062253931 13839610587104677593380897)
          ·
            refine ⟨10379707940328508195035673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13839610587104677593380897 10379707940328508195035673)
            ·
              refine ⟨7784780955246381146276755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10379707940328508195035673 7784780955246381146276755)
              ·
                refine ⟨11677171432869571719415133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7784780955246381146276755 11677171432869571719415133)
                ·
                  refine ⟨4378939287326089394780675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11677171432869571719415133 4378939287326089394780675)
                  ·
                    refine ⟨6568408930989134092171013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4378939287326089394780675 6568408930989134092171013)
                    ·
                      refine ⟨1231576674560462642282065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6568408930989134092171013 1231576674560462642282065)
                      ·
                        rfl

theorem cell23_2398487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_2398487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398487 prefixEnd_2398487 := by exact prefixLift 2398487
  have htrace : WordTrace (prefixWord ++ tailWord_2398487) baseStart_2398487 baseEnd_2398487 := by
    simpa [prefixWord, tailWord_2398487, baseEnd_2398487] using wordTrace_append hprefix tailTrace_2398487
  have hstable : (prefixWord ++ tailWord_2398487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398487).length < 2 ^ (prefixWord ++ tailWord_2398487).sum := by decide
  have hdescent : baseEnd_2398487 < baseStart_2398487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398498 : List Nat := [3, 3, 1, 1, 3, 2, 2, 3, 1, 1, 3]
def baseStart_2398498 : Nat := 118140960795 + 2398498 * 2 ^ 59
def prefixEnd_2398498 : Nat := 4983230072969 + 3 ^ 40 * 2398498 * 2
def baseEnd_2398498 : Nat := 1231582322847662099244515

theorem tailTrace_2398498 : CollatzResearch.WordTrace tailWord_2398498 prefixEnd_2398498 1231582322847662099244515 := by
  unfold tailWord_2398498
  simp only [CollatzResearch.WordTrace]
  refine ⟨21870102216164712922783037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58320272576439234460754765 21870102216164712922783037)
  ·
    refine ⟨8201288331061767346043639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21870102216164712922783037 8201288331061767346043639)
    ·
      refine ⟨12301932496592651019065459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8201288331061767346043639 12301932496592651019065459)
      ·
        refine ⟨18452898744888976528598189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12301932496592651019065459 18452898744888976528598189)
        ·
          refine ⟨6919837029333366198224321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18452898744888976528598189 6919837029333366198224321)
          ·
            refine ⟨5189877772000024648668241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6919837029333366198224321 5189877772000024648668241)
            ·
              refine ⟨3892408329000018486501181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5189877772000024648668241 3892408329000018486501181)
              ·
                refine ⟨1459653123375006932437943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3892408329000018486501181 1459653123375006932437943)
                ·
                  refine ⟨2189479685062510398656915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1459653123375006932437943 2189479685062510398656915)
                  ·
                    refine ⟨3284219527593765597985373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2189479685062510398656915 3284219527593765597985373)
                    ·
                      refine ⟨1231582322847662099244515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3284219527593765597985373 1231582322847662099244515)
                      ·
                        rfl

theorem cell23_2398498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_2398498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398498 prefixEnd_2398498 := by exact prefixLift 2398498
  have htrace : WordTrace (prefixWord ++ tailWord_2398498) baseStart_2398498 baseEnd_2398498 := by
    simpa [prefixWord, tailWord_2398498, baseEnd_2398498] using wordTrace_append hprefix tailTrace_2398498
  have hstable : (prefixWord ++ tailWord_2398498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398498).length < 2 ^ (prefixWord ++ tailWord_2398498).sum := by decide
  have hdescent : baseEnd_2398498 < baseStart_2398498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398501 : List Nat := [1, 3, 1, 2, 5, 2, 2, 1, 1, 5]
def baseStart_2398501 : Nat := 118140960795 + 2398501 * 2 ^ 59
def prefixEnd_2398501 : Nat := 4983230072969 + 3 ^ 40 * 2398501 * 2
def baseEnd_2398501 : Nat := 410527954429875195835667

theorem tailTrace_2398501 : CollatzResearch.WordTrace tailWord_2398501 prefixEnd_2398501 410527954429875195835667 := by
  unfold tailWord_2398501
  simp only [CollatzResearch.WordTrace]
  refine ⟨87480518283647983203491357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58320345522431988802327571 87480518283647983203491357)
  ·
    refine ⟨32805194356367993701309259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87480518283647983203491357 32805194356367993701309259)
    ·
      refine ⟨49207791534551990551963889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32805194356367993701309259 49207791534551990551963889)
      ·
        refine ⟨36905843650913992913972917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49207791534551990551963889 36905843650913992913972917)
        ·
          refine ⟨3459922842273186835684961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36905843650913992913972917 3459922842273186835684961)
          ·
            refine ⟨2594942131704890126763721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3459922842273186835684961 2594942131704890126763721)
            ·
              refine ⟨1946206598778667595072791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2594942131704890126763721 1946206598778667595072791)
              ·
                refine ⟨2919309898168001392609187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1946206598778667595072791 2919309898168001392609187)
                ·
                  refine ⟨4378964847252002088913781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2919309898168001392609187 4378964847252002088913781)
                  ·
                    refine ⟨410527954429875195835667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4378964847252002088913781 410527954429875195835667)
                    ·
                      rfl

theorem cell23_2398501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 1, 5].length) (baseStart_2398501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398501 prefixEnd_2398501 := by exact prefixLift 2398501
  have htrace : WordTrace (prefixWord ++ tailWord_2398501) baseStart_2398501 baseEnd_2398501 := by
    simpa [prefixWord, tailWord_2398501, baseEnd_2398501] using wordTrace_append hprefix tailTrace_2398501
  have hstable : (prefixWord ++ tailWord_2398501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398501).length < 2 ^ (prefixWord ++ tailWord_2398501).sum := by decide
  have hdescent : baseEnd_2398501 < baseStart_2398501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398514 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 4, 4]
def baseStart_2398514 : Nat := 118140960795 + 2398514 * 2 ^ 59
def prefixEnd_2398514 : Nat := 4983230072969 + 3 ^ 40 * 2398514 * 2
def baseEnd_2398514 : Nat := 410530179512711345548147

theorem tailTrace_2398514 : CollatzResearch.WordTrace tailWord_2398514 prefixEnd_2398514 410530179512711345548147 := by
  unfold tailWord_2398514
  simp only [CollatzResearch.WordTrace]
  refine ⟨21870248108150221605928649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58320661621733924282476397 21870248108150221605928649)
  ·
    refine ⟨16402686081112666204446487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21870248108150221605928649 16402686081112666204446487)
    ·
      refine ⟨24604029121668999306669731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16402686081112666204446487 24604029121668999306669731)
      ·
        refine ⟨36906043682503498960004597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24604029121668999306669731 36906043682503498960004597)
        ·
          refine ⟨3459941595234703027500431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36906043682503498960004597 3459941595234703027500431)
          ·
            refine ⟨5189912392852054541250647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3459941595234703027500431 5189912392852054541250647)
            ·
              refine ⟨7784868589278081811875971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5189912392852054541250647 7784868589278081811875971)
              ·
                refine ⟨11677302883917122717813957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7784868589278081811875971 11677302883917122717813957)
                ·
                  refine ⟨2189494290734460509590117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11677302883917122717813957 2189494290734460509590117)
                  ·
                    refine ⟨410530179512711345548147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2189494290734460509590117 410530179512711345548147)
                    ·
                      rfl

theorem cell23_2398514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_2398514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398514 prefixEnd_2398514 := by exact prefixLift 2398514
  have htrace : WordTrace (prefixWord ++ tailWord_2398514) baseStart_2398514 baseEnd_2398514 := by
    simpa [prefixWord, tailWord_2398514, baseEnd_2398514] using wordTrace_append hprefix tailTrace_2398514
  have hstable : (prefixWord ++ tailWord_2398514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398514).length < 2 ^ (prefixWord ++ tailWord_2398514).sum := by decide
  have hdescent : baseEnd_2398514 < baseStart_2398514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398521 : List Nat := [1, 2, 1, 6, 1, 1, 1, 3, 3, 2, 2]
def baseStart_2398521 : Nat := 118140960795 + 2398521 * 2 ^ 59
def prefixEnd_2398521 : Nat := 4983230072969 + 3 ^ 40 * 2398521 * 2
def baseEnd_2398521 : Nat := 1231594132902715509256909

theorem tailTrace_2398521 : CollatzResearch.WordTrace tailWord_2398521 prefixEnd_2398521 1231594132902715509256909 := by
  unfold tailWord_2398521
  simp only [CollatzResearch.WordTrace]
  refine ⟨87481247743575526619219417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58320831829050351079479611 87481247743575526619219417)
  ·
    refine ⟨65610935807681644964414563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87481247743575526619219417 65610935807681644964414563)
    ·
      refine ⟨98416403711522467446621845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65610935807681644964414563 98416403711522467446621845)
      ·
        refine ⟨4613268923977615661560399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 98416403711522467446621845 4613268923977615661560399)
        ·
          refine ⟨6919903385966423492340599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4613268923977615661560399 6919903385966423492340599)
          ·
            refine ⟨10379855078949635238510899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6919903385966423492340599 10379855078949635238510899)
            ·
              refine ⟨15569782618424452857766349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10379855078949635238510899 15569782618424452857766349)
              ·
                refine ⟨5838668481909169821662381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15569782618424452857766349 5838668481909169821662381)
                ·
                  refine ⟨2189500680715938683123393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5838668481909169821662381 2189500680715938683123393)
                  ·
                    refine ⟨1642125510536954012342545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2189500680715938683123393 1642125510536954012342545)
                    ·
                      refine ⟨1231594132902715509256909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1642125510536954012342545 1231594132902715509256909)
                      ·
                        rfl

theorem cell23_2398521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_2398521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398521 prefixEnd_2398521 := by exact prefixLift 2398521
  have htrace : WordTrace (prefixWord ++ tailWord_2398521) baseStart_2398521 baseEnd_2398521 := by
    simpa [prefixWord, tailWord_2398521, baseEnd_2398521] using wordTrace_append hprefix tailTrace_2398521
  have hstable : (prefixWord ++ tailWord_2398521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398521).length < 2 ^ (prefixWord ++ tailWord_2398521).sum := by decide
  have hdescent : baseEnd_2398521 < baseStart_2398521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398582 : List Nat := [5, 1, 1, 4, 2, 1, 2, 1, 2, 4]
def baseStart_2398582 : Nat := 118140960795 + 2398582 * 2 ^ 59
def prefixEnd_2398582 : Nat := 4983230072969 + 3 ^ 40 * 2398582 * 2
def baseEnd_2398582 : Nat := 410541818407546590198043

theorem tailTrace_2398582 : CollatzResearch.WordTrace tailWord_2398582 prefixEnd_2398582 410541818407546590198043 := by
  unfold tailWord_2398582
  simp only [CollatzResearch.WordTrace]
  refine ⟨5467717037272158377324375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58322315064236356024793333 5467717037272158377324375)
  ·
    refine ⟨8201575555908237565986563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5467717037272158377324375 8201575555908237565986563)
    ·
      refine ⟨12302363333862356348979845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8201575555908237565986563 12302363333862356348979845)
      ·
        refine ⟨2306693125099191815433721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12302363333862356348979845 2306693125099191815433721)
        ·
          refine ⟨1730019843824393861575291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2306693125099191815433721 1730019843824393861575291)
          ·
            refine ⟨2595029765736590792362937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1730019843824393861575291 2595029765736590792362937)
            ·
              refine ⟨1946272324302443094272203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2595029765736590792362937 1946272324302443094272203)
              ·
                refine ⟨2919408486453664641408305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1946272324302443094272203 2919408486453664641408305)
                ·
                  refine ⟨2189556364840248481056229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2919408486453664641408305 2189556364840248481056229)
                  ·
                    refine ⟨410541818407546590198043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2189556364840248481056229 410541818407546590198043)
                    ·
                      rfl

theorem cell23_2398582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_2398582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398582 prefixEnd_2398582 := by exact prefixLift 2398582
  have htrace : WordTrace (prefixWord ++ tailWord_2398582) baseStart_2398582 baseEnd_2398582 := by
    simpa [prefixWord, tailWord_2398582, baseEnd_2398582] using wordTrace_append hprefix tailTrace_2398582
  have hstable : (prefixWord ++ tailWord_2398582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398582).length < 2 ^ (prefixWord ++ tailWord_2398582).sum := by decide
  have hdescent : baseEnd_2398582 < baseStart_2398582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398664 : List Nat := [2, 1, 3, 1, 3, 2, 3, 1, 2, 5]
def baseStart_2398664 : Nat := 118140960795 + 2398664 * 2 ^ 59
def prefixEnd_2398664 : Nat := 4983230072969 + 3 ^ 40 * 2398664 * 2
def baseEnd_2398664 : Nat := 410555853545436149922917

theorem tailTrace_2398664 : CollatzResearch.WordTrace tailWord_2398664 prefixEnd_2398664 410555853545436149922917 := by
  unfold tailWord_2398664
  simp only [CollatzResearch.WordTrace]
  refine ⟨43743231691028731020837523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58324308921371641361116697 43743231691028731020837523)
  ·
    refine ⟨65614847536543096531256285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43743231691028731020837523 65614847536543096531256285)
    ·
      refine ⟨24605567826203661199221107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65614847536543096531256285 24605567826203661199221107)
      ·
        refine ⟨36908351739305491798831661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24605567826203661199221107 36908351739305491798831661)
        ·
          refine ⟨13840631902239559424561873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36908351739305491798831661 13840631902239559424561873)
          ·
            refine ⟨10380473926679669568421405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13840631902239559424561873 10380473926679669568421405)
            ·
              refine ⟨3892677722504876088158027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10380473926679669568421405 3892677722504876088158027)
              ·
                refine ⟨5839016583757314132237041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3892677722504876088158027 5839016583757314132237041)
                ·
                  refine ⟨4379262437817985599177781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5839016583757314132237041 4379262437817985599177781)
                  ·
                    refine ⟨410555853545436149922917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4379262437817985599177781 410555853545436149922917)
                    ·
                      rfl

theorem cell23_2398664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_2398664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398664 prefixEnd_2398664 := by exact prefixLift 2398664
  have htrace : WordTrace (prefixWord ++ tailWord_2398664) baseStart_2398664 baseEnd_2398664 := by
    simpa [prefixWord, tailWord_2398664, baseEnd_2398664] using wordTrace_append hprefix tailTrace_2398664
  have hstable : (prefixWord ++ tailWord_2398664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398664).length < 2 ^ (prefixWord ++ tailWord_2398664).sum := by decide
  have hdescent : baseEnd_2398664 < baseStart_2398664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398724 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 8]
def baseStart_2398724 : Nat := 118140960795 + 2398724 * 2 ^ 59
def prefixEnd_2398724 : Nat := 4983230072969 + 3 ^ 40 * 2398724 * 2
def baseEnd_2398724 : Nat := 136855374386175357224275

theorem tailTrace_2398724 : CollatzResearch.WordTrace tailWord_2398724 prefixEnd_2398724 136855374386175357224275 := by
  unfold tailWord_2398724
  simp only [CollatzResearch.WordTrace]
  refine ⟨43744325880920046144429613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58325767841226728192572817 43744325880920046144429613)
  ·
    refine ⟨16404122205345017304161105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43744325880920046144429613 16404122205345017304161105)
    ·
      refine ⟨12303091654008762978120829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16404122205345017304161105 12303091654008762978120829)
      ·
        refine ⟨4613659370253286116795311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12303091654008762978120829 4613659370253286116795311)
        ·
          refine ⟨6920489055379929175192967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4613659370253286116795311 6920489055379929175192967)
          ·
            refine ⟨10380733583069893762789451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6920489055379929175192967 10380733583069893762789451)
            ·
              refine ⟨15571100374604840644184177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10380733583069893762789451 15571100374604840644184177)
              ·
                refine ⟨11678325280953630483138133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15571100374604840644184177 11678325280953630483138133)
                ·
                  refine ⟨136855374386175357224275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11678325280953630483138133 136855374386175357224275)
                  ·
                    rfl

theorem cell23_2398724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_2398724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398724 prefixEnd_2398724 := by exact prefixLift 2398724
  have htrace : WordTrace (prefixWord ++ tailWord_2398724) baseStart_2398724 baseEnd_2398724 := by
    simpa [prefixWord, tailWord_2398724, baseEnd_2398724] using wordTrace_append hprefix tailTrace_2398724
  have hstable : (prefixWord ++ tailWord_2398724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398724).length < 2 ^ (prefixWord ++ tailWord_2398724).sum := by decide
  have hdescent : baseEnd_2398724 < baseStart_2398724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398754 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 3, 5]
def baseStart_2398754 : Nat := 118140960795 + 2398754 * 2 ^ 59
def prefixEnd_2398754 : Nat := 4983230072969 + 3 ^ 40 * 2398754 * 2
def baseEnd_2398754 : Nat := 410571257965071032547779

theorem tailTrace_2398754 : CollatzResearch.WordTrace tailWord_2398754 prefixEnd_2398754 410571257965071032547779 := by
  unfold tailWord_2398754
  simp only [CollatzResearch.WordTrace]
  refine ⟨21872436487932851853112829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58326497301154271608300877 21872436487932851853112829)
  ·
    refine ⟨8202163682974819444917311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21872436487932851853112829 8202163682974819444917311)
    ·
      refine ⟨12303245524462229167375967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8202163682974819444917311 12303245524462229167375967)
      ·
        refine ⟨18454868286693343751063951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12303245524462229167375967 18454868286693343751063951)
        ·
          refine ⟨27682302430040015626595927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18454868286693343751063951 27682302430040015626595927)
          ·
            refine ⟨41523453645060023439893891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27682302430040015626595927 41523453645060023439893891)
            ·
              refine ⟨62285180467590035159840837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41523453645060023439893891 62285180467590035159840837)
              ·
                refine ⟨11678471337673131592470157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62285180467590035159840837 11678471337673131592470157)
                ·
                  refine ⟨4379426751627424347176309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11678471337673131592470157 4379426751627424347176309)
                  ·
                    refine ⟨410571257965071032547779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4379426751627424347176309 410571257965071032547779)
                    ·
                      rfl

theorem cell23_2398754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_2398754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398754 prefixEnd_2398754 := by exact prefixLift 2398754
  have htrace : WordTrace (prefixWord ++ tailWord_2398754) baseStart_2398754 baseEnd_2398754 := by
    simpa [prefixWord, tailWord_2398754, baseEnd_2398754] using wordTrace_append hprefix tailTrace_2398754
  have hstable : (prefixWord ++ tailWord_2398754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398754).length < 2 ^ (prefixWord ++ tailWord_2398754).sum := by decide
  have hdescent : baseEnd_2398754 < baseStart_2398754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398767 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 7, 6]
def baseStart_2398767 : Nat := 118140960795 + 2398767 * 2 ^ 59
def prefixEnd_2398767 : Nat := 4983230072969 + 3 ^ 40 * 2398767 * 2
def baseEnd_2398767 : Nat := 410573483047907182260259

theorem tailTrace_2398767 : CollatzResearch.WordTrace tailWord_2398767 prefixEnd_2398767 410573483047907182260259 := by
  unfold tailWord_2398767
  simp only [CollatzResearch.WordTrace]
  refine ⟨87490220100684310632674555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58326813400456207088449703 87490220100684310632674555)
  ·
    refine ⟨131235330151026465949011833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87490220100684310632674555 131235330151026465949011833)
    ·
      refine ⟨98426497613269849461758875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131235330151026465949011833 98426497613269849461758875)
      ·
        refine ⟨147639746419904774192638313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98426497613269849461758875 147639746419904774192638313)
        ·
          refine ⟨110729809814928580644478735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147639746419904774192638313 110729809814928580644478735)
          ·
            refine ⟨166094714722392870966718103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110729809814928580644478735 166094714722392870966718103)
            ·
              refine ⟨249142072083589306450077155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166094714722392870966718103 249142072083589306450077155)
              ·
                refine ⟨373713108125383959675115733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249142072083589306450077155 373713108125383959675115733)
                ·
                  refine ⟨8758900971688686554885525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 373713108125383959675115733 8758900971688686554885525)
                  ·
                    refine ⟨410573483047907182260259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8758900971688686554885525 410573483047907182260259)
                    ·
                      rfl

theorem cell23_2398767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 6].length) (baseStart_2398767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398767 prefixEnd_2398767 := by exact prefixLift 2398767
  have htrace : WordTrace (prefixWord ++ tailWord_2398767) baseStart_2398767 baseEnd_2398767 := by
    simpa [prefixWord, tailWord_2398767, baseEnd_2398767] using wordTrace_append hprefix tailTrace_2398767
  have hstable : (prefixWord ++ tailWord_2398767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398767).length < 2 ^ (prefixWord ++ tailWord_2398767).sum := by decide
  have hdescent : baseEnd_2398767 < baseStart_2398767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398778 : List Nat := [3, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2]
def baseStart_2398778 : Nat := 118140960795 + 2398778 * 2 ^ 59
def prefixEnd_2398778 : Nat := 4983230072969 + 3 ^ 40 * 2398778 * 2
def baseEnd_2398778 : Nat := 1231726097430921003743227

theorem tailTrace_2398778 : CollatzResearch.WordTrace tailWord_2398778 prefixEnd_2398778 1231726097430921003743227 := by
  unfold tailWord_2398778
  simp only [CollatzResearch.WordTrace]
  refine ⟨21872655325911114877831247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58327080869096306340883325 21872655325911114877831247)
  ·
    refine ⟨32808982988866672316746871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21872655325911114877831247 32808982988866672316746871)
    ·
      refine ⟨49213474483300008475120307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32808982988866672316746871 49213474483300008475120307)
      ·
        refine ⟨73820211724950012712680461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49213474483300008475120307 73820211724950012712680461)
        ·
          refine ⟨27682579396856254767255173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73820211724950012712680461 27682579396856254767255173)
          ·
            refine ⟨5190483636910547768860345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27682579396856254767255173 5190483636910547768860345)
            ·
              refine ⟨3892862727682910826645259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5190483636910547768860345 3892862727682910826645259)
              ·
                refine ⟨5839294091524366239967889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3892862727682910826645259 5839294091524366239967889)
                ·
                  refine ⟨4379470568643274679975917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5839294091524366239967889 4379470568643274679975917)
                  ·
                    refine ⟨1642301463241228004990969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4379470568643274679975917 1642301463241228004990969)
                    ·
                      refine ⟨1231726097430921003743227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1642301463241228004990969 1231726097430921003743227)
                      ·
                        rfl

theorem cell23_2398778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2].length) (baseStart_2398778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398778 prefixEnd_2398778 := by exact prefixLift 2398778
  have htrace : WordTrace (prefixWord ++ tailWord_2398778) baseStart_2398778 baseEnd_2398778 := by
    simpa [prefixWord, tailWord_2398778, baseEnd_2398778] using wordTrace_append hprefix tailTrace_2398778
  have hstable : (prefixWord ++ tailWord_2398778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398778).length < 2 ^ (prefixWord ++ tailWord_2398778).sum := by decide
  have hdescent : baseEnd_2398778 < baseStart_2398778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398784 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 6, 4]
def baseStart_2398784 : Nat := 118140960795 + 2398784 * 2 ^ 59
def prefixEnd_2398784 : Nat := 4983230072969 + 3 ^ 40 * 2398784 * 2
def baseEnd_2398784 : Nat := 410576392771615993422733

theorem tailTrace_2398784 : CollatzResearch.WordTrace tailWord_2398784 prefixEnd_2398784 410576392771615993422733 := by
  unfold tailWord_2398784
  simp only [CollatzResearch.WordTrace]
  refine ⟨43745420070811361268021703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58327226761081815024028937 43745420070811361268021703)
  ·
    refine ⟨65618130106217041902032555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43745420070811361268021703 65618130106217041902032555)
    ·
      refine ⟨98427195159325562853048833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65618130106217041902032555 98427195159325562853048833)
      ·
        refine ⟨73820396369494172139786625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98427195159325562853048833 73820396369494172139786625)
        ·
          refine ⟨55365297277120629104839969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73820396369494172139786625 55365297277120629104839969)
          ·
            refine ⟨41523972957840471828629977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55365297277120629104839969 41523972957840471828629977)
            ·
              refine ⟨31142979718380353871472483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41523972957840471828629977 31142979718380353871472483)
              ·
                refine ⟨46714469577570530807208725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31142979718380353871472483 46714469577570530807208725)
                ·
                  refine ⟨2189740761448618631587909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46714469577570530807208725 2189740761448618631587909)
                  ·
                    refine ⟨410576392771615993422733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2189740761448618631587909 410576392771615993422733)
                    ·
                      rfl

theorem cell23_2398784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 6, 4].length) (baseStart_2398784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398784 prefixEnd_2398784 := by exact prefixLift 2398784
  have htrace : WordTrace (prefixWord ++ tailWord_2398784) baseStart_2398784 baseEnd_2398784 := by
    simpa [prefixWord, tailWord_2398784, baseEnd_2398784] using wordTrace_append hprefix tailTrace_2398784
  have hstable : (prefixWord ++ tailWord_2398784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398784).length < 2 ^ (prefixWord ++ tailWord_2398784).sum := by decide
  have hdescent : baseEnd_2398784 < baseStart_2398784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398801 : List Nat := [1, 2, 2, 1, 3, 3, 1, 4, 2, 4]
def baseStart_2398801 : Nat := 118140960795 + 2398801 * 2 ^ 59
def prefixEnd_2398801 : Nat := 4983230072969 + 3 ^ 40 * 2398801 * 2
def baseEnd_2398801 : Nat := 410579302495324804585207

theorem tailTrace_2398801 : CollatzResearch.WordTrace tailWord_2398801 prefixEnd_2398801 410579302495324804585207 := by
  unfold tailWord_2398801
  simp only [CollatzResearch.WordTrace]
  refine ⟨87491460182561134439412257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58327640121707422959608171 87491460182561134439412257)
  ·
    refine ⟨65618595136920850829559193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87491460182561134439412257 65618595136920850829559193)
    ·
      refine ⟨49213946352690638122169395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65618595136920850829559193 49213946352690638122169395)
      ·
        refine ⟨73820919529035957183254093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49213946352690638122169395 73820919529035957183254093)
        ·
          refine ⟨27682844823388483943720285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73820919529035957183254093 27682844823388483943720285)
          ·
            refine ⟨10381066808770681478895107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27682844823388483943720285 10381066808770681478895107)
            ·
              refine ⟨15571600213156022218342661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10381066808770681478895107 15571600213156022218342661)
              ·
                refine ⟨2919675039966754165939249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15571600213156022218342661 2919675039966754165939249)
                ·
                  refine ⟨2189756279975065624454437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2919675039966754165939249 2189756279975065624454437)
                  ·
                    refine ⟨410579302495324804585207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2189756279975065624454437 410579302495324804585207)
                    ·
                      rfl

theorem cell23_2398801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 4].length) (baseStart_2398801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398801 prefixEnd_2398801 := by exact prefixLift 2398801
  have htrace : WordTrace (prefixWord ++ tailWord_2398801) baseStart_2398801 baseEnd_2398801 := by
    simpa [prefixWord, tailWord_2398801, baseEnd_2398801] using wordTrace_append hprefix tailTrace_2398801
  have hstable : (prefixWord ++ tailWord_2398801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398801).length < 2 ^ (prefixWord ++ tailWord_2398801).sum := by decide
  have hdescent : baseEnd_2398801 < baseStart_2398801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398841 : List Nat := [1, 2, 1, 3, 3, 2, 2, 2, 1, 3, 3]
def baseStart_2398841 : Nat := 118140960795 + 2398841 * 2 ^ 59
def prefixEnd_2398841 : Nat := 4983230072969 + 3 ^ 40 * 2398841 * 2
def baseEnd_2398841 : Nat := 1231758446712154257255437

theorem tailTrace_2398841 : CollatzResearch.WordTrace tailWord_2398841 prefixEnd_2398841 1231758446712154257255437 := by
  unfold tailWord_2398841
  simp only [CollatzResearch.WordTrace]
  refine ⟨87492919102416221270868377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58328612734944147513912251 87492919102416221270868377)
  ·
    refine ⟨65619689326812165953151283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87492919102416221270868377 65619689326812165953151283)
    ·
      refine ⟨98429533990218248929726925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65619689326812165953151283 98429533990218248929726925)
      ·
        refine ⟨36911075246331843348647597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98429533990218248929726925 36911075246331843348647597)
        ·
          refine ⟨13841653217374441255742849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36911075246331843348647597 13841653217374441255742849)
          ·
            refine ⟨10381239913030830941807137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13841653217374441255742849 10381239913030830941807137)
            ·
              refine ⟨7785929934773123206355353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10381239913030830941807137 7785929934773123206355353)
              ·
                refine ⟨5839447451079842404766515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7785929934773123206355353 5839447451079842404766515)
                ·
                  refine ⟨8759171176619763607149773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5839447451079842404766515 8759171176619763607149773)
                  ·
                    refine ⟨3284689191232411352681165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8759171176619763607149773 3284689191232411352681165)
                    ·
                      refine ⟨1231758446712154257255437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3284689191232411352681165 1231758446712154257255437)
                      ·
                        rfl

theorem cell23_2398841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_2398841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398841 prefixEnd_2398841 := by exact prefixLift 2398841
  have htrace : WordTrace (prefixWord ++ tailWord_2398841) baseStart_2398841 baseEnd_2398841 := by
    simpa [prefixWord, tailWord_2398841, baseEnd_2398841] using wordTrace_append hprefix tailTrace_2398841
  have hstable : (prefixWord ++ tailWord_2398841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398841).length < 2 ^ (prefixWord ++ tailWord_2398841).sum := by decide
  have hdescent : baseEnd_2398841 < baseStart_2398841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398901 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_2398901 : Nat := 118140960795 + 2398901 * 2 ^ 59
def prefixEnd_2398901 : Nat := 4983230072969 + 3 ^ 40 * 2398901 * 2
def baseEnd_2398901 : Nat := 1231789255551424022505161

theorem tailTrace_2398901 : CollatzResearch.WordTrace tailWord_2398901 prefixEnd_2398901 1231789255551424022505161 := by
  unfold tailWord_2398901
  simp only [CollatzResearch.WordTrace]
  refine ⟨87495107482198851518052557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58330071654799234345368371 87495107482198851518052557)
  ·
    refine ⟨32810665305824569319269709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87495107482198851518052557 32810665305824569319269709)
    ·
      refine ⟨12303999489684213494726141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32810665305824569319269709 12303999489684213494726141)
      ·
        refine ⟨4613999808631580060522303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12303999489684213494726141 4613999808631580060522303)
        ·
          refine ⟨6920999712947370090783455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4613999808631580060522303 6920999712947370090783455)
          ·
            refine ⟨10381499569421055136175183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6920999712947370090783455 10381499569421055136175183)
            ·
              refine ⟨15572249354131582704262775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10381499569421055136175183 15572249354131582704262775)
              ·
                refine ⟨23358374031197374056394163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15572249354131582704262775 23358374031197374056394163)
                ·
                  refine ⟨35037561046796061084591245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23358374031197374056394163 35037561046796061084591245)
                  ·
                    refine ⟨13139085392548522906721717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35037561046796061084591245 13139085392548522906721717)
                    ·
                      refine ⟨1231789255551424022505161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13139085392548522906721717 1231789255551424022505161)
                      ·
                        rfl

theorem cell23_2398901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_2398901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398901 prefixEnd_2398901 := by exact prefixLift 2398901
  have htrace : WordTrace (prefixWord ++ tailWord_2398901) baseStart_2398901 baseEnd_2398901 := by
    simpa [prefixWord, tailWord_2398901, baseEnd_2398901] using wordTrace_append hprefix tailTrace_2398901
  have hstable : (prefixWord ++ tailWord_2398901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398901).length < 2 ^ (prefixWord ++ tailWord_2398901).sum := by decide
  have hdescent : baseEnd_2398901 < baseStart_2398901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398944 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 7]
def baseStart_2398944 : Nat := 118140960795 + 2398944 * 2 ^ 59
def prefixEnd_2398944 : Nat := 4983230072969 + 3 ^ 40 * 2398944 * 2
def baseEnd_2398944 : Nat := 1231811335219567354267463

theorem tailTrace_2398944 : CollatzResearch.WordTrace tailWord_2398944 prefixEnd_2398944 1231811335219567354267463 := by
  unfold tailWord_2398944
  simp only [CollatzResearch.WordTrace]
  refine ⟨43748337910521534930933943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58331117214028713241245257 43748337910521534930933943)
  ·
    refine ⟨65622506865782302396400915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43748337910521534930933943 65622506865782302396400915)
    ·
      refine ⟨98433760298673453594601373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65622506865782302396400915 98433760298673453594601373)
      ·
        refine ⟨36912660112002545097975515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98433760298673453594601373 36912660112002545097975515)
        ·
          refine ⟨55368990168003817646963273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36912660112002545097975515 55368990168003817646963273)
          ·
            refine ⟨41526742626002863235222455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55368990168003817646963273 41526742626002863235222455)
            ·
              refine ⟨62290113939004294852833683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41526742626002863235222455 62290113939004294852833683)
              ·
                refine ⟨93435170908506442279250525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62290113939004294852833683 93435170908506442279250525)
                ·
                  refine ⟨35038189090689915854718947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93435170908506442279250525 35038189090689915854718947)
                  ·
                    refine ⟨52557283636034873782078421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35038189090689915854718947 52557283636034873782078421)
                    ·
                      refine ⟨1231811335219567354267463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52557283636034873782078421 1231811335219567354267463)
                      ·
                        rfl

theorem cell23_2398944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_2398944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398944 prefixEnd_2398944 := by exact prefixLift 2398944
  have htrace : WordTrace (prefixWord ++ tailWord_2398944) baseStart_2398944 baseEnd_2398944 := by
    simpa [prefixWord, tailWord_2398944, baseEnd_2398944] using wordTrace_append hprefix tailTrace_2398944
  have hstable : (prefixWord ++ tailWord_2398944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398944).length < 2 ^ (prefixWord ++ tailWord_2398944).sum := by decide
  have hdescent : baseEnd_2398944 < baseStart_2398944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398978 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_2398978 : Nat := 118140960795 + 2398978 * 2 ^ 59
def prefixEnd_2398978 : Nat := 4983230072969 + 3 ^ 40 * 2398978 * 2
def baseEnd_2398978 : Nat := 1231828793561820221242307

theorem tailTrace_2398978 : CollatzResearch.WordTrace tailWord_2398978 prefixEnd_2398978 1231828793561820221242307 := by
  unfold tailWord_2398978
  simp only [CollatzResearch.WordTrace]
  refine ⟨21874478975729973417151397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58331943935279929112403725 21874478975729973417151397)
  ·
    refine ⟨4101464807949370015715887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21874478975729973417151397 4101464807949370015715887)
    ·
      refine ⟨6152197211924055023573831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4101464807949370015715887 6152197211924055023573831)
      ·
        refine ⟨9228295817886082535360747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6152197211924055023573831 9228295817886082535360747)
        ·
          refine ⟨13842443726829123803041121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9228295817886082535360747 13842443726829123803041121)
          ·
            refine ⟨10381832795121842852280841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13842443726829123803041121 10381832795121842852280841)
            ·
              refine ⟨7786374596341382139210631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10381832795121842852280841 7786374596341382139210631)
              ·
                refine ⟨11679561894512073208815947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7786374596341382139210631 11679561894512073208815947)
                ·
                  refine ⟨17519342841768109813223921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11679561894512073208815947 17519342841768109813223921)
                  ·
                    refine ⟨13139507131326082359917941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17519342841768109813223921 13139507131326082359917941)
                    ·
                      refine ⟨1231828793561820221242307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13139507131326082359917941 1231828793561820221242307)
                      ·
                        rfl

theorem cell23_2398978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_2398978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398978 prefixEnd_2398978 := by exact prefixLift 2398978
  have htrace : WordTrace (prefixWord ++ tailWord_2398978) baseStart_2398978 baseEnd_2398978 := by
    simpa [prefixWord, tailWord_2398978, baseEnd_2398978] using wordTrace_append hprefix tailTrace_2398978
  have hstable : (prefixWord ++ tailWord_2398978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398978).length < 2 ^ (prefixWord ++ tailWord_2398978).sum := by decide
  have hdescent : baseEnd_2398978 < baseStart_2398978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398981 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 7, 4]
def baseStart_2398981 : Nat := 118140960795 + 2398981 * 2 ^ 59
def prefixEnd_2398981 : Nat := 4983230072969 + 3 ^ 40 * 2398981 * 2
def baseEnd_2398981 : Nat := 410610111334594569834931

theorem tailTrace_2398981 : CollatzResearch.WordTrace tailWord_2398981 prefixEnd_2398981 410610111334594569834931 := by
  unfold tailWord_2398981
  simp only [CollatzResearch.WordTrace]
  refine ⟨87498025321909025180964797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58332016881272683453976531 87498025321909025180964797)
  ·
    refine ⟨32811759495715884442861799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87498025321909025180964797 32811759495715884442861799)
    ·
      refine ⟨49217639243573826664292699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32811759495715884442861799 49217639243573826664292699)
      ·
        refine ⟨73826458865360739996439049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49217639243573826664292699 73826458865360739996439049)
        ·
          refine ⟨55369844149020554997329287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73826458865360739996439049 55369844149020554997329287)
          ·
            refine ⟨83054766223530832495993931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55369844149020554997329287 83054766223530832495993931)
            ·
              refine ⟨124582149335296248743990897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83054766223530832495993931 124582149335296248743990897)
              ·
                refine ⟨93436612001472186557993173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124582149335296248743990897 93436612001472186557993173)
                ·
                  refine ⟨2189920593784504372452965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 93436612001472186557993173 2189920593784504372452965)
                  ·
                    refine ⟨410610111334594569834931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2189920593784504372452965 410610111334594569834931)
                    ·
                      rfl

theorem cell23_2398981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 4].length) (baseStart_2398981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398981 prefixEnd_2398981 := by exact prefixLift 2398981
  have htrace : WordTrace (prefixWord ++ tailWord_2398981) baseStart_2398981 baseEnd_2398981 := by
    simpa [prefixWord, tailWord_2398981, baseEnd_2398981] using wordTrace_append hprefix tailTrace_2398981
  have hstable : (prefixWord ++ tailWord_2398981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398981).length < 2 ^ (prefixWord ++ tailWord_2398981).sum := by decide
  have hdescent : baseEnd_2398981 < baseStart_2398981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2398991 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 3]
def baseStart_2398991 : Nat := 118140960795 + 2398991 * 2 ^ 59
def prefixEnd_2398991 : Nat := 4983230072969 + 3 ^ 40 * 2398991 * 2
def baseEnd_2398991 : Nat := 1231835468810328670379747

theorem tailTrace_2398991 : CollatzResearch.WordTrace tailWord_2398991 prefixEnd_2398991 1231835468810328670379747 := by
  unfold tailWord_2398991
  simp only [CollatzResearch.WordTrace]
  refine ⟨87498390051872796888828827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58332260034581864592552551 87498390051872796888828827)
  ·
    refine ⟨131247585077809195333243241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87498390051872796888828827 131247585077809195333243241)
    ·
      refine ⟨98435688808356896499932431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131247585077809195333243241 98435688808356896499932431)
      ·
        refine ⟨147653533212535344749898647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98435688808356896499932431 147653533212535344749898647)
        ·
          refine ⟨221480299818803017124847971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147653533212535344749898647 221480299818803017124847971)
          ·
            refine ⟨332220449728204525687271957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221480299818803017124847971 332220449728204525687271957)
            ·
              refine ⟨15572833581009587141590873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 332220449728204525687271957 15572833581009587141590873)
              ·
                refine ⟨11679625185757190356193155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15572833581009587141590873 11679625185757190356193155)
                ·
                  refine ⟨17519437778635785534289733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11679625185757190356193155 17519437778635785534289733)
                  ·
                    refine ⟨3284894583494209787679325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17519437778635785534289733 3284894583494209787679325)
                    ·
                      refine ⟨1231835468810328670379747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3284894583494209787679325 1231835468810328670379747)
                      ·
                        rfl

theorem cell23_2398991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 3].length) (baseStart_2398991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2398991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2398991 prefixEnd_2398991 := by exact prefixLift 2398991
  have htrace : WordTrace (prefixWord ++ tailWord_2398991) baseStart_2398991 baseEnd_2398991 := by
    simpa [prefixWord, tailWord_2398991, baseEnd_2398991] using wordTrace_append hprefix tailTrace_2398991
  have hstable : (prefixWord ++ tailWord_2398991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2398991).length < 2 ^ (prefixWord ++ tailWord_2398991).sum := by decide
  have hdescent : baseEnd_2398991 < baseStart_2398991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2398991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399005 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 1, 3, 4]
def baseStart_2399005 : Nat := 118140960795 + 2399005 * 2 ^ 59
def prefixEnd_2399005 : Nat := 4983230072969 + 3 ^ 40 * 2399005 * 2
def baseEnd_2399005 : Nat := 1231842657539491615604683

theorem tailTrace_2399005 : CollatzResearch.WordTrace tailWord_2399005 prefixEnd_2399005 1231842657539491615604683 := by
  unfold tailWord_2399005
  simp only [CollatzResearch.WordTrace]
  refine ⟨87498900673822077279838469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58332600449214718186558979 87498900673822077279838469)
  ·
    refine ⟨16406043876341639489969713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87498900673822077279838469 16406043876341639489969713)
    ·
      refine ⟨12304532907256229617477285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16406043876341639489969713 12304532907256229617477285)
      ·
        refine ⟨2307099920110543053276991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12304532907256229617477285 2307099920110543053276991)
        ·
          refine ⟨3460649880165814579915487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2307099920110543053276991 3460649880165814579915487)
          ·
            refine ⟨5190974820248721869873231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3460649880165814579915487 5190974820248721869873231)
            ·
              refine ⟨7786462230373082804809847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5190974820248721869873231 7786462230373082804809847)
              ·
                refine ⟨11679693345559624207214771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7786462230373082804809847 11679693345559624207214771)
                ·
                  refine ⟨17519540018339436310822157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11679693345559624207214771 17519540018339436310822157)
                  ·
                    refine ⟨6569827506877288616558309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17519540018339436310822157 6569827506877288616558309)
                    ·
                      refine ⟨1231842657539491615604683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6569827506877288616558309 1231842657539491615604683)
                      ·
                        rfl

theorem cell23_2399005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_2399005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399005 prefixEnd_2399005 := by exact prefixLift 2399005
  have htrace : WordTrace (prefixWord ++ tailWord_2399005) baseStart_2399005 baseEnd_2399005 := by
    simpa [prefixWord, tailWord_2399005, baseEnd_2399005] using wordTrace_append hprefix tailTrace_2399005
  have hstable : (prefixWord ++ tailWord_2399005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399005).length < 2 ^ (prefixWord ++ tailWord_2399005).sum := by decide
  have hdescent : baseEnd_2399005 < baseStart_2399005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399008 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 3]
def baseStart_2399008 : Nat := 118140960795 + 2399008 * 2 ^ 59
def prefixEnd_2399008 : Nat := 4983230072969 + 3 ^ 40 * 2399008 * 2
def baseEnd_2399008 : Nat := 1231844197981455103867169

theorem tailTrace_2399008 : CollatzResearch.WordTrace tailWord_2399008 prefixEnd_2399008 1231844197981455103867169 := by
  unfold tailWord_2399008
  simp only [CollatzResearch.WordTrace]
  refine ⟨43749505046405604396098839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58332673395207472528131785 43749505046405604396098839)
  ·
    refine ⟨65624257569608406594148259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43749505046405604396098839 65624257569608406594148259)
    ·
      refine ⟨98436386354412609891222389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65624257569608406594148259 98436386354412609891222389)
      ·
        refine ⟨9228411220726182177302099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98436386354412609891222389 9228411220726182177302099)
        ·
          refine ⟨13842616831089273265953149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9228411220726182177302099 13842616831089273265953149)
          ·
            refine ⟨5190981311658477474732431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13842616831089273265953149 5190981311658477474732431)
            ·
              refine ⟨7786471967487716212098647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5190981311658477474732431 7786471967487716212098647)
              ·
                refine ⟨11679707951231574318147971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7786471967487716212098647 11679707951231574318147971)
                ·
                  refine ⟨17519561926847361477221957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11679707951231574318147971 17519561926847361477221957)
                  ·
                    refine ⟨3284917861283880276979117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17519561926847361477221957 3284917861283880276979117)
                    ·
                      refine ⟨1231844197981455103867169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3284917861283880276979117 1231844197981455103867169)
                      ·
                        rfl

theorem cell23_2399008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_2399008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399008 prefixEnd_2399008 := by exact prefixLift 2399008
  have htrace : WordTrace (prefixWord ++ tailWord_2399008) baseStart_2399008 baseEnd_2399008 := by
    simpa [prefixWord, tailWord_2399008, baseEnd_2399008] using wordTrace_append hprefix tailTrace_2399008
  have hstable : (prefixWord ++ tailWord_2399008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399008).length < 2 ^ (prefixWord ++ tailWord_2399008).sum := by decide
  have hdescent : baseEnd_2399008 < baseStart_2399008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399048 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 3, 5, 2]
def baseStart_2399048 : Nat := 118140960795 + 2399048 * 2 ^ 59
def prefixEnd_2399048 : Nat := 4983230072969 + 3 ^ 40 * 2399048 * 2
def baseEnd_2399048 : Nat := 1231864737207634947366985

theorem tailTrace_2399048 : CollatzResearch.WordTrace tailWord_2399048 prefixEnd_2399048 1231864737207634947366985 := by
  unfold tailWord_2399048
  simp only [CollatzResearch.WordTrace]
  refine ⟨43750234506333147811826899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58333646008444197082435865 43750234506333147811826899)
  ·
    refine ⟨65625351759499721717740349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43750234506333147811826899 65625351759499721717740349)
    ·
      refine ⟨24609506909812395644152631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65625351759499721717740349 24609506909812395644152631)
      ·
        refine ⟨36914260364718593466228947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24609506909812395644152631 36914260364718593466228947)
        ·
          refine ⟨55371390547077890199343421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36914260364718593466228947 55371390547077890199343421)
          ·
            refine ⟨20764271455154208824753783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55371390547077890199343421 20764271455154208824753783)
            ·
              refine ⟨31146407182731313237130675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20764271455154208824753783 31146407182731313237130675)
              ·
                refine ⟨46719610774096969855696013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31146407182731313237130675 46719610774096969855696013)
                ·
                  refine ⟨17519854040286363695886005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46719610774096969855696013 17519854040286363695886005)
                  ·
                    refine ⟨1642486316276846596489313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17519854040286363695886005 1642486316276846596489313)
                    ·
                      refine ⟨1231864737207634947366985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1642486316276846596489313 1231864737207634947366985)
                      ·
                        rfl

theorem cell23_2399048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 3, 5, 2].length) (baseStart_2399048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399048 prefixEnd_2399048 := by exact prefixLift 2399048
  have htrace : WordTrace (prefixWord ++ tailWord_2399048) baseStart_2399048 baseEnd_2399048 := by
    simpa [prefixWord, tailWord_2399048, baseEnd_2399048] using wordTrace_append hprefix tailTrace_2399048
  have hstable : (prefixWord ++ tailWord_2399048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399048).length < 2 ^ (prefixWord ++ tailWord_2399048).sum := by decide
  have hdescent : baseEnd_2399048 < baseStart_2399048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399071 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 3, 6]
def baseStart_2399071 : Nat := 118140960795 + 2399071 * 2 ^ 59
def prefixEnd_2399071 : Nat := 4983230072969 + 3 ^ 40 * 2399071 * 2
def baseEnd_2399071 : Nat := 410625515754229452459793

theorem tailTrace_2399071 : CollatzResearch.WordTrace tailWord_2399071 prefixEnd_2399071 410625515754229452459793 := by
  unfold tailWord_2399071
  simp only [CollatzResearch.WordTrace]
  refine ⟨87501307891582970551741067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58334205261055313701160711 87501307891582970551741067)
  ·
    refine ⟨131251961837374455827611601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87501307891582970551741067 131251961837374455827611601)
    ·
      refine ⟨98438971378030841870708701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131251961837374455827611601 98438971378030841870708701)
      ·
        refine ⟨36914614266761565701515763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98438971378030841870708701 36914614266761565701515763)
        ·
          refine ⟨55371921400142348552273645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36914614266761565701515763 55371921400142348552273645)
          ·
            refine ⟨20764470525053380707102617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55371921400142348552273645 20764470525053380707102617)
            ·
              refine ⟨15573352893790035530326963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20764470525053380707102617 15573352893790035530326963)
              ·
                refine ⟨23360029340685053295490445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15573352893790035530326963 23360029340685053295490445)
                ·
                  refine ⟨8760011002756894985808917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23360029340685053295490445 8760011002756894985808917)
                  ·
                    refine ⟨410625515754229452459793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8760011002756894985808917 410625515754229452459793)
                    ·
                      rfl

theorem cell23_2399071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 6].length) (baseStart_2399071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399071 prefixEnd_2399071 := by exact prefixLift 2399071
  have htrace : WordTrace (prefixWord ++ tailWord_2399071) baseStart_2399071 baseEnd_2399071 := by
    simpa [prefixWord, tailWord_2399071, baseEnd_2399071] using wordTrace_append hprefix tailTrace_2399071
  have hstable : (prefixWord ++ tailWord_2399071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399071).length < 2 ^ (prefixWord ++ tailWord_2399071).sum := by decide
  have hdescent : baseEnd_2399071 < baseStart_2399071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399088 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 4, 4]
def baseStart_2399088 : Nat := 118140960795 + 2399088 * 2 ^ 59
def prefixEnd_2399088 : Nat := 4983230072969 + 3 ^ 40 * 2399088 * 2
def baseEnd_2399088 : Nat := 410628425477938263622267

theorem tailTrace_2399088 : CollatzResearch.WordTrace tailWord_2399088 prefixEnd_2399088 410628425477938263622267 := by
  unfold tailWord_2399088
  simp only [CollatzResearch.WordTrace]
  refine ⟨43750963966260691227554959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58334618621680921636739945 43750963966260691227554959)
  ·
    refine ⟨65626445949391036841332439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43750963966260691227554959 65626445949391036841332439)
    ·
      refine ⟨98439668924086555261998659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65626445949391036841332439 98439668924086555261998659)
      ·
        refine ⟨147659503386129832892997989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98439668924086555261998659 147659503386129832892997989)
        ·
          refine ⟨27686156884899343667437123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147659503386129832892997989 27686156884899343667437123)
          ·
            refine ⟨41529235327349015501155685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27686156884899343667437123 41529235327349015501155685)
            ·
              refine ⟨7786731623877940406466691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41529235327349015501155685 7786731623877940406466691)
              ·
                refine ⟨11680097435816910609700037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7786731623877940406466691 11680097435816910609700037)
                ·
                  refine ⟨2190018269215670739318757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11680097435816910609700037 2190018269215670739318757)
                  ·
                    refine ⟨410628425477938263622267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2190018269215670739318757 410628425477938263622267)
                    ·
                      rfl

theorem cell23_2399088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 4, 4].length) (baseStart_2399088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399088 prefixEnd_2399088 := by exact prefixLift 2399088
  have htrace : WordTrace (prefixWord ++ tailWord_2399088) baseStart_2399088 baseEnd_2399088 := by
    simpa [prefixWord, tailWord_2399088, baseEnd_2399088] using wordTrace_append hprefix tailTrace_2399088
  have hstable : (prefixWord ++ tailWord_2399088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399088).length < 2 ^ (prefixWord ++ tailWord_2399088).sum := by decide
  have hdescent : baseEnd_2399088 < baseStart_2399088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399089 : List Nat := [1, 2, 2, 2, 1, 5, 3, 2, 1, 1, 3]
def baseStart_2399089 : Nat := 118140960795 + 2399089 * 2 ^ 59
def prefixEnd_2399089 : Nat := 4983230072969 + 3 ^ 40 * 2399089 * 2
def baseEnd_2399089 : Nat := 1231885789914469286954297

theorem tailTrace_2399089 : CollatzResearch.WordTrace tailWord_2399089 prefixEnd_2399089 1231885789914469286954297 := by
  unfold tailWord_2399089
  simp only [CollatzResearch.WordTrace]
  refine ⟨87501964405517759625896321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58334642937011839750597547 87501964405517759625896321)
  ·
    refine ⟨65626473304138319719422241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87501964405517759625896321 65626473304138319719422241)
    ·
      refine ⟨49219854978103739789566681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65626473304138319719422241 49219854978103739789566681)
      ·
        refine ⟨36914891233577804842175011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49219854978103739789566681 36914891233577804842175011)
        ·
          refine ⟨55372336850366707263262517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36914891233577804842175011 55372336850366707263262517)
          ·
            refine ⟨5191156579721878805930861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55372336850366707263262517 5191156579721878805930861)
            ·
              refine ⟨1946683717395704552224073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5191156579721878805930861 1946683717395704552224073)
              ·
                refine ⟨1460012788046778414168055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1946683717395704552224073 1460012788046778414168055)
                ·
                  refine ⟨2190019182070167621252083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1460012788046778414168055 2190019182070167621252083)
                  ·
                    refine ⟨3285028773105251431878125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2190019182070167621252083 3285028773105251431878125)
                    ·
                      refine ⟨1231885789914469286954297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3285028773105251431878125 1231885789914469286954297)
                      ·
                        rfl

theorem cell23_2399089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 1, 1, 3].length) (baseStart_2399089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399089 prefixEnd_2399089 := by exact prefixLift 2399089
  have htrace : WordTrace (prefixWord ++ tailWord_2399089) baseStart_2399089 baseEnd_2399089 := by
    simpa [prefixWord, tailWord_2399089, baseEnd_2399089] using wordTrace_append hprefix tailTrace_2399089
  have hstable : (prefixWord ++ tailWord_2399089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399089).length < 2 ^ (prefixWord ++ tailWord_2399089).sum := by decide
  have hdescent : baseEnd_2399089 < baseStart_2399089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399091 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 6]
def baseStart_2399091 : Nat := 118140960795 + 2399091 * 2 ^ 59
def prefixEnd_2399091 : Nat := 4983230072969 + 3 ^ 40 * 2399091 * 2
def baseEnd_2399091 : Nat := 1231886816875778279129287

theorem tailTrace_2399091 : CollatzResearch.WordTrace tailWord_2399091 prefixEnd_2399091 1231886816875778279129287 := by
  unfold tailWord_2399091
  simp only [CollatzResearch.WordTrace]
  refine ⟨87502037351510513967469127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58334691567673675978312751 87502037351510513967469127)
  ·
    refine ⟨131253056027265770951203691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87502037351510513967469127 131253056027265770951203691)
    ·
      refine ⟨196879584040898656426805537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131253056027265770951203691 196879584040898656426805537)
      ·
        refine ⟨147659688030673992320104153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196879584040898656426805537 147659688030673992320104153)
        ·
          refine ⟨110744766023005494240078115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147659688030673992320104153 110744766023005494240078115)
          ·
            refine ⟨166117149034508241360117173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110744766023005494240078115 166117149034508241360117173)
            ·
              refine ⟨15573482721985147627510985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 166117149034508241360117173 15573482721985147627510985)
              ·
                refine ⟨11680112041488860720633239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15573482721985147627510985 11680112041488860720633239)
                ·
                  refine ⟨17520168062233291080949859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11680112041488860720633239 17520168062233291080949859)
                  ·
                    refine ⟨26280252093349936621424789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17520168062233291080949859 26280252093349936621424789)
                    ·
                      refine ⟨1231886816875778279129287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26280252093349936621424789 1231886816875778279129287)
                      ·
                        rfl

theorem cell23_2399091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 6].length) (baseStart_2399091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399091 prefixEnd_2399091 := by exact prefixLift 2399091
  have htrace : WordTrace (prefixWord ++ tailWord_2399091) baseStart_2399091 baseEnd_2399091 := by
    simpa [prefixWord, tailWord_2399091, baseEnd_2399091] using wordTrace_append hprefix tailTrace_2399091
  have hstable : (prefixWord ++ tailWord_2399091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399091).length < 2 ^ (prefixWord ++ tailWord_2399091).sum := by decide
  have hdescent : baseEnd_2399091 < baseStart_2399091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399098 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3]
def baseStart_2399098 : Nat := 118140960795 + 2399098 * 2 ^ 59
def prefixEnd_2399098 : Nat := 4983230072969 + 3 ^ 40 * 2399098 * 2
def baseEnd_2399098 : Nat := 1231890411240359751741755

theorem tailTrace_2399098 : CollatzResearch.WordTrace tailWord_2399098 prefixEnd_2399098 1231890411240359751741755 := by
  unfold tailWord_2399098
  simp only [CollatzResearch.WordTrace]
  refine ⟨21875573165621288540743487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58334861774990102775315965 21875573165621288540743487)
  ·
    refine ⟨32813359748431932811115231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21875573165621288540743487 32813359748431932811115231)
    ·
      refine ⟨49220039622647899216672847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32813359748431932811115231 49220039622647899216672847)
      ·
        refine ⟨73830059433971848825009271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49220039622647899216672847 73830059433971848825009271)
        ·
          refine ⟨110745089150957773237513907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73830059433971848825009271 110745089150957773237513907)
          ·
            refine ⟨166117633726436659856270861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110745089150957773237513907 166117633726436659856270861)
            ·
              refine ⟨62294112647413747446101573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166117633726436659856270861 62294112647413747446101573)
              ·
                refine ⟨11680146121390077646144045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62294112647413747446101573 11680146121390077646144045)
                ·
                  refine ⟨4380054795521279117304017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11680146121390077646144045 4380054795521279117304017)
                  ·
                    refine ⟨3285041096640959337978013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4380054795521279117304017 3285041096640959337978013)
                    ·
                      refine ⟨1231890411240359751741755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3285041096640959337978013 1231890411240359751741755)
                      ·
                        rfl

theorem cell23_2399098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3].length) (baseStart_2399098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399098 prefixEnd_2399098 := by exact prefixLift 2399098
  have htrace : WordTrace (prefixWord ++ tailWord_2399098) baseStart_2399098 baseEnd_2399098 := by
    simpa [prefixWord, tailWord_2399098, baseEnd_2399098] using wordTrace_append hprefix tailTrace_2399098
  have hstable : (prefixWord ++ tailWord_2399098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399098).length < 2 ^ (prefixWord ++ tailWord_2399098).sum := by decide
  have hdescent : baseEnd_2399098 < baseStart_2399098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399101 : List Nat := [1, 4, 1, 1, 2, 1, 3, 10]
def baseStart_2399101 : Nat := 118140960795 + 2399101 * 2 ^ 59
def prefixEnd_2399101 : Nat := 4983230072969 + 3 ^ 40 * 2399101 * 2
def baseEnd_2399101 : Nat := 45625627840086045926083

theorem tailTrace_2399101 : CollatzResearch.WordTrace tailWord_2399101 prefixEnd_2399101 45625627840086045926083 := by
  unfold tailWord_2399101
  simp only [CollatzResearch.WordTrace]
  refine ⟨87502402081474285675333157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58334934720982857116888771 87502402081474285675333157)
  ·
    refine ⟨16406700390276428564124967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87502402081474285675333157 16406700390276428564124967)
    ·
      refine ⟨24610050585414642846187451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16406700390276428564124967 24610050585414642846187451)
      ·
        refine ⟨36915075878121964269281177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24610050585414642846187451 36915075878121964269281177)
        ·
          refine ⟨27686306908591473201960883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36915075878121964269281177 27686306908591473201960883)
          ·
            refine ⟨41529460362887209802941325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27686306908591473201960883 41529460362887209802941325)
            ·
              refine ⟨15573547636082703676102997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41529460362887209802941325 15573547636082703676102997)
              ·
                refine ⟨45625627840086045926083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15573547636082703676102997 45625627840086045926083)
                ·
                  rfl

theorem cell23_2399101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 10].length) (baseStart_2399101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399101 prefixEnd_2399101 := by exact prefixLift 2399101
  have htrace : WordTrace (prefixWord ++ tailWord_2399101) baseStart_2399101 baseEnd_2399101 := by
    simpa [prefixWord, tailWord_2399101, baseEnd_2399101] using wordTrace_append hprefix tailTrace_2399101
  have hstable : (prefixWord ++ tailWord_2399101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399101).length < 2 ^ (prefixWord ++ tailWord_2399101).sum := by decide
  have hdescent : baseEnd_2399101 < baseStart_2399101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399108 : List Nat := [2, 3, 2, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_2399108 : Nat := 118140960795 + 2399108 * 2 ^ 59
def prefixEnd_2399108 : Nat := 4983230072969 + 3 ^ 40 * 2399108 * 2
def baseEnd_2399108 : Nat := 1231895546046904712616709

theorem tailTrace_2399108 : CollatzResearch.WordTrace tailWord_2399108 prefixEnd_2399108 1231895546046904712616709 := by
  unfold tailWord_2399108
  simp only [CollatzResearch.WordTrace]
  refine ⟨43751328696224462935418989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58335104928299283913891985 43751328696224462935418989)
  ·
    refine ⟨16406748261084173600782121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43751328696224462935418989 16406748261084173600782121)
    ·
      refine ⟨12305061195813130200586591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16406748261084173600782121 12305061195813130200586591)
      ·
        refine ⟨18457591793719695300879887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12305061195813130200586591 18457591793719695300879887)
        ·
          refine ⟨27686387690579542951319831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18457591793719695300879887 27686387690579542951319831)
          ·
            refine ⟨41529581535869314426979747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27686387690579542951319831 41529581535869314426979747)
            ·
              refine ⟨62294372303803971640469621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41529581535869314426979747 62294372303803971640469621)
              ·
                refine ⟨5840097403481622341294027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62294372303803971640469621 5840097403481622341294027)
                ·
                  refine ⟨8760146105222433511941041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5840097403481622341294027 8760146105222433511941041)
                  ·
                    refine ⟨6570109578916825133955781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8760146105222433511941041 6570109578916825133955781)
                    ·
                      refine ⟨1231895546046904712616709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6570109578916825133955781 1231895546046904712616709)
                      ·
                        rfl

theorem cell23_2399108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_2399108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399108 prefixEnd_2399108 := by exact prefixLift 2399108
  have htrace : WordTrace (prefixWord ++ tailWord_2399108) baseStart_2399108 baseEnd_2399108 := by
    simpa [prefixWord, tailWord_2399108, baseEnd_2399108] using wordTrace_append hprefix tailTrace_2399108
  have hstable : (prefixWord ++ tailWord_2399108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399108).length < 2 ^ (prefixWord ++ tailWord_2399108).sum := by decide
  have hdescent : baseEnd_2399108 < baseStart_2399108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399112 : List Nat := [2, 1, 3, 3, 2, 3, 1, 2, 1, 1, 4]
def baseStart_2399112 : Nat := 118140960795 + 2399112 * 2 ^ 59
def prefixEnd_2399112 : Nat := 4983230072969 + 3 ^ 40 * 2399112 * 2
def baseEnd_2399112 : Nat := 1231897599969522696966691

theorem tailTrace_2399112 : CollatzResearch.WordTrace tailWord_2399112 prefixEnd_2399112 1231897599969522696966691 := by
  unfold tailWord_2399112
  simp only [CollatzResearch.WordTrace]
  refine ⟨43751401642217217276991795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58335202189622956369322393 43751401642217217276991795)
  ·
    refine ⟨65627102463325825915487693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43751401642217217276991795 65627102463325825915487693)
    ·
      refine ⟨24610163423747184718307885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65627102463325825915487693 24610163423747184718307885)
      ·
        refine ⟨9228811283905194269365457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24610163423747184718307885 9228811283905194269365457)
        ·
          refine ⟨6921608462928895702024093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9228811283905194269365457 6921608462928895702024093)
          ·
            refine ⟨2595603173598335888259035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6921608462928895702024093 2595603173598335888259035)
            ·
              refine ⟨3893404760397503832388553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2595603173598335888259035 3893404760397503832388553)
              ·
                refine ⟨2920053570298127874291415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3893404760397503832388553 2920053570298127874291415)
                ·
                  refine ⟨4380080355447191811437123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2920053570298127874291415 4380080355447191811437123)
                  ·
                    refine ⟨6570120533170787717155685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4380080355447191811437123 6570120533170787717155685)
                    ·
                      refine ⟨1231897599969522696966691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6570120533170787717155685 1231897599969522696966691)
                      ·
                        rfl

theorem cell23_2399112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_2399112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399112 prefixEnd_2399112 := by exact prefixLift 2399112
  have htrace : WordTrace (prefixWord ++ tailWord_2399112) baseStart_2399112 baseEnd_2399112 := by
    simpa [prefixWord, tailWord_2399112, baseEnd_2399112] using wordTrace_append hprefix tailTrace_2399112
  have hstable : (prefixWord ++ tailWord_2399112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399112).length < 2 ^ (prefixWord ++ tailWord_2399112).sum := by decide
  have hdescent : baseEnd_2399112 < baseStart_2399112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399115 : List Nat := [1, 1, 1, 1, 4, 2, 5, 2, 1, 2, 3]
def baseStart_2399115 : Nat := 118140960795 + 2399115 * 2 ^ 59
def prefixEnd_2399115 : Nat := 4983230072969 + 3 ^ 40 * 2399115 * 2
def baseEnd_2399115 : Nat := 1231899140411486185229177

theorem tailTrace_2399115 : CollatzResearch.WordTrace tailWord_2399115 prefixEnd_2399115 1231899140411486185229177 := by
  unfold tailWord_2399115
  simp only [CollatzResearch.WordTrace]
  refine ⟨87502912703423566066342799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58335275135615710710895199 87502912703423566066342799)
  ·
    refine ⟨131254369055135349099514199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87502912703423566066342799 131254369055135349099514199)
    ·
      refine ⟨196881553582703023649271299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131254369055135349099514199 196881553582703023649271299)
      ·
        refine ⟨295322330374054535473906949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196881553582703023649271299 295322330374054535473906949)
        ·
          refine ⟨55372936945135225401357553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 295322330374054535473906949 55372936945135225401357553)
          ·
            refine ⟨41529702708851419051018165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55372936945135225401357553 41529702708851419051018165)
            ·
              refine ⟨3893409628954820536032953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41529702708851419051018165 3893409628954820536032953)
              ·
                refine ⟨2920057221716115402024715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3893409628954820536032953 2920057221716115402024715)
                ·
                  refine ⟨4380085832574173103037073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2920057221716115402024715 4380085832574173103037073)
                  ·
                    refine ⟨3285064374430629827277805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4380085832574173103037073 3285064374430629827277805)
                    ·
                      refine ⟨1231899140411486185229177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3285064374430629827277805 1231899140411486185229177)
                      ·
                        rfl

theorem cell23_2399115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 2, 3].length) (baseStart_2399115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399115 prefixEnd_2399115 := by exact prefixLift 2399115
  have htrace : WordTrace (prefixWord ++ tailWord_2399115) baseStart_2399115 baseEnd_2399115 := by
    simpa [prefixWord, tailWord_2399115, baseEnd_2399115] using wordTrace_append hprefix tailTrace_2399115
  have hstable : (prefixWord ++ tailWord_2399115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399115).length < 2 ^ (prefixWord ++ tailWord_2399115).sum := by decide
  have hdescent : baseEnd_2399115 < baseStart_2399115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399126 : List Nat := [5, 3, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_2399126 : Nat := 118140960795 + 2399126 * 2 ^ 59
def prefixEnd_2399126 : Nat := 4983230072969 + 3 ^ 40 * 2399126 * 2
def baseEnd_2399126 : Nat := 410634929566228547397209

theorem tailTrace_2399126 : CollatzResearch.WordTrace tailWord_2399126 prefixEnd_2399126 410634929566228547397209 := by
  unfold tailWord_2399126
  simp only [CollatzResearch.WordTrace]
  refine ⟨5468957119148982184062077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58335542604255809963328821 5468957119148982184062077)
  ·
    refine ⟨2050858919680868319023279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5468957119148982184062077 2050858919680868319023279)
    ·
      refine ⟨3076288379521302478534919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2050858919680868319023279 3076288379521302478534919)
      ·
        refine ⟨4614432569281953717802379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3076288379521302478534919 4614432569281953717802379)
        ·
          refine ⟨6921648853922930576703569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4614432569281953717802379 6921648853922930576703569)
          ·
            refine ⟨5191236640442197932527677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6921648853922930576703569 5191236640442197932527677)
            ·
              refine ⟨1946713740165824224697879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5191236640442197932527677 1946713740165824224697879)
              ·
                refine ⟨2920070610248736337046819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1946713740165824224697879 2920070610248736337046819)
                ·
                  refine ⟨4380105915373104505570229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2920070610248736337046819 4380105915373104505570229)
                  ·
                    refine ⟨410634929566228547397209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4380105915373104505570229 410634929566228547397209)
                    ·
                      rfl

theorem cell23_2399126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_2399126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399126 prefixEnd_2399126 := by exact prefixLift 2399126
  have htrace : WordTrace (prefixWord ++ tailWord_2399126) baseStart_2399126 baseEnd_2399126 := by
    simpa [prefixWord, tailWord_2399126, baseEnd_2399126] using wordTrace_append hprefix tailTrace_2399126
  have hstable : (prefixWord ++ tailWord_2399126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399126).length < 2 ^ (prefixWord ++ tailWord_2399126).sum := by decide
  have hdescent : baseEnd_2399126 < baseStart_2399126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399132 : List Nat := [2, 2, 3, 3, 2, 2, 1, 1, 1, 1, 5]
def baseStart_2399132 : Nat := 118140960795 + 2399132 * 2 ^ 59
def prefixEnd_2399132 : Nat := 4983230072969 + 3 ^ 40 * 2399132 * 2
def baseEnd_2399132 : Nat := 1231907869582612618716599

theorem tailTrace_2399132 : CollatzResearch.WordTrace tailWord_2399132 prefixEnd_2399132 1231907869582612618716599 := by
  unfold tailWord_2399132
  simp only [CollatzResearch.WordTrace]
  refine ⟨43751766372180988984855825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58335688496241318646474433 43751766372180988984855825)
  ·
    refine ⟨32813824779135741738641869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43751766372180988984855825 32813824779135741738641869)
    ·
      refine ⟨12305184292175903151990701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32813824779135741738641869 12305184292175903151990701)
      ·
        refine ⟨4614444109565963681996513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12305184292175903151990701 4614444109565963681996513)
        ·
          refine ⟨3460833082174472761497385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4614444109565963681996513 3460833082174472761497385)
          ·
            refine ⟨2595624811630854571123039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3460833082174472761497385 2595624811630854571123039)
            ·
              refine ⟨3893437217446281856684559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2595624811630854571123039 3893437217446281856684559)
              ·
                refine ⟨5840155826169422785026839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3893437217446281856684559 5840155826169422785026839)
                ·
                  refine ⟨8760233739254134177540259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5840155826169422785026839 8760233739254134177540259)
                  ·
                    refine ⟨13140350608881201266310389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8760233739254134177540259 13140350608881201266310389)
                    ·
                      refine ⟨1231907869582612618716599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13140350608881201266310389 1231907869582612618716599)
                      ·
                        rfl

theorem cell23_2399132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_2399132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399132 prefixEnd_2399132 := by exact prefixLift 2399132
  have htrace : WordTrace (prefixWord ++ tailWord_2399132) baseStart_2399132 baseEnd_2399132 := by
    simpa [prefixWord, tailWord_2399132, baseEnd_2399132] using wordTrace_append hprefix tailTrace_2399132
  have hstable : (prefixWord ++ tailWord_2399132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399132).length < 2 ^ (prefixWord ++ tailWord_2399132).sum := by decide
  have hdescent : baseEnd_2399132 < baseStart_2399132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399141 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 2, 3, 7]
def baseStart_2399141 : Nat := 118140960795 + 2399141 * 2 ^ 59
def prefixEnd_2399141 : Nat := 4983230072969 + 3 ^ 40 * 2399141 * 2
def baseEnd_2399141 : Nat := 1231912490908503083504057

theorem tailTrace_2399141 : CollatzResearch.WordTrace tailWord_2399141 prefixEnd_2399141 1231912490908503083504057 := by
  unfold tailWord_2399141
  simp only [CollatzResearch.WordTrace]
  refine ⟨87503861001329372506789277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58335907334219581671192851 87503861001329372506789277)
  ·
    refine ⟨32813947875498514690045979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87503861001329372506789277 32813947875498514690045979)
    ·
      refine ⟨49220921813247772035068969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32813947875498514690045979 49220921813247772035068969)
      ·
        refine ⟨36915691359935829026301727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49220921813247772035068969 36915691359935829026301727)
        ·
          refine ⟨55373537039903743539452591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36915691359935829026301727 55373537039903743539452591)
          ·
            refine ⟨83060305559855615309178887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55373537039903743539452591 83060305559855615309178887)
            ·
              refine ⟨124590458339783422963768331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83060305559855615309178887 124590458339783422963768331)
              ·
                refine ⟨186885687509675134445652497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124590458339783422963768331 186885687509675134445652497)
                ·
                  refine ⟨140164265632256350834239373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 186885687509675134445652497 140164265632256350834239373)
                  ·
                    refine ⟨52561599612096131562839765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 140164265632256350834239373 52561599612096131562839765)
                    ·
                      refine ⟨1231912490908503083504057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52561599612096131562839765 1231912490908503083504057)
                      ·
                        rfl

theorem cell23_2399141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_2399141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399141 prefixEnd_2399141 := by exact prefixLift 2399141
  have htrace : WordTrace (prefixWord ++ tailWord_2399141) baseStart_2399141 baseEnd_2399141 := by
    simpa [prefixWord, tailWord_2399141, baseEnd_2399141] using wordTrace_append hprefix tailTrace_2399141
  have hstable : (prefixWord ++ tailWord_2399141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399141).length < 2 ^ (prefixWord ++ tailWord_2399141).sum := by decide
  have hdescent : baseEnd_2399141 < baseStart_2399141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399185 : List Nat := [1, 2, 2, 1, 2, 1, 3, 4, 1, 4, 2]
def baseStart_2399185 : Nat := 118140960795 + 2399185 * 2 ^ 59
def prefixEnd_2399185 : Nat := 4983230072969 + 3 ^ 40 * 2399185 * 2
def baseEnd_2399185 : Nat := 1231935084057300911353855

theorem tailTrace_2399185 : CollatzResearch.WordTrace tailWord_2399185 prefixEnd_2399185 1231935084057300911353855 := by
  unfold tailWord_2399185
  simp only [CollatzResearch.WordTrace]
  refine ⟨87505465813169968021391009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58336977208779978680927339 87505465813169968021391009)
  ·
    refine ⟨65629099359877476016043257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87505465813169968021391009 65629099359877476016043257)
    ·
      refine ⟨49221824519908107012032443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65629099359877476016043257 49221824519908107012032443)
      ·
        refine ⟨73832736779862160518048665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49221824519908107012032443 73832736779862160518048665)
        ·
          refine ⟨55374552584896620388536499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73832736779862160518048665 55374552584896620388536499)
          ·
            refine ⟨83061828877344930582804749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55374552584896620388536499 83061828877344930582804749)
            ·
              refine ⟨31148185829004348968551781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83061828877344930582804749 31148185829004348968551781)
              ·
                refine ⟨5840284842938315431603459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31148185829004348968551781 5840284842938315431603459)
                ·
                  refine ⟨8760427264407473147405189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5840284842938315431603459 8760427264407473147405189)
                  ·
                    refine ⟨1642580112076401215138473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8760427264407473147405189 1642580112076401215138473)
                    ·
                      refine ⟨1231935084057300911353855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1642580112076401215138473 1231935084057300911353855)
                      ·
                        rfl

theorem cell23_2399185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 4, 2].length) (baseStart_2399185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399185 prefixEnd_2399185 := by exact prefixLift 2399185
  have htrace : WordTrace (prefixWord ++ tailWord_2399185) baseStart_2399185 baseEnd_2399185 := by
    simpa [prefixWord, tailWord_2399185, baseEnd_2399185] using wordTrace_append hprefix tailTrace_2399185
  have hstable : (prefixWord ++ tailWord_2399185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399185).length < 2 ^ (prefixWord ++ tailWord_2399185).sum := by decide
  have hdescent : baseEnd_2399185 < baseStart_2399185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399189 : List Nat := [1, 3, 2, 3, 3, 1, 1, 3, 1, 3, 2]
def baseStart_2399189 : Nat := 118140960795 + 2399189 * 2 ^ 59
def prefixEnd_2399189 : Nat := 4983230072969 + 3 ^ 40 * 2399189 * 2
def baseEnd_2399189 : Nat := 1231937137979918895703837

theorem tailTrace_2399189 : CollatzResearch.WordTrace tailWord_2399189 prefixEnd_2399189 1231937137979918895703837 := by
  unfold tailWord_2399189
  simp only [CollatzResearch.WordTrace]
  refine ⟨87505611705155476704536621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58337074470103651136357747 87505611705155476704536621)
  ·
    refine ⟨32814604389433303764201233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87505611705155476704536621 32814604389433303764201233)
    ·
      refine ⟨24610953292074977823150925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32814604389433303764201233 24610953292074977823150925)
      ·
        refine ⟨9229107484528116683681597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24610953292074977823150925 9229107484528116683681597)
        ·
          refine ⟨3460915306698043756380599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9229107484528116683681597 3460915306698043756380599)
          ·
            refine ⟨5191372960047065634570899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3460915306698043756380599 5191372960047065634570899)
            ·
              refine ⟨7787059440070598451856349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5191372960047065634570899 7787059440070598451856349)
              ·
                refine ⟨2920147290026474419446131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7787059440070598451856349 2920147290026474419446131)
                ·
                  refine ⟨4380220935039711629169197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2920147290026474419446131 4380220935039711629169197)
                  ·
                    refine ⟨1642582850639891860938449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4380220935039711629169197 1642582850639891860938449)
                    ·
                      refine ⟨1231937137979918895703837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1642582850639891860938449 1231937137979918895703837)
                      ·
                        rfl

theorem cell23_2399189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_2399189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399189 prefixEnd_2399189 := by exact prefixLift 2399189
  have htrace : WordTrace (prefixWord ++ tailWord_2399189) baseStart_2399189 baseEnd_2399189 := by
    simpa [prefixWord, tailWord_2399189, baseEnd_2399189] using wordTrace_append hprefix tailTrace_2399189
  have hstable : (prefixWord ++ tailWord_2399189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399189).length < 2 ^ (prefixWord ++ tailWord_2399189).sum := by decide
  have hdescent : baseEnd_2399189 < baseStart_2399189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399208 : List Nat := [2, 1, 4, 1, 1, 1, 3, 3, 7]
def baseStart_2399208 : Nat := 118140960795 + 2399208 * 2 ^ 59
def prefixEnd_2399208 : Nat := 4983230072969 + 3 ^ 40 * 2399208 * 2
def baseEnd_2399208 : Nat := 136882988234706035707361

theorem tailTrace_2399208 : CollatzResearch.WordTrace tailWord_2399208 prefixEnd_2399208 136882988234706035707361 := by
  unfold tailWord_2399208
  simp only [CollatzResearch.WordTrace]
  refine ⟨43753152346043321474739139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58337536461391095299652185 43753152346043321474739139)
  ·
    refine ⟨65629728519064982212108709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43753152346043321474739139 65629728519064982212108709)
    ·
      refine ⟨12305574097324684164770383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65629728519064982212108709 12305574097324684164770383)
      ·
        refine ⟨18458361145987026247155575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12305574097324684164770383 18458361145987026247155575)
        ·
          refine ⟨27687541718980539370733363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18458361145987026247155575 27687541718980539370733363)
          ·
            refine ⟨41531312578470809056100045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27687541718980539370733363 41531312578470809056100045)
            ·
              refine ⟨15574242216926553396037517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41531312578470809056100045 15574242216926553396037517)
              ·
                refine ⟨5840340831347457523514069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15574242216926553396037517 5840340831347457523514069)
                ·
                  refine ⟨136882988234706035707361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5840340831347457523514069 136882988234706035707361)
                  ·
                    rfl

theorem cell23_2399208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 7].length) (baseStart_2399208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399208 prefixEnd_2399208 := by exact prefixLift 2399208
  have htrace : WordTrace (prefixWord ++ tailWord_2399208) baseStart_2399208 baseEnd_2399208 := by
    simpa [prefixWord, tailWord_2399208, baseEnd_2399208] using wordTrace_append hprefix tailTrace_2399208
  have hstable : (prefixWord ++ tailWord_2399208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399208).length < 2 ^ (prefixWord ++ tailWord_2399208).sum := by decide
  have hdescent : baseEnd_2399208 < baseStart_2399208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399242 : List Nat := [3, 1, 2, 2, 3, 1, 3, 3, 5]
def baseStart_2399242 : Nat := 118140960795 + 2399242 * 2 ^ 59
def prefixEnd_2399242 : Nat := 4983230072969 + 3 ^ 40 * 2399242 * 2
def baseEnd_2399242 : Nat := 136884928050511909815677

theorem tailTrace_2399242 : CollatzResearch.WordTrace tailWord_2399242 prefixEnd_2399242 136884928050511909815677 := by
  unfold tailWord_2399242
  simp only [CollatzResearch.WordTrace]
  refine ⟨21876886193490866689053995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58338363182642311170810653 21876886193490866689053995)
  ·
    refine ⟨32815329290236300033580993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21876886193490866689053995 32815329290236300033580993)
    ·
      refine ⟨24611496967677225025185745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32815329290236300033580993 24611496967677225025185745)
      ·
        refine ⟨18458622725757918768889309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24611496967677225025185745 18458622725757918768889309)
        ·
          refine ⟨6921983522159219538333491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18458622725757918768889309 6921983522159219538333491)
          ·
            refine ⟨10382975283238829307500237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6921983522159219538333491 10382975283238829307500237)
            ·
              refine ⟨3893615731214560990312589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10382975283238829307500237 3893615731214560990312589)
              ·
                refine ⟨1460105899205460371367221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3893615731214560990312589 1460105899205460371367221)
                ·
                  refine ⟨136884928050511909815677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1460105899205460371367221 136884928050511909815677)
                  ·
                    rfl

theorem cell23_2399242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 5].length) (baseStart_2399242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399242 prefixEnd_2399242 := by exact prefixLift 2399242
  have htrace : WordTrace (prefixWord ++ tailWord_2399242) baseStart_2399242 baseEnd_2399242 := by
    simpa [prefixWord, tailWord_2399242, baseEnd_2399242] using wordTrace_append hprefix tailTrace_2399242
  have hstable : (prefixWord ++ tailWord_2399242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399242).length < 2 ^ (prefixWord ++ tailWord_2399242).sum := by decide
  have hdescent : baseEnd_2399242 < baseStart_2399242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399255 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 4, 5]
def baseStart_2399255 : Nat := 118140960795 + 2399255 * 2 ^ 59
def prefixEnd_2399255 : Nat := 4983230072969 + 3 ^ 40 * 2399255 * 2
def baseEnd_2399255 : Nat := 410657009234371879159511

theorem tailTrace_2399255 : CollatzResearch.WordTrace tailWord_2399255 prefixEnd_2399255 410657009234371879159511 := by
  unfold tailWord_2399255
  simp only [CollatzResearch.WordTrace]
  refine ⟨87508018922916369976439219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58338679281944246650959479 87508018922916369976439219)
  ·
    refine ⟨131262028384374554964658829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87508018922916369976439219 131262028384374554964658829)
    ·
      refine ⟨49223260644140458111747061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131262028384374554964658829 49223260644140458111747061)
      ·
        refine ⟨4614680685388167947976287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49223260644140458111747061 4614680685388167947976287)
        ·
          refine ⟨6922021028082251921964431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4614680685388167947976287 6922021028082251921964431)
          ·
            refine ⟨10383031542123377882946647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6922021028082251921964431 10383031542123377882946647)
            ·
              refine ⟨15574547313185066824419971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10383031542123377882946647 15574547313185066824419971)
              ·
                refine ⟨23361820969777600236629957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15574547313185066824419971 23361820969777600236629957)
                ·
                  refine ⟨4380341431833300044368117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23361820969777600236629957 4380341431833300044368117)
                  ·
                    refine ⟨410657009234371879159511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4380341431833300044368117 410657009234371879159511)
                    ·
                      rfl

theorem cell23_2399255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_2399255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399255 prefixEnd_2399255 := by exact prefixLift 2399255
  have htrace : WordTrace (prefixWord ++ tailWord_2399255) baseStart_2399255 baseEnd_2399255 := by
    simpa [prefixWord, tailWord_2399255, baseEnd_2399255] using wordTrace_append hprefix tailTrace_2399255
  have hstable : (prefixWord ++ tailWord_2399255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399255).length < 2 ^ (prefixWord ++ tailWord_2399255).sum := by decide
  have hdescent : baseEnd_2399255 < baseStart_2399255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399265 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 1, 2, 5]
def baseStart_2399265 : Nat := 118140960795 + 2399265 * 2 ^ 59
def prefixEnd_2399265 : Nat := 4983230072969 + 3 ^ 40 * 2399265 * 2
def baseEnd_2399265 : Nat := 1231976162509660598353487

theorem tailTrace_2399265 : CollatzResearch.WordTrace tailWord_2399265 prefixEnd_2399265 1231976162509660598353487 := by
  unfold tailWord_2399265
  simp only [CollatzResearch.WordTrace]
  refine ⟨87508383652880141684303249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58338922435253427789535499 87508383652880141684303249)
  ·
    refine ⟨65631287739660106263227437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87508383652880141684303249 65631287739660106263227437)
    ·
      refine ⟨24611732902372539848710289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65631287739660106263227437 24611732902372539848710289)
      ·
        refine ⟨18458799676779404886532717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24611732902372539848710289 18458799676779404886532717)
        ·
          refine ⟨6922049878792276832449769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18458799676779404886532717 6922049878792276832449769)
          ·
            refine ⟨5191537409094207624337327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6922049878792276832449769 5191537409094207624337327)
            ·
              refine ⟨7787306113641311436505991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5191537409094207624337327 7787306113641311436505991)
              ·
                refine ⟨11680959170461967154758987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7787306113641311436505991 11680959170461967154758987)
                ·
                  refine ⟨17521438755692950732138481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11680959170461967154758987 17521438755692950732138481)
                  ·
                    refine ⟨13141079066769713049103861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17521438755692950732138481 13141079066769713049103861)
                    ·
                      refine ⟨1231976162509660598353487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13141079066769713049103861 1231976162509660598353487)
                      ·
                        rfl

theorem cell23_2399265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_2399265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399265 prefixEnd_2399265 := by exact prefixLift 2399265
  have htrace : WordTrace (prefixWord ++ tailWord_2399265) baseStart_2399265 baseEnd_2399265 := by
    simpa [prefixWord, tailWord_2399265, baseEnd_2399265] using wordTrace_append hprefix tailTrace_2399265
  have hstable : (prefixWord ++ tailWord_2399265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399265).length < 2 ^ (prefixWord ++ tailWord_2399265).sum := by decide
  have hdescent : baseEnd_2399265 < baseStart_2399265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399275 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 1, 6, 2]
def baseStart_2399275 : Nat := 118140960795 + 2399275 * 2 ^ 59
def prefixEnd_2399275 : Nat := 4983230072969 + 3 ^ 40 * 2399275 * 2
def baseEnd_2399275 : Nat := 1231981297316205559228441

theorem tailTrace_2399275 : CollatzResearch.WordTrace tailWord_2399275 prefixEnd_2399275 1231981297316205559228441 := by
  unfold tailWord_2399275
  simp only [CollatzResearch.WordTrace]
  refine ⟨87508748382843913392167279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58339165588562608928111519 87508748382843913392167279)
  ·
    refine ⟨131263122574265870088250919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87508748382843913392167279 131263122574265870088250919)
    ·
      refine ⟨196894683861398805132376379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131263122574265870088250919 196894683861398805132376379)
      ·
        refine ⟨295342025792098207698564569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196894683861398805132376379 295342025792098207698564569)
        ·
          refine ⟨221506519344073655773923427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295342025792098207698564569 221506519344073655773923427)
          ·
            refine ⟨332259779016110483660885141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221506519344073655773923427 332259779016110483660885141)
            ·
              refine ⟨15574677141380178921603991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 332259779016110483660885141 15574677141380178921603991)
              ·
                refine ⟨23362015712070268382405987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15574677141380178921603991 23362015712070268382405987)
                ·
                  refine ⟨35043023568105402573608981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23362015712070268382405987 35043023568105402573608981)
                  ·
                    refine ⟨1642641729754940745637921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35043023568105402573608981 1642641729754940745637921)
                    ·
                      refine ⟨1231981297316205559228441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1642641729754940745637921 1231981297316205559228441)
                      ·
                        rfl

theorem cell23_2399275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 6, 2].length) (baseStart_2399275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399275 prefixEnd_2399275 := by exact prefixLift 2399275
  have htrace : WordTrace (prefixWord ++ tailWord_2399275) baseStart_2399275 baseEnd_2399275 := by
    simpa [prefixWord, tailWord_2399275, baseEnd_2399275] using wordTrace_append hprefix tailTrace_2399275
  have hstable : (prefixWord ++ tailWord_2399275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399275).length < 2 ^ (prefixWord ++ tailWord_2399275).sum := by decide
  have hdescent : baseEnd_2399275 < baseStart_2399275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399285 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 5, 4]
def baseStart_2399285 : Nat := 118140960795 + 2399285 * 2 ^ 59
def prefixEnd_2399285 : Nat := 4983230072969 + 3 ^ 40 * 2399285 * 2
def baseEnd_2399285 : Nat := 410662144040916840034465

theorem tailTrace_2399285 : CollatzResearch.WordTrace tailWord_2399285 prefixEnd_2399285 410662144040916840034465 := by
  unfold tailWord_2399285
  simp only [CollatzResearch.WordTrace]
  refine ⟨87509113112807685100031309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58339408741871790066687539 87509113112807685100031309)
  ·
    refine ⟨32815917417302881912511741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87509113112807685100031309 32815917417302881912511741)
    ·
      refine ⟨12305969031488580717191903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32815917417302881912511741 12305969031488580717191903)
      ·
        refine ⟨18458953547232871075787855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12305969031488580717191903 18458953547232871075787855)
        ·
          refine ⟨27688430320849306613681783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18458953547232871075787855 27688430320849306613681783)
          ·
            refine ⟨41532645481273959920522675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27688430320849306613681783 41532645481273959920522675)
            ·
              refine ⟨62298968221910939880784013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41532645481273959920522675 62298968221910939880784013)
              ·
                refine ⟨23362113083216602455294005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62298968221910939880784013 23362113083216602455294005)
                ·
                  refine ⟨2190198101551556480183813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23362113083216602455294005 2190198101551556480183813)
                  ·
                    refine ⟨410662144040916840034465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2190198101551556480183813 410662144040916840034465)
                    ·
                      rfl

theorem cell23_2399285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_2399285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399285 prefixEnd_2399285 := by exact prefixLift 2399285
  have htrace : WordTrace (prefixWord ++ tailWord_2399285) baseStart_2399285 baseEnd_2399285 := by
    simpa [prefixWord, tailWord_2399285, baseEnd_2399285] using wordTrace_append hprefix tailTrace_2399285
  have hstable : (prefixWord ++ tailWord_2399285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399285).length < 2 ^ (prefixWord ++ tailWord_2399285).sum := by decide
  have hdescent : baseEnd_2399285 < baseStart_2399285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399292 : List Nat := [2, 2, 2, 2, 2, 3, 2, 1, 2, 1, 4]
def baseStart_2399292 : Nat := 118140960795 + 2399292 * 2 ^ 59
def prefixEnd_2399292 : Nat := 4983230072969 + 3 ^ 40 * 2399292 * 2
def baseEnd_2399292 : Nat := 1231990026487331992715863

theorem tailTrace_2399292 : CollatzResearch.WordTrace tailWord_2399292 prefixEnd_2399292 1231990026487331992715863 := by
  unfold tailWord_2399292
  simp only [CollatzResearch.WordTrace]
  refine ⟨43754684211891162647768065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58339578949188216863690753 43754684211891162647768065)
  ·
    refine ⟨32816013158918371985826049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43754684211891162647768065 32816013158918371985826049)
    ·
      refine ⟨24612009869188778989369537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32816013158918371985826049 24612009869188778989369537)
      ·
        refine ⟨18459007401891584242027153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24612009869188778989369537 18459007401891584242027153)
        ·
          refine ⟨13844255551418688181520365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18459007401891584242027153 13844255551418688181520365)
          ·
            refine ⟨5191595831782008068070137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13844255551418688181520365 5191595831782008068070137)
            ·
              refine ⟨3893696873836506051052603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5191595831782008068070137 3893696873836506051052603)
              ·
                refine ⟨5840545310754759076578905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3893696873836506051052603 5840545310754759076578905)
                ·
                  refine ⟨4380408983066069307434179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5840545310754759076578905 4380408983066069307434179)
                  ·
                    refine ⟨6570613474599103961151269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4380408983066069307434179 6570613474599103961151269)
                    ·
                      refine ⟨1231990026487331992715863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6570613474599103961151269 1231990026487331992715863)
                      ·
                        rfl

theorem cell23_2399292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_2399292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399292 prefixEnd_2399292 := by exact prefixLift 2399292
  have htrace : WordTrace (prefixWord ++ tailWord_2399292) baseStart_2399292 baseEnd_2399292 := by
    simpa [prefixWord, tailWord_2399292, baseEnd_2399292] using wordTrace_append hprefix tailTrace_2399292
  have hstable : (prefixWord ++ tailWord_2399292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399292).length < 2 ^ (prefixWord ++ tailWord_2399292).sum := by decide
  have hdescent : baseEnd_2399292 < baseStart_2399292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399326 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_2399326 : Nat := 118140960795 + 2399326 * 2 ^ 59
def prefixEnd_2399326 : Nat := 4983230072969 + 3 ^ 40 * 2399326 * 2
def baseEnd_2399326 : Nat := 1232007484829584859690707

theorem tailTrace_2399326 : CollatzResearch.WordTrace tailWord_2399326 prefixEnd_2399326 1232007484829584859690707 := by
  unfold tailWord_2399326
  simp only [CollatzResearch.WordTrace]
  refine ⟨10938826063207393637784229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58340405670439432734849221 10938826063207393637784229)
  ·
    refine ⟨2051029886851386307084543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10938826063207393637784229 2051029886851386307084543)
    ·
      refine ⟨3076544830277079460626815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2051029886851386307084543 3076544830277079460626815)
      ·
        refine ⟨4614817245415619190940223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3076544830277079460626815 4614817245415619190940223)
        ·
          refine ⟨6922225868123428786410335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4614817245415619190940223 6922225868123428786410335)
          ·
            refine ⟨10383338802185143179615503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6922225868123428786410335 10383338802185143179615503)
            ·
              refine ⟨15575008203277714769423255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10383338802185143179615503 15575008203277714769423255)
              ·
                refine ⟨23362512304916572154134883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15575008203277714769423255 23362512304916572154134883)
                ·
                  refine ⟨35043768457374858231202325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23362512304916572154134883 35043768457374858231202325)
                  ·
                    refine ⟨1642676646439446479587609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35043768457374858231202325 1642676646439446479587609)
                    ·
                      refine ⟨1232007484829584859690707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1642676646439446479587609 1232007484829584859690707)
                      ·
                        rfl

theorem cell23_2399326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_2399326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399326 prefixEnd_2399326 := by exact prefixLift 2399326
  have htrace : WordTrace (prefixWord ++ tailWord_2399326) baseStart_2399326 baseEnd_2399326 := by
    simpa [prefixWord, tailWord_2399326, baseEnd_2399326] using wordTrace_append hprefix tailTrace_2399326
  have hstable : (prefixWord ++ tailWord_2399326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399326).length < 2 ^ (prefixWord ++ tailWord_2399326).sum := by decide
  have hdescent : baseEnd_2399326 < baseStart_2399326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399399 : List Nat := [1, 1, 6, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_2399399 : Nat := 118140960795 + 2399399 * 2 ^ 59
def prefixEnd_2399399 : Nat := 4983230072969 + 3 ^ 40 * 2399399 * 2
def baseEnd_2399399 : Nat := 1232044968917363074077871

theorem tailTrace_2399399 : CollatzResearch.WordTrace tailWord_2399399 prefixEnd_2399399 1232044968917363074077871 := by
  unfold tailWord_2399399
  simp only [CollatzResearch.WordTrace]
  refine ⟨87513271034394682569681251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58342180689596455046454167 87513271034394682569681251)
  ·
    refine ⟨131269906551592023854521877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87513271034394682569681251 131269906551592023854521877)
    ·
      refine ⟨6153276869605876118180713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 131269906551592023854521877 6153276869605876118180713)
      ·
        refine ⟨4614957652204407088635535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6153276869605876118180713 4614957652204407088635535)
        ·
          refine ⟨6922436478306610632953303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4614957652204407088635535 6922436478306610632953303)
          ·
            refine ⟨10383654717459915949429955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6922436478306610632953303 10383654717459915949429955)
            ·
              refine ⟨15575482076189873924144933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10383654717459915949429955 15575482076189873924144933)
              ·
                refine ⟨2920402889285601360777175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15575482076189873924144933 2920402889285601360777175)
                ·
                  refine ⟨4380604333928402041165763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2920402889285601360777175 4380604333928402041165763)
                  ·
                    refine ⟨6570906500892603061748645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4380604333928402041165763 6570906500892603061748645)
                    ·
                      refine ⟨1232044968917363074077871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6570906500892603061748645 1232044968917363074077871)
                      ·
                        rfl

theorem cell23_2399399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_2399399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399399 prefixEnd_2399399 := by exact prefixLift 2399399
  have htrace : WordTrace (prefixWord ++ tailWord_2399399) baseStart_2399399 baseEnd_2399399 := by
    simpa [prefixWord, tailWord_2399399, baseEnd_2399399] using wordTrace_append hprefix tailTrace_2399399
  have hstable : (prefixWord ++ tailWord_2399399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399399).length < 2 ^ (prefixWord ++ tailWord_2399399).sum := by decide
  have hdescent : baseEnd_2399399 < baseStart_2399399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399416 : List Nat := [2, 1, 2, 1, 2, 1, 2, 7, 1, 2, 2]
def baseStart_2399416 : Nat := 118140960795 + 2399416 * 2 ^ 59
def prefixEnd_2399416 : Nat := 4983230072969 + 3 ^ 40 * 2399416 * 2
def baseEnd_2399416 : Nat := 1232053698088489507565293

theorem tailTrace_2399416 : CollatzResearch.WordTrace tailWord_2399416 prefixEnd_2399416 1232053698088489507565293 := by
  unfold tailWord_2399416
  simp only [CollatzResearch.WordTrace]
  refine ⟨43756945537666547236525051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58342594050222062982033401 43756945537666547236525051)
  ·
    refine ⟨65635418306499820854787577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43756945537666547236525051 65635418306499820854787577)
    ·
      refine ⟨49226563729874865641090683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65635418306499820854787577 49226563729874865641090683)
      ·
        refine ⟨73839845594812298461636025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49226563729874865641090683 73839845594812298461636025)
        ·
          refine ⟨55379884196109223846227019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73839845594812298461636025 55379884196109223846227019)
          ·
            refine ⟨83069826294163835769340529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55379884196109223846227019 83069826294163835769340529)
            ·
              refine ⟨62302369720622876827005397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83069826294163835769340529 62302369720622876827005397)
              ·
                refine ⟨1460211790327098675632939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 62302369720622876827005397 1460211790327098675632939)
                ·
                  refine ⟨2190317685490648013449409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1460211790327098675632939 2190317685490648013449409)
                  ·
                    refine ⟨1642738264117986010087057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2190317685490648013449409 1642738264117986010087057)
                    ·
                      refine ⟨1232053698088489507565293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1642738264117986010087057 1232053698088489507565293)
                      ·
                        rfl

theorem cell23_2399416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 1, 2, 2].length) (baseStart_2399416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399416 prefixEnd_2399416 := by exact prefixLift 2399416
  have htrace : WordTrace (prefixWord ++ tailWord_2399416) baseStart_2399416 baseEnd_2399416 := by
    simpa [prefixWord, tailWord_2399416, baseEnd_2399416] using wordTrace_append hprefix tailTrace_2399416
  have hstable : (prefixWord ++ tailWord_2399416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399416).length < 2 ^ (prefixWord ++ tailWord_2399416).sum := by decide
  have hdescent : baseEnd_2399416 < baseStart_2399416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399422 : List Nat := [4, 2, 1, 1, 3, 3, 9]
def baseStart_2399422 : Nat := 118140960795 + 2399422 * 2 ^ 59
def prefixEnd_2399422 : Nat := 4983230072969 + 3 ^ 40 * 2399422 * 2
def baseEnd_2399422 : Nat := 15210577518177981285065

theorem tailTrace_2399422 : CollatzResearch.WordTrace tailWord_2399422 prefixEnd_2399422 15210577518177981285065 := by
  unfold tailWord_2399422
  simp only [CollatzResearch.WordTrace]
  refine ⟨10939263739163919687221065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58342739942207571665179013 10939263739163919687221065)
  ·
    refine ⟨8204447804372939765415799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10939263739163919687221065 8204447804372939765415799)
    ·
      refine ⟨12306671706559409648123699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8204447804372939765415799 12306671706559409648123699)
      ·
        refine ⟨18460007559839114472185549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12306671706559409648123699 18460007559839114472185549)
        ·
          refine ⟨6922502834939667927069581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18460007559839114472185549 6922502834939667927069581)
          ·
            refine ⟨2595938563102375472651093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6922502834939667927069581 2595938563102375472651093)
            ·
              refine ⟨15210577518177981285065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2595938563102375472651093 15210577518177981285065)
              ·
                rfl

theorem cell23_2399422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 9].length) (baseStart_2399422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399422 prefixEnd_2399422 := by exact prefixLift 2399422
  have htrace : WordTrace (prefixWord ++ tailWord_2399422) baseStart_2399422 baseEnd_2399422 := by
    simpa [prefixWord, tailWord_2399422, baseEnd_2399422] using wordTrace_append hprefix tailTrace_2399422
  have hstable : (prefixWord ++ tailWord_2399422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399422).length < 2 ^ (prefixWord ++ tailWord_2399422).sum := by decide
  have hdescent : baseEnd_2399422 < baseStart_2399422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399453 : List Nat := [1, 4, 3, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_2399453 : Nat := 118140960795 + 2399453 * 2 ^ 59
def prefixEnd_2399453 : Nat := 4983230072969 + 3 ^ 40 * 2399453 * 2
def baseEnd_2399453 : Nat := 1232072696872705862802623

theorem tailTrace_2399453 : CollatzResearch.WordTrace tailWord_2399453 prefixEnd_2399453 1232072696872705862802623 := by
  unfold tailWord_2399453
  simp only [CollatzResearch.WordTrace]
  refine ⟨87515240576199049792147013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58343493717466033194764675 87515240576199049792147013)
  ·
    refine ⟨16409107608037321836027565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87515240576199049792147013 16409107608037321836027565)
    ·
      refine ⟨6153415353013995688510337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16409107608037321836027565 6153415353013995688510337)
      ·
        refine ⟨4615061514760496766382753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6153415353013995688510337 4615061514760496766382753)
        ·
          refine ⟨3461296136070372574787065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4615061514760496766382753 3461296136070372574787065)
          ·
            refine ⟨2595972102052779431090299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3461296136070372574787065 2595972102052779431090299)
            ·
              refine ⟨3893958153079169146635449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2595972102052779431090299 3893958153079169146635449)
              ·
                refine ⟨2920468614809376859976587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3893958153079169146635449 2920468614809376859976587)
                ·
                  refine ⟨4380702922214065289964881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2920468614809376859976587 4380702922214065289964881)
                  ·
                    refine ⟨3285527191660548967473661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4380702922214065289964881 3285527191660548967473661)
                    ·
                      refine ⟨1232072696872705862802623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3285527191660548967473661 1232072696872705862802623)
                      ·
                        rfl

theorem cell23_2399453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_2399453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399453 prefixEnd_2399453 := by exact prefixLift 2399453
  have htrace : WordTrace (prefixWord ++ tailWord_2399453) baseStart_2399453 baseEnd_2399453 := by
    simpa [prefixWord, tailWord_2399453, baseEnd_2399453] using wordTrace_append hprefix tailTrace_2399453
  have hstable : (prefixWord ++ tailWord_2399453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399453).length < 2 ^ (prefixWord ++ tailWord_2399453).sum := by decide
  have hdescent : baseEnd_2399453 < baseStart_2399453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399485 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 1, 5, 6]
def baseStart_2399485 : Nat := 118140960795 + 2399485 * 2 ^ 59
def prefixEnd_2399485 : Nat := 4983230072969 + 3 ^ 40 * 2399485 * 2
def baseEnd_2399485 : Nat := 1232089128253649737602475

theorem tailTrace_2399485 : CollatzResearch.WordTrace tailWord_2399485 prefixEnd_2399485 1232089128253649737602475 := by
  unfold tailWord_2399485
  simp only [CollatzResearch.WordTrace]
  refine ⟨87516407712083119257311909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58344271808055412838207939 87516407712083119257311909)
  ·
    refine ⟨16409326446015584860745983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87516407712083119257311909 16409326446015584860745983)
    ·
      refine ⟨24613989669023377291118975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16409326446015584860745983 24613989669023377291118975)
      ·
        refine ⟨36920984503535065936678463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24613989669023377291118975 36920984503535065936678463)
        ·
          refine ⟨55381476755302598905017695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36920984503535065936678463 55381476755302598905017695)
          ·
            refine ⟨83072215132953898357526543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55381476755302598905017695 83072215132953898357526543)
            ·
              refine ⟨124608322699430847536289815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83072215132953898357526543 124608322699430847536289815)
              ·
                refine ⟨186912484049146271304434723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124608322699430847536289815 186912484049146271304434723)
                ·
                  refine ⟨280368726073719406956652085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186912484049146271304434723 280368726073719406956652085)
                  ·
                    refine ⟨26284568069411194402186133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 280368726073719406956652085 26284568069411194402186133)
                    ·
                      refine ⟨1232089128253649737602475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26284568069411194402186133 1232089128253649737602475)
                      ·
                        rfl

theorem cell23_2399485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_2399485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399485 prefixEnd_2399485 := by exact prefixLift 2399485
  have htrace : WordTrace (prefixWord ++ tailWord_2399485) baseStart_2399485 baseEnd_2399485 := by
    simpa [prefixWord, tailWord_2399485, baseEnd_2399485] using wordTrace_append hprefix tailTrace_2399485
  have hstable : (prefixWord ++ tailWord_2399485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399485).length < 2 ^ (prefixWord ++ tailWord_2399485).sum := by decide
  have hdescent : baseEnd_2399485 < baseStart_2399485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399502 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4]
def baseStart_2399502 : Nat := 118140960795 + 2399502 * 2 ^ 59
def prefixEnd_2399502 : Nat := 4983230072969 + 3 ^ 40 * 2399502 * 2
def baseEnd_2399502 : Nat := 1232097857424776171089897

theorem tailTrace_2399502 : CollatzResearch.WordTrace tailWord_2399502 prefixEnd_2399502 1232097857424776171089897 := by
  unfold tailWord_2399502
  simp only [CollatzResearch.WordTrace]
  refine ⟨10939628469127691395085095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58344685168681020773787173 10939628469127691395085095)
  ·
    refine ⟨16409442703691537092627643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10939628469127691395085095 16409442703691537092627643)
    ·
      refine ⟨24614164055537305638941465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16409442703691537092627643 24614164055537305638941465)
      ·
        refine ⟨18460623041652979229206099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24614164055537305638941465 18460623041652979229206099)
        ·
          refine ⟨27690934562479468843809149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18460623041652979229206099 27690934562479468843809149)
          ·
            refine ⟨10384100460929800816428431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27690934562479468843809149 10384100460929800816428431)
            ·
              refine ⟨15576150691394701224642647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10384100460929800816428431 15576150691394701224642647)
              ·
                refine ⟨23364226037092051836963971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15576150691394701224642647 23364226037092051836963971)
                ·
                  refine ⟨35046339055638077755445957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23364226037092051836963971 35046339055638077755445957)
                  ·
                    refine ⟨6571188572932139579146117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35046339055638077755445957 6571188572932139579146117)
                    ·
                      refine ⟨1232097857424776171089897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6571188572932139579146117 1232097857424776171089897)
                      ·
                        rfl

theorem cell23_2399502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_2399502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399502 prefixEnd_2399502 := by exact prefixLift 2399502
  have htrace : WordTrace (prefixWord ++ tailWord_2399502) baseStart_2399502 baseEnd_2399502 := by
    simpa [prefixWord, tailWord_2399502, baseEnd_2399502] using wordTrace_append hprefix tailTrace_2399502
  have hstable : (prefixWord ++ tailWord_2399502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399502).length < 2 ^ (prefixWord ++ tailWord_2399502).sum := by decide
  have hdescent : baseEnd_2399502 < baseStart_2399502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399512 : List Nat := [2, 1, 2, 3, 1, 4, 1, 2, 7]
def baseStart_2399512 : Nat := 118140960795 + 2399512 * 2 ^ 59
def prefixEnd_2399512 : Nat := 4983230072969 + 3 ^ 40 * 2399512 * 2
def baseEnd_2399512 : Nat := 136900332470146792440539

theorem tailTrace_2399512 : CollatzResearch.WordTrace tailWord_2399512 prefixEnd_2399512 136900332470146792440539 := by
  unfold tailWord_2399512
  simp only [CollatzResearch.WordTrace]
  refine ⟨43758696241492651434272395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58344928321990201912363193 43758696241492651434272395)
  ·
    refine ⟨65638044362238977151408593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43758696241492651434272395 65638044362238977151408593)
    ·
      refine ⟨49228533271679232863556445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65638044362238977151408593 49228533271679232863556445)
      ·
        refine ⟨18460699976879712323833667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49228533271679232863556445 18460699976879712323833667)
        ·
          refine ⟨27691049965319568485750501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18460699976879712323833667 27691049965319568485750501)
          ·
            refine ⟨5192071868497419091078219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27691049965319568485750501 5192071868497419091078219)
            ·
              refine ⟨7788107802746128636617329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5192071868497419091078219 7788107802746128636617329)
              ·
                refine ⟨5841080852059596477462997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7788107802746128636617329 5841080852059596477462997)
                ·
                  refine ⟨136900332470146792440539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5841080852059596477462997 136900332470146792440539)
                  ·
                    rfl

theorem cell23_2399512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 7].length) (baseStart_2399512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399512 prefixEnd_2399512 := by exact prefixLift 2399512
  have htrace : WordTrace (prefixWord ++ tailWord_2399512) baseStart_2399512 baseEnd_2399512 := by
    simpa [prefixWord, tailWord_2399512, baseEnd_2399512] using wordTrace_append hprefix tailTrace_2399512
  have hstable : (prefixWord ++ tailWord_2399512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399512).length < 2 ^ (prefixWord ++ tailWord_2399512).sum := by decide
  have hdescent : baseEnd_2399512 < baseStart_2399512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399556 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_2399556 : Nat := 118140960795 + 2399556 * 2 ^ 59
def prefixEnd_2399556 : Nat := 4983230072969 + 3 ^ 40 * 2399556 * 2
def baseEnd_2399556 : Nat := 1232125585380118959814649

theorem tailTrace_2399556 : CollatzResearch.WordTrace tailWord_2399556 prefixEnd_2399556 1232125585380118959814649 := by
  unfold tailWord_2399556
  simp only [CollatzResearch.WordTrace]
  refine ⟨43759498647412949191573261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58345998196550598922097681 43759498647412949191573261)
  ·
    refine ⟨16409811992779855946839973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43759498647412949191573261 16409811992779855946839973)
    ·
      refine ⟨3076839748646222990032495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16409811992779855946839973 3076839748646222990032495)
      ·
        refine ⟨4615259622969334485048743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3076839748646222990032495 4615259622969334485048743)
        ·
          refine ⟨6922889434454001727573115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4615259622969334485048743 6922889434454001727573115)
          ·
            refine ⟨10384334151681002591359673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6922889434454001727573115 10384334151681002591359673)
            ·
              refine ⟨7788250613760751943519755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10384334151681002591359673 7788250613760751943519755)
              ·
                refine ⟨11682375920641127915279633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7788250613760751943519755 11682375920641127915279633)
                ·
                  refine ⟨8761781940480845936459725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11682375920641127915279633 8761781940480845936459725)
                  ·
                    refine ⟨3285668227680317226172397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8761781940480845936459725 3285668227680317226172397)
                    ·
                      refine ⟨1232125585380118959814649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3285668227680317226172397 1232125585380118959814649)
                      ·
                        rfl

theorem cell23_2399556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_2399556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399556 prefixEnd_2399556 := by exact prefixLift 2399556
  have htrace : WordTrace (prefixWord ++ tailWord_2399556) baseStart_2399556 baseEnd_2399556 := by
    simpa [prefixWord, tailWord_2399556, baseEnd_2399556] using wordTrace_append hprefix tailTrace_2399556
  have hstable : (prefixWord ++ tailWord_2399556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399556).length < 2 ^ (prefixWord ++ tailWord_2399556).sum := by decide
  have hdescent : baseEnd_2399556 < baseStart_2399556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399572 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 2, 8]
def baseStart_2399572 : Nat := 118140960795 + 2399572 * 2 ^ 59
def prefixEnd_2399572 : Nat := 4983230072969 + 3 ^ 40 * 2399572 * 2
def baseEnd_2399572 : Nat := 410711267023530299071525

theorem tailTrace_2399572 : CollatzResearch.WordTrace tailWord_2399572 prefixEnd_2399572 410711267023530299071525 := by
  unfold tailWord_2399572
  simp only [CollatzResearch.WordTrace]
  refine ⟨43759790431383966557864485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58346387241845288743819313 43759790431383966557864485)
  ·
    refine ⟨8204960705884493729599591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43759790431383966557864485 8204960705884493729599591)
    ·
      refine ⟨12307441058826740594399387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8204960705884493729599591 12307441058826740594399387)
      ·
        refine ⟨18461161588240110891599081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12307441058826740594399387 18461161588240110891599081)
        ·
          refine ⟨13845871191180083168699311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18461161588240110891599081 13845871191180083168699311)
          ·
            refine ⟨20768806786770124753048967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13845871191180083168699311 20768806786770124753048967)
            ·
              refine ⟨31153210180155187129573451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20768806786770124753048967 31153210180155187129573451)
              ·
                refine ⟨46729815270232780694360177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31153210180155187129573451 46729815270232780694360177)
                ·
                  refine ⟨35047361452674585520770133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46729815270232780694360177 35047361452674585520770133)
                  ·
                    refine ⟨410711267023530299071525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35047361452674585520770133 410711267023530299071525)
                    ·
                      rfl

theorem cell23_2399572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_2399572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399572 prefixEnd_2399572 := by exact prefixLift 2399572
  have htrace : WordTrace (prefixWord ++ tailWord_2399572) baseStart_2399572 baseEnd_2399572 := by
    simpa [prefixWord, tailWord_2399572, baseEnd_2399572] using wordTrace_append hprefix tailTrace_2399572
  have hstable : (prefixWord ++ tailWord_2399572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399572).length < 2 ^ (prefixWord ++ tailWord_2399572).sum := by decide
  have hdescent : baseEnd_2399572 < baseStart_2399572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399599 : List Nat := [1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 3]
def baseStart_2399599 : Nat := 118140960795 + 2399599 * 2 ^ 59
def prefixEnd_2399599 : Nat := 4983230072969 + 3 ^ 40 * 2399599 * 2
def baseEnd_2399599 : Nat := 1232147665048262291576951

theorem tailTrace_2399599 : CollatzResearch.WordTrace tailWord_2399599 prefixEnd_2399599 1232147665048262291576951 := by
  unfold tailWord_2399599
  simp only [CollatzResearch.WordTrace]
  refine ⟨87520565633670116726961851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58347043755780077817974567 87520565633670116726961851)
  ·
    refine ⟨131280848450505175090442777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87520565633670116726961851 131280848450505175090442777)
    ·
      refine ⟨98460636337878881317832083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131280848450505175090442777 98460636337878881317832083)
      ·
        refine ⟨147690954506818321976748125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98460636337878881317832083 147690954506818321976748125)
        ·
          refine ⟨55384107940056870741280547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147690954506818321976748125 55384107940056870741280547)
          ·
            refine ⟨83076161910085306111920821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55384107940056870741280547 83076161910085306111920821)
            ·
              refine ⟨7788390179070497447992577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83076161910085306111920821 7788390179070497447992577)
              ·
                refine ⟨5841292634302873085994433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7788390179070497447992577 5841292634302873085994433)
                ·
                  refine ⟨4380969475727154814495825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5841292634302873085994433 4380969475727154814495825)
                  ·
                    refine ⟨3285727106795366110871869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4380969475727154814495825 3285727106795366110871869)
                    ·
                      refine ⟨1232147665048262291576951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3285727106795366110871869 1232147665048262291576951)
                      ·
                        rfl

theorem cell23_2399599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 3].length) (baseStart_2399599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399599 prefixEnd_2399599 := by exact prefixLift 2399599
  have htrace : WordTrace (prefixWord ++ tailWord_2399599) baseStart_2399599 baseEnd_2399599 := by
    simpa [prefixWord, tailWord_2399599, baseEnd_2399599] using wordTrace_append hprefix tailTrace_2399599
  have hstable : (prefixWord ++ tailWord_2399599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399599).length < 2 ^ (prefixWord ++ tailWord_2399599).sum := by decide
  have hdescent : baseEnd_2399599 < baseStart_2399599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399602 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 8]
def baseStart_2399602 : Nat := 118140960795 + 2399602 * 2 ^ 59
def prefixEnd_2399602 : Nat := 4983230072969 + 3 ^ 40 * 2399602 * 2
def baseEnd_2399602 : Nat := 136905467276691753315493

theorem tailTrace_2399602 : CollatzResearch.WordTrace tailWord_2399602 prefixEnd_2399602 136905467276691753315493 := by
  unfold tailWord_2399602
  simp only [CollatzResearch.WordTrace]
  refine ⟨21880168763164812059830265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58347116701772832159547373 21880168763164812059830265)
  ·
    refine ⟨16410126572373609044872699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21880168763164812059830265 16410126572373609044872699)
    ·
      refine ⟨24615189858560413567309049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16410126572373609044872699 24615189858560413567309049)
      ·
        refine ⟨18461392393920310175481787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24615189858560413567309049 18461392393920310175481787)
        ·
          refine ⟨27692088590880465263222681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18461392393920310175481787 27692088590880465263222681)
          ·
            refine ⟨20769066443160348947417011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27692088590880465263222681 20769066443160348947417011)
            ·
              refine ⟨31153599664740523421125517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20769066443160348947417011 31153599664740523421125517)
              ·
                refine ⟨11682599874277696282922069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31153599664740523421125517 11682599874277696282922069)
                ·
                  refine ⟨136905467276691753315493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11682599874277696282922069 136905467276691753315493)
                  ·
                    rfl

theorem cell23_2399602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_2399602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399602 prefixEnd_2399602 := by exact prefixLift 2399602
  have htrace : WordTrace (prefixWord ++ tailWord_2399602) baseStart_2399602 baseEnd_2399602 := by
    simpa [prefixWord, tailWord_2399602, baseEnd_2399602] using wordTrace_append hprefix tailTrace_2399602
  have hstable : (prefixWord ++ tailWord_2399602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399602).length < 2 ^ (prefixWord ++ tailWord_2399602).sum := by decide
  have hdescent : baseEnd_2399602 < baseStart_2399602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399619 : List Nat := [1, 1, 1, 3, 5, 2, 1, 3, 6]
def baseStart_2399619 : Nat := 118140960795 + 2399619 * 2 ^ 59
def prefixEnd_2399619 : Nat := 4983230072969 + 3 ^ 40 * 2399619 * 2
def baseEnd_2399619 : Nat := 136906437184594690369651

theorem tailTrace_2399619 : CollatzResearch.WordTrace tailWord_2399619 prefixEnd_2399619 136906437184594690369651 := by
  unfold tailWord_2399619
  simp only [CollatzResearch.WordTrace]
  refine ⟨87521295093597660142689911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58347530062398440095126607 87521295093597660142689911)
  ·
    refine ⟨131281942640396490214034867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87521295093597660142689911 131281942640396490214034867)
    ·
      refine ⟨196922913960594735321052301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131281942640396490214034867 196922913960594735321052301)
      ·
        refine ⟨73846092735223025745394613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196922913960594735321052301 73846092735223025745394613)
        ·
          refine ⟨6923071193927158663630745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73846092735223025745394613 6923071193927158663630745)
          ·
            refine ⟨5192303395445368997723059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6923071193927158663630745 5192303395445368997723059)
            ·
              refine ⟨7788455093168053496584589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5192303395445368997723059 7788455093168053496584589)
              ·
                refine ⟨2920670659938020061219221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7788455093168053496584589 2920670659938020061219221)
                ·
                  refine ⟨136906437184594690369651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2920670659938020061219221 136906437184594690369651)
                  ·
                    rfl

theorem cell23_2399619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 6].length) (baseStart_2399619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399619 prefixEnd_2399619 := by exact prefixLift 2399619
  have htrace : WordTrace (prefixWord ++ tailWord_2399619) baseStart_2399619 baseEnd_2399619 := by
    simpa [prefixWord, tailWord_2399619, baseEnd_2399619] using wordTrace_append hprefix tailTrace_2399619
  have hstable : (prefixWord ++ tailWord_2399619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399619).length < 2 ^ (prefixWord ++ tailWord_2399619).sum := by decide
  have hdescent : baseEnd_2399619 < baseStart_2399619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399700 : List Nat := [2, 4, 1, 2, 3, 2, 2, 1, 1, 5]
def baseStart_2399700 : Nat := 118140960795 + 2399700 * 2 ^ 59
def prefixEnd_2399700 : Nat := 4983230072969 + 3 ^ 40 * 2399700 * 2
def baseEnd_2399700 : Nat := 410733175531455465471329

theorem tailTrace_2399700 : CollatzResearch.WordTrace tailWord_2399700 prefixEnd_2399700 410733175531455465471329 := by
  unfold tailWord_2399700
  simp only [CollatzResearch.WordTrace]
  refine ⟨43762124703152105488194277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58349499604202807317592369 43762124703152105488194277)
  ·
    refine ⟨8205398381841019779036427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43762124703152105488194277 8205398381841019779036427)
    ·
      refine ⟨12308097572761529668554641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8205398381841019779036427 12308097572761529668554641)
      ·
        refine ⟨9231073179571147251415981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12308097572761529668554641 9231073179571147251415981)
        ·
          refine ⟨3461652442339180219280993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9231073179571147251415981 3461652442339180219280993)
          ·
            refine ⟨2596239331754385164460745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3461652442339180219280993 2596239331754385164460745)
            ·
              refine ⟨1947179498815788873345559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2596239331754385164460745 1947179498815788873345559)
              ·
                refine ⟨2920769248223683310018339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1947179498815788873345559 2920769248223683310018339)
                ·
                  refine ⟨4381153872335524965027509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2920769248223683310018339 4381153872335524965027509)
                  ·
                    refine ⟨410733175531455465471329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4381153872335524965027509 410733175531455465471329)
                    ·
                      rfl

theorem cell23_2399700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_2399700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399700 prefixEnd_2399700 := by exact prefixLift 2399700
  have htrace : WordTrace (prefixWord ++ tailWord_2399700) baseStart_2399700 baseEnd_2399700 := by
    simpa [prefixWord, tailWord_2399700, baseEnd_2399700] using wordTrace_append hprefix tailTrace_2399700
  have hstable : (prefixWord ++ tailWord_2399700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399700).length < 2 ^ (prefixWord ++ tailWord_2399700).sum := by decide
  have hdescent : baseEnd_2399700 < baseStart_2399700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399709 : List Nat := [1, 4, 3, 1, 1, 3, 10]
def baseStart_2399709 : Nat := 118140960795 + 2399709 * 2 ^ 59
def prefixEnd_2399709 : Nat := 4983230072969 + 3 ^ 40 * 2399709 * 2
def baseEnd_2399709 : Nat := 15212396887904405693845

theorem tailTrace_2399709 : CollatzResearch.WordTrace tailWord_2399709 prefixEnd_2399709 15212396887904405693845 := by
  unfold tailWord_2399709
  simp only [CollatzResearch.WordTrace]
  refine ⟨87524577663271605513466181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58349718442181070342310787 87524577663271605513466181)
  ·
    refine ⟨16410858311863426033774909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87524577663271605513466181 16410858311863426033774909)
    ·
      refine ⟨6154071866948784762665591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16410858311863426033774909 6154071866948784762665591)
      ·
        refine ⟨9231107800423177143998387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6154071866948784762665591 9231107800423177143998387)
        ·
          refine ⟨13846661700634765715997581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9231107800423177143998387 13846661700634765715997581)
          ·
            refine ⟨5192498137738037143499093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13846661700634765715997581 5192498137738037143499093)
            ·
              refine ⟨15212396887904405693845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5192498137738037143499093 15212396887904405693845)
              ·
                rfl

theorem cell23_2399709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 10].length) (baseStart_2399709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399709 prefixEnd_2399709 := by exact prefixLift 2399709
  have htrace : WordTrace (prefixWord ++ tailWord_2399709) baseStart_2399709 baseEnd_2399709 := by
    simpa [prefixWord, tailWord_2399709, baseEnd_2399709] using wordTrace_append hprefix tailTrace_2399709
  have hstable : (prefixWord ++ tailWord_2399709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399709).length < 2 ^ (prefixWord ++ tailWord_2399709).sum := by decide
  have hdescent : baseEnd_2399709 < baseStart_2399709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399713 : List Nat := [1, 2, 3, 1, 2, 5, 1, 2, 2, 4]
def baseStart_2399713 : Nat := 118140960795 + 2399713 * 2 ^ 59
def prefixEnd_2399713 : Nat := 4983230072969 + 3 ^ 40 * 2399713 * 2
def baseEnd_2399713 : Nat := 410735400614291615183809

theorem tailTrace_2399713 : CollatzResearch.WordTrace tailWord_2399713 prefixEnd_2399713 410735400614291615183809 := by
  unfold tailWord_2399713
  simp only [CollatzResearch.WordTrace]
  refine ⟨87524723555257114196611793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58349815703504742797741195 87524723555257114196611793)
  ·
    refine ⟨65643542666442835647458845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87524723555257114196611793 65643542666442835647458845)
    ·
      refine ⟨24616328499916063367797067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65643542666442835647458845 24616328499916063367797067)
      ·
        refine ⟨36924492749874095051695601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24616328499916063367797067 36924492749874095051695601)
        ·
          refine ⟨27693369562405571288771701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36924492749874095051695601 27693369562405571288771701)
          ·
            refine ⟨2596253396475522308322347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27693369562405571288771701 2596253396475522308322347)
            ·
              refine ⟨3894380094713283462483521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2596253396475522308322347 3894380094713283462483521)
              ·
                refine ⟨2920785071034962596862641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3894380094713283462483521 2920785071034962596862641)
                ·
                  refine ⟨2190588803276221947646981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2920785071034962596862641 2190588803276221947646981)
                  ·
                    refine ⟨410735400614291615183809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2190588803276221947646981 410735400614291615183809)
                    ·
                      rfl

theorem cell23_2399713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_2399713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399713 prefixEnd_2399713 := by exact prefixLift 2399713
  have htrace : WordTrace (prefixWord ++ tailWord_2399713) baseStart_2399713 baseEnd_2399713 := by
    simpa [prefixWord, tailWord_2399713, baseEnd_2399713] using wordTrace_append hprefix tailTrace_2399713
  have hstable : (prefixWord ++ tailWord_2399713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399713).length < 2 ^ (prefixWord ++ tailWord_2399713).sum := by decide
  have hdescent : baseEnd_2399713 < baseStart_2399713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399720 : List Nat := [2, 1, 4, 1, 1, 2, 1, 6, 1, 2, 2]
def baseStart_2399720 : Nat := 118140960795 + 2399720 * 2 ^ 59
def prefixEnd_2399720 : Nat := 4983230072969 + 3 ^ 40 * 2399720 * 2
def baseEnd_2399720 : Nat := 1232209796207456318163895

theorem tailTrace_2399720 : CollatzResearch.WordTrace tailWord_2399720 prefixEnd_2399720 1232209796207456318163895 := by
  unfold tailWord_2399720
  simp only [CollatzResearch.WordTrace]
  refine ⟨43762489433115877196058307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58349985910821169594744409 43762489433115877196058307)
  ·
    refine ⟨65643734149673815794087461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43762489433115877196058307 65643734149673815794087461)
    ·
      refine ⟨12308200153063840461391399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65643734149673815794087461 12308200153063840461391399)
      ·
        refine ⟨18462300229595760692087099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12308200153063840461391399 18462300229595760692087099)
        ·
          refine ⟨27693450344393641038130649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18462300229595760692087099 27693450344393641038130649)
          ·
            refine ⟨20770087758295230778597987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27693450344393641038130649 20770087758295230778597987)
            ·
              refine ⟨31155131637442846167896981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20770087758295230778597987 31155131637442846167896981)
              ·
                refine ⟨1460396795505133414120171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31155131637442846167896981 1460396795505133414120171)
                ·
                  refine ⟨2190595193257700121180257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1460396795505133414120171 2190595193257700121180257)
                  ·
                    refine ⟨1642946394943275090885193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2190595193257700121180257 1642946394943275090885193)
                    ·
                      refine ⟨1232209796207456318163895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1642946394943275090885193 1232209796207456318163895)
                      ·
                        rfl

theorem cell23_2399720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_2399720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399720 prefixEnd_2399720 := by exact prefixLift 2399720
  have htrace : WordTrace (prefixWord ++ tailWord_2399720) baseStart_2399720 baseEnd_2399720 := by
    simpa [prefixWord, tailWord_2399720, baseEnd_2399720] using wordTrace_append hprefix tailTrace_2399720
  have hstable : (prefixWord ++ tailWord_2399720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399720).length < 2 ^ (prefixWord ++ tailWord_2399720).sum := by decide
  have hdescent : baseEnd_2399720 < baseStart_2399720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399730 : List Nat := [3, 2, 1, 4, 1, 2, 3, 1, 2, 4]
def baseStart_2399730 : Nat := 118140960795 + 2399730 * 2 ^ 59
def prefixEnd_2399730 : Nat := 4983230072969 + 3 ^ 40 * 2399730 * 2
def baseEnd_2399730 : Nat := 410738310338000426346283

theorem tailTrace_2399730 : CollatzResearch.WordTrace tailWord_2399730 prefixEnd_2399730 410738310338000426346283 := by
  unfold tailWord_2399730
  simp only [CollatzResearch.WordTrace]
  refine ⟨21881335899048881524995161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58350229064130350733320429 21881335899048881524995161)
  ·
    refine ⟨16411001924286661143746371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21881335899048881524995161 16411001924286661143746371)
    ·
      refine ⟨24616502886429991715619557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16411001924286661143746371 24616502886429991715619557)
      ·
        refine ⟨4615594291205623446678667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24616502886429991715619557 4615594291205623446678667)
        ·
          refine ⟨6923391436808435170018001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4615594291205623446678667 6923391436808435170018001)
          ·
            refine ⟨5192543577606326377513501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6923391436808435170018001 5192543577606326377513501)
            ·
              refine ⟨1947203841602372391567563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5192543577606326377513501 1947203841602372391567563)
              ·
                refine ⟨2920805762403558587351345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1947203841602372391567563 2920805762403558587351345)
                ·
                  refine ⟨2190604321802668940513509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2920805762403558587351345 2190604321802668940513509)
                  ·
                    refine ⟨410738310338000426346283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2190604321802668940513509 410738310338000426346283)
                    ·
                      rfl

theorem cell23_2399730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_2399730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399730 prefixEnd_2399730 := by exact prefixLift 2399730
  have htrace : WordTrace (prefixWord ++ tailWord_2399730) baseStart_2399730 baseEnd_2399730 := by
    simpa [prefixWord, tailWord_2399730, baseEnd_2399730] using wordTrace_append hprefix tailTrace_2399730
  have hstable : (prefixWord ++ tailWord_2399730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399730).length < 2 ^ (prefixWord ++ tailWord_2399730).sum := by decide
  have hdescent : baseEnd_2399730 < baseStart_2399730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399733 : List Nat := [1, 3, 5, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_2399733 : Nat := 118140960795 + 2399733 * 2 ^ 59
def prefixEnd_2399733 : Nat := 4983230072969 + 3 ^ 40 * 2399733 * 2
def baseEnd_2399733 : Nat := 1232216471455964767301335

theorem tailTrace_2399733 : CollatzResearch.WordTrace tailWord_2399733 prefixEnd_2399733 1232216471455964767301335 := by
  unfold tailWord_2399733
  simp only [CollatzResearch.WordTrace]
  refine ⟨87525453015184657612339853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58350302010123105074893235 87525453015184657612339853)
  ·
    refine ⟨32822044880694246604627445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87525453015184657612339853 32822044880694246604627445)
    ·
      refine ⟨3077066707565085619183823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32822044880694246604627445 3077066707565085619183823)
      ·
        refine ⟨4615600061347628428775735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3077066707565085619183823 4615600061347628428775735)
        ·
          refine ⟨6923400092021442643163603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4615600061347628428775735 6923400092021442643163603)
          ·
            refine ⟨10385100138032163964745405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6923400092021442643163603 10385100138032163964745405)
            ·
              refine ⟨3894412551762061486779527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10385100138032163964745405 3894412551762061486779527)
              ·
                refine ⟨5841618827643092230169291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3894412551762061486779527 5841618827643092230169291)
                ·
                  refine ⟨8762428241464638345253937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5841618827643092230169291 8762428241464638345253937)
                  ·
                    refine ⟨6571821181098478758940453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8762428241464638345253937 6571821181098478758940453)
                    ·
                      refine ⟨1232216471455964767301335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6571821181098478758940453 1232216471455964767301335)
                      ·
                        rfl

theorem cell23_2399733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_2399733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399733 prefixEnd_2399733 := by exact prefixLift 2399733
  have htrace : WordTrace (prefixWord ++ tailWord_2399733) baseStart_2399733 baseEnd_2399733 := by
    simpa [prefixWord, tailWord_2399733, baseEnd_2399733] using wordTrace_append hprefix tailTrace_2399733
  have hstable : (prefixWord ++ tailWord_2399733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399733).length < 2 ^ (prefixWord ++ tailWord_2399733).sum := by decide
  have hdescent : baseEnd_2399733 < baseStart_2399733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399736 : List Nat := [2, 1, 2, 1, 1, 5, 3, 1, 1, 3, 3]
def baseStart_2399736 : Nat := 118140960795 + 2399736 * 2 ^ 59
def prefixEnd_2399736 : Nat := 4983230072969 + 3 ^ 40 * 2399736 * 2
def baseEnd_2399736 : Nat := 1232218011897928255563821

theorem tailTrace_2399736 : CollatzResearch.WordTrace tailWord_2399736 prefixEnd_2399736 1232218011897928255563821 := by
  unfold tailWord_2399736
  simp only [CollatzResearch.WordTrace]
  refine ⟨43762781217086894562349531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58350374956115859416466041 43762781217086894562349531)
  ·
    refine ⟨65644171825630341843524297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43762781217086894562349531 65644171825630341843524297)
    ·
      refine ⟨49233128869222756382643223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65644171825630341843524297 49233128869222756382643223)
      ·
        refine ⟨73849693303834134573964835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49233128869222756382643223 73849693303834134573964835)
        ·
          refine ⟨110774539955751201860947253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73849693303834134573964835 110774539955751201860947253)
          ·
            refine ⟨10385113120851675174463805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110774539955751201860947253 10385113120851675174463805)
            ·
              refine ⟨3894417420319378190423927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10385113120851675174463805 3894417420319378190423927)
              ·
                refine ⟨5841626130479067285635891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3894417420319378190423927 5841626130479067285635891)
                ·
                  refine ⟨8762439195718600928453837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5841626130479067285635891 8762439195718600928453837)
                  ·
                    refine ⟨3285914698394475348170189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8762439195718600928453837 3285914698394475348170189)
                    ·
                      refine ⟨1232218011897928255563821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3285914698394475348170189 1232218011897928255563821)
                      ·
                        rfl

theorem cell23_2399736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 1, 3, 3].length) (baseStart_2399736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399736 prefixEnd_2399736 := by exact prefixLift 2399736
  have htrace : WordTrace (prefixWord ++ tailWord_2399736) baseStart_2399736 baseEnd_2399736 := by
    simpa [prefixWord, tailWord_2399736, baseEnd_2399736] using wordTrace_append hprefix tailTrace_2399736
  have hstable : (prefixWord ++ tailWord_2399736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399736).length < 2 ^ (prefixWord ++ tailWord_2399736).sum := by decide
  have hdescent : baseEnd_2399736 < baseStart_2399736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399763 : List Nat := [1, 1, 1, 2, 1, 6, 2, 3, 1, 3, 2]
def baseStart_2399763 : Nat := 118140960795 + 2399763 * 2 ^ 59
def prefixEnd_2399763 : Nat := 4983230072969 + 3 ^ 40 * 2399763 * 2
def baseEnd_2399763 : Nat := 1232231875875599649926197

theorem tailTrace_2399763 : CollatzResearch.WordTrace tailWord_2399763 prefixEnd_2399763 1232231875875599649926197 := by
  unfold tailWord_2399763
  simp only [CollatzResearch.WordTrace]
  refine ⟨87526547205075972735931943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58351031470050648490621295 87526547205075972735931943)
  ·
    refine ⟨131289820807613959103897915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87526547205075972735931943 131289820807613959103897915)
    ·
      refine ⟨196934731211420938655846873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131289820807613959103897915 196934731211420938655846873)
      ·
        refine ⟨147701048408565703991885155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196934731211420938655846873 147701048408565703991885155)
        ·
          refine ⟨221551572612848555987827733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147701048408565703991885155 221551572612848555987827733)
          ·
            refine ⟨10385229966227276061929425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 221551572612848555987827733 10385229966227276061929425)
            ·
              refine ⟨7788922474670457046447069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10385229966227276061929425 7788922474670457046447069)
              ·
                refine ⟨2920845928001421392417651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7788922474670457046447069 2920845928001421392417651)
                ·
                  refine ⟨4381268892002132088626477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2920845928001421392417651 4381268892002132088626477)
                  ·
                    refine ⟨1642975834500799533234929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4381268892002132088626477 1642975834500799533234929)
                    ·
                      refine ⟨1232231875875599649926197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1642975834500799533234929 1232231875875599649926197)
                      ·
                        rfl

theorem cell23_2399763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 3, 2].length) (baseStart_2399763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399763 prefixEnd_2399763 := by exact prefixLift 2399763
  have htrace : WordTrace (prefixWord ++ tailWord_2399763) baseStart_2399763 baseEnd_2399763 := by
    simpa [prefixWord, tailWord_2399763, baseEnd_2399763] using wordTrace_append hprefix tailTrace_2399763
  have hstable : (prefixWord ++ tailWord_2399763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399763).length < 2 ^ (prefixWord ++ tailWord_2399763).sum := by decide
  have hdescent : baseEnd_2399763 < baseStart_2399763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399829 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 3, 7]
def baseStart_2399829 : Nat := 118140960795 + 2399829 * 2 ^ 59
def prefixEnd_2399829 : Nat := 4983230072969 + 3 ^ 40 * 2399829 * 2
def baseEnd_2399829 : Nat := 410755255199598797233631

theorem tailTrace_2399829 : CollatzResearch.WordTrace tailWord_2399829 prefixEnd_2399829 410755255199598797233631 := by
  unfold tailWord_2399829
  simp only [CollatzResearch.WordTrace]
  refine ⟨87528954422836866007834541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58352636281891244005223027 87528954422836866007834541)
  ·
    refine ⟨32823357908563824752937953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87528954422836866007834541 32823357908563824752937953)
    ·
      refine ⟨24617518431422868564703465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32823357908563824752937953 24617518431422868564703465)
      ·
        refine ⟨18463138823567151423527599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24617518431422868564703465 18463138823567151423527599)
        ·
          refine ⟨27694708235350727135291399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18463138823567151423527599 27694708235350727135291399)
          ·
            refine ⟨41542062353026090702937099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27694708235350727135291399 41542062353026090702937099)
            ·
              refine ⟨62313093529539136054405649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41542062353026090702937099 62313093529539136054405649)
              ·
                refine ⟨46734820147154352040804237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62313093529539136054405649 46734820147154352040804237)
                ·
                  refine ⟨17525557555182882015301589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46734820147154352040804237 17525557555182882015301589)
                  ·
                    refine ⟨410755255199598797233631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17525557555182882015301589 410755255199598797233631)
                    ·
                      rfl

theorem cell23_2399829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_2399829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399829 prefixEnd_2399829 := by exact prefixLift 2399829
  have htrace : WordTrace (prefixWord ++ tailWord_2399829) baseStart_2399829 baseEnd_2399829 := by
    simpa [prefixWord, tailWord_2399829, baseEnd_2399829] using wordTrace_append hprefix tailTrace_2399829
  have hstable : (prefixWord ++ tailWord_2399829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399829).length < 2 ^ (prefixWord ++ tailWord_2399829).sum := by decide
  have hdescent : baseEnd_2399829 < baseStart_2399829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399866 : List Nat := [3, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4]
def baseStart_2399866 : Nat := 118140960795 + 2399866 * 2 ^ 59
def prefixEnd_2399866 : Nat := 4983230072969 + 3 ^ 40 * 2399866 * 2
def baseEnd_2399866 : Nat := 1232284764383012746938223

theorem tailTrace_2399866 : CollatzResearch.WordTrace tailWord_2399866 prefixEnd_2399866 1232284764383012746938223 := by
  unfold tailWord_2399866
  simp only [CollatzResearch.WordTrace]
  refine ⟨21882575980925705331732863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58353535949135214217954301 21882575980925705331732863)
  ·
    refine ⟨32823863971388557997599295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21882575980925705331732863 32823863971388557997599295)
    ·
      refine ⟨49235795957082836996398943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32823863971388557997599295 49235795957082836996398943)
      ·
        refine ⟨73853693935624255494598415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49235795957082836996398943 73853693935624255494598415)
        ·
          refine ⟨110780540903436383241897623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73853693935624255494598415 110780540903436383241897623)
          ·
            refine ⟨166170811355154574862846435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110780540903436383241897623 166170811355154574862846435)
            ·
              refine ⟨249256217032731862294269653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166170811355154574862846435 249256217032731862294269653)
              ·
                refine ⟨5841942586704653022521945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 249256217032731862294269653 5841942586704653022521945)
                ·
                  refine ⟨4381456940028489766891459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5841942586704653022521945 4381456940028489766891459)
                  ·
                    refine ⟨6572185410042734650337189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4381456940028489766891459 6572185410042734650337189)
                    ·
                      refine ⟨1232284764383012746938223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6572185410042734650337189 1232284764383012746938223)
                      ·
                        rfl

theorem cell23_2399866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_2399866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399866 prefixEnd_2399866 := by exact prefixLift 2399866
  have htrace : WordTrace (prefixWord ++ tailWord_2399866) baseStart_2399866 baseEnd_2399866 := by
    simpa [prefixWord, tailWord_2399866, baseEnd_2399866] using wordTrace_append hprefix tailTrace_2399866
  have hstable : (prefixWord ++ tailWord_2399866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399866).length < 2 ^ (prefixWord ++ tailWord_2399866).sum := by decide
  have hdescent : baseEnd_2399866 < baseStart_2399866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399927 : List Nat := [1, 1, 3, 1, 5, 3, 1, 3, 1, 4]
def baseStart_2399927 : Nat := 118140960795 + 2399927 * 2 ^ 59
def prefixEnd_2399927 : Nat := 4983230072969 + 3 ^ 40 * 2399927 * 2
def baseEnd_2399927 : Nat := 410772028900979002758481

theorem tailTrace_2399927 : CollatzResearch.WordTrace tailWord_2399927 prefixEnd_2399927 410772028900979002758481 := by
  unfold tailWord_2399927
  simp only [CollatzResearch.WordTrace]
  refine ⟨87532528776481828744902035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58355019184321219163268023 87532528776481828744902035)
  ·
    refine ⟨131298793164722743117353053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87532528776481828744902035 131298793164722743117353053)
    ·
      refine ⟨49237047436771028669007395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131298793164722743117353053 49237047436771028669007395)
      ·
        refine ⟨73855571155156543003511093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49237047436771028669007395 73855571155156543003511093)
        ·
          refine ⟨6923959795795925906579165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73855571155156543003511093 6923959795795925906579165)
          ·
            refine ⟨2596484923423472214967187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6923959795795925906579165 2596484923423472214967187)
            ·
              refine ⟨3894727385135208322450781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2596484923423472214967187 3894727385135208322450781)
              ·
                refine ⟨1460522769425703120919043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3894727385135208322450781 1460522769425703120919043)
                ·
                  refine ⟨2190784154138554681378565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1460522769425703120919043 2190784154138554681378565)
                  ·
                    refine ⟨410772028900979002758481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2190784154138554681378565 410772028900979002758481)
                    ·
                      rfl

theorem cell23_2399927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 1, 4].length) (baseStart_2399927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399927 prefixEnd_2399927 := by exact prefixLift 2399927
  have htrace : WordTrace (prefixWord ++ tailWord_2399927) baseStart_2399927 baseEnd_2399927 := by
    simpa [prefixWord, tailWord_2399927, baseEnd_2399927] using wordTrace_append hprefix tailTrace_2399927
  have hstable : (prefixWord ++ tailWord_2399927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399927).length < 2 ^ (prefixWord ++ tailWord_2399927).sum := by decide
  have hdescent : baseEnd_2399927 < baseStart_2399927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399973 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 3, 1, 4]
def baseStart_2399973 : Nat := 118140960795 + 2399973 * 2 ^ 59
def prefixEnd_2399973 : Nat := 4983230072969 + 3 ^ 40 * 2399973 * 2
def baseEnd_2399973 : Nat := 1232339706813043828300231

theorem tailTrace_2399973 : CollatzResearch.WordTrace tailWord_2399973 prefixEnd_2399973 1232339706813043828300231 := by
  unfold tailWord_2399973
  simp only [CollatzResearch.WordTrace]
  refine ⟨87534206534315178601076573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58356137689543452400717715 87534206534315178601076573)
  ·
    refine ⟨32825327450368191975403715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87534206534315178601076573 32825327450368191975403715)
    ·
      refine ⟨49237991175552287963105573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32825327450368191975403715 49237991175552287963105573)
      ·
        refine ⟨9232123345416053993082295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49237991175552287963105573 9232123345416053993082295)
        ·
          refine ⟨13848185018124080989623443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9232123345416053993082295 13848185018124080989623443)
          ·
            refine ⟨20772277527186121484435165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13848185018124080989623443 20772277527186121484435165)
            ·
              refine ⟨7789604072694795556663187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20772277527186121484435165 7789604072694795556663187)
              ·
                refine ⟨11684406109042193334994781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7789604072694795556663187 11684406109042193334994781)
                ·
                  refine ⟨4381652290890822500623043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11684406109042193334994781 4381652290890822500623043)
                  ·
                    refine ⟨6572478436336233750934565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4381652290890822500623043 6572478436336233750934565)
                    ·
                      refine ⟨1232339706813043828300231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6572478436336233750934565 1232339706813043828300231)
                      ·
                        rfl

theorem cell23_2399973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_2399973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399973 prefixEnd_2399973 := by exact prefixLift 2399973
  have htrace : WordTrace (prefixWord ++ tailWord_2399973) baseStart_2399973 baseEnd_2399973 := by
    simpa [prefixWord, tailWord_2399973, baseEnd_2399973] using wordTrace_append hprefix tailTrace_2399973
  have hstable : (prefixWord ++ tailWord_2399973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399973).length < 2 ^ (prefixWord ++ tailWord_2399973).sum := by decide
  have hdescent : baseEnd_2399973 < baseStart_2399973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400040 : List Nat := [2, 1, 5, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_2400040 : Nat := 118140960795 + 2400040 * 2 ^ 59
def prefixEnd_2400040 : Nat := 4983230072969 + 3 ^ 40 * 2400040 * 2
def baseEnd_2400040 : Nat := 1232374110016895066162423

theorem tailTrace_2400040 : CollatzResearch.WordTrace tailWord_2400040 prefixEnd_2400040 1232374110016895066162423 := by
  unfold tailWord_2400040
  simp only [CollatzResearch.WordTrace]
  refine ⟨43768325112536224521882787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58357766816714966029177049 43768325112536224521882787)
  ·
    refine ⟨65652487668804336782824181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43768325112536224521882787 65652487668804336782824181)
    ·
      refine ⟨6154920718950406573389767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65652487668804336782824181 6154920718950406573389767)
      ·
        refine ⟨9232381078425609860084651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6154920718950406573389767 9232381078425609860084651)
        ·
          refine ⟨13848571617638414790126977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9232381078425609860084651 13848571617638414790126977)
          ·
            refine ⟨10386428713228811092595233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13848571617638414790126977 10386428713228811092595233)
            ·
              refine ⟨7789821534921608319446425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10386428713228811092595233 7789821534921608319446425)
              ·
                refine ⟨5842366151191206239584819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7789821534921608319446425 5842366151191206239584819)
                ·
                  refine ⟨8763549226786809359377229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5842366151191206239584819 8763549226786809359377229)
                  ·
                    refine ⟨3286330960045053509766461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8763549226786809359377229 3286330960045053509766461)
                    ·
                      refine ⟨1232374110016895066162423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3286330960045053509766461 1232374110016895066162423)
                      ·
                        rfl

theorem cell23_2400040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_2400040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400040 prefixEnd_2400040 := by exact prefixLift 2400040
  have htrace : WordTrace (prefixWord ++ tailWord_2400040) baseStart_2400040 baseEnd_2400040 := by
    simpa [prefixWord, tailWord_2400040, baseEnd_2400040] using wordTrace_append hprefix tailTrace_2400040
  have hstable : (prefixWord ++ tailWord_2400040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400040).length < 2 ^ (prefixWord ++ tailWord_2400040).sum := by decide
  have hdescent : baseEnd_2400040 < baseStart_2400040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400084 : List Nat := [2, 4, 1, 1, 3, 2, 2, 2, 1, 3, 2]
def baseStart_2400084 : Nat := 118140960795 + 2400084 * 2 ^ 59
def prefixEnd_2400084 : Nat := 4983230072969 + 3 ^ 40 * 2400084 * 2
def baseEnd_2400084 : Nat := 1232396703165692894012221

theorem tailTrace_2400084 : CollatzResearch.WordTrace tailWord_2400084 prefixEnd_2400084 1232396703165692894012221 := by
  unfold tailWord_2400084
  simp only [CollatzResearch.WordTrace]
  refine ⟨43769127518456522279183653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58358836691275363038911537 43769127518456522279183653)
  ·
    refine ⟨8206711409710597927346935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43769127518456522279183653 8206711409710597927346935)
    ·
      refine ⟨12310067114565896891020403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8206711409710597927346935 12310067114565896891020403)
      ·
        refine ⟨18465100671848845336530605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12310067114565896891020403 18465100671848845336530605)
        ·
          refine ⟨6924412751943317001198977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18465100671848845336530605 6924412751943317001198977)
          ·
            refine ⟨5193309563957487750899233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6924412751943317001198977 5193309563957487750899233)
            ·
              refine ⟨3894982172968115813174425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5193309563957487750899233 3894982172968115813174425)
              ·
                refine ⟨2921236629726086859880819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3894982172968115813174425 2921236629726086859880819)
                ·
                  refine ⟨4381854944589130289821229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2921236629726086859880819 4381854944589130289821229)
                  ·
                    refine ⟨1643195604220923858682961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4381854944589130289821229 1643195604220923858682961)
                    ·
                      refine ⟨1232396703165692894012221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1643195604220923858682961 1232396703165692894012221)
                      ·
                        rfl

theorem cell23_2400084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_2400084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400084 prefixEnd_2400084 := by exact prefixLift 2400084
  have htrace : WordTrace (prefixWord ++ tailWord_2400084) baseStart_2400084 baseEnd_2400084 := by
    simpa [prefixWord, tailWord_2400084, baseEnd_2400084] using wordTrace_append hprefix tailTrace_2400084
  have hstable : (prefixWord ++ tailWord_2400084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400084).length < 2 ^ (prefixWord ++ tailWord_2400084).sum := by decide
  have hdescent : baseEnd_2400084 < baseStart_2400084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400100 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 2, 1, 5]
def baseStart_2400100 : Nat := 118140960795 + 2400100 * 2 ^ 59
def prefixEnd_2400100 : Nat := 4983230072969 + 3 ^ 40 * 2400100 * 2
def baseEnd_2400100 : Nat := 1232404918856164831412147

theorem tailTrace_2400100 : CollatzResearch.WordTrace tailWord_2400100 prefixEnd_2400100 1232404918856164831412147 := by
  unfold tailWord_2400100
  simp only [CollatzResearch.WordTrace]
  refine ⟨43769419302427539645474877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58359225736570052860633169 43769419302427539645474877)
  ·
    refine ⟨16413532238410327367053079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43769419302427539645474877 16413532238410327367053079)
    ·
      refine ⟨24620298357615491050579619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16413532238410327367053079 24620298357615491050579619)
      ·
        refine ⟨36930447536423236575869429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24620298357615491050579619 36930447536423236575869429)
        ·
          refine ⟨3462229456539678428987759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36930447536423236575869429 3462229456539678428987759)
          ·
            refine ⟨5193344184809517643481639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3462229456539678428987759 5193344184809517643481639)
            ·
              refine ⟨7790016277214276465222459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5193344184809517643481639 7790016277214276465222459)
              ·
                refine ⟨11685024415821414697833689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7790016277214276465222459 11685024415821414697833689)
                ·
                  refine ⟨8763768311866061023375267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11685024415821414697833689 8763768311866061023375267)
                  ·
                    refine ⟨13145652467799091535062901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8763768311866061023375267 13145652467799091535062901)
                    ·
                      refine ⟨1232404918856164831412147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13145652467799091535062901 1232404918856164831412147)
                      ·
                        rfl

theorem cell23_2400100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_2400100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400100 prefixEnd_2400100 := by exact prefixLift 2400100
  have htrace : WordTrace (prefixWord ++ tailWord_2400100) baseStart_2400100 baseEnd_2400100 := by
    simpa [prefixWord, tailWord_2400100, baseEnd_2400100] using wordTrace_append hprefix tailTrace_2400100
  have hstable : (prefixWord ++ tailWord_2400100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400100).length < 2 ^ (prefixWord ++ tailWord_2400100).sum := by decide
  have hdescent : baseEnd_2400100 < baseStart_2400100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400131 : List Nat := [1, 1, 1, 3, 4, 4, 2, 1, 2, 2, 2]
def baseStart_2400131 : Nat := 118140960795 + 2400131 * 2 ^ 59
def prefixEnd_2400131 : Nat := 4983230072969 + 3 ^ 40 * 2400131 * 2
def baseEnd_2400131 : Nat := 1232420836756454210124505

theorem tailTrace_2400131 : CollatzResearch.WordTrace tailWord_2400131 prefixEnd_2400131 1232420836756454210124505 := by
  unfold tailWord_2400131
  simp only [CollatzResearch.WordTrace]
  refine ⟨87539969267742771585328247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58359979511828514390218831 87539969267742771585328247)
  ·
    refine ⟨131309953901614157377992371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87539969267742771585328247 131309953901614157377992371)
    ·
      refine ⟨196964930852421236066988557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131309953901614157377992371 196964930852421236066988557)
      ·
        refine ⟨73861849069657963525120709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196964930852421236066988557 73861849069657963525120709)
        ·
          refine ⟨13849096700560868160960133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73861849069657963525120709 13849096700560868160960133)
          ·
            refine ⟨2596705631355162780180025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13849096700560868160960133 2596705631355162780180025)
            ·
              refine ⟨1947529223516372085135019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2596705631355162780180025 1947529223516372085135019)
              ·
                refine ⟨2921293835274558127702529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1947529223516372085135019 2921293835274558127702529)
                ·
                  refine ⟨2190970376455918595776897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2921293835274558127702529 2190970376455918595776897)
                  ·
                    refine ⟨1643227782341938946832673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2190970376455918595776897 1643227782341938946832673)
                    ·
                      refine ⟨1232420836756454210124505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1643227782341938946832673 1232420836756454210124505)
                      ·
                        rfl

theorem cell23_2400131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 2, 2, 2].length) (baseStart_2400131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400131 prefixEnd_2400131 := by exact prefixLift 2400131
  have htrace : WordTrace (prefixWord ++ tailWord_2400131) baseStart_2400131 baseEnd_2400131 := by
    simpa [prefixWord, tailWord_2400131, baseEnd_2400131] using wordTrace_append hprefix tailTrace_2400131
  have hstable : (prefixWord ++ tailWord_2400131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400131).length < 2 ^ (prefixWord ++ tailWord_2400131).sum := by decide
  have hdescent : baseEnd_2400131 < baseStart_2400131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400133 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 4, 5]
def baseStart_2400133 : Nat := 118140960795 + 2400133 * 2 ^ 59
def prefixEnd_2400133 : Nat := 4983230072969 + 3 ^ 40 * 2400133 * 2
def baseEnd_2400133 : Nat := 410807287905921067433165

theorem tailTrace_2400133 : CollatzResearch.WordTrace tailWord_2400133 prefixEnd_2400133 410807287905921067433165 := by
  unfold tailWord_2400133
  simp only [CollatzResearch.WordTrace]
  refine ⟨87540042213735525926901053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58360028142490350617934035 87540042213735525926901053)
  ·
    refine ⟨32827515830150822222587895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87540042213735525926901053 32827515830150822222587895)
    ·
      refine ⟨49241273745226233333881843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32827515830150822222587895 49241273745226233333881843)
      ·
        refine ⟨73861910617839350000822765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49241273745226233333881843 73861910617839350000822765)
        ·
          refine ⟨27698216481689756250308537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73861910617839350000822765 27698216481689756250308537)
          ·
            refine ⟨20773662361267317187731403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27698216481689756250308537 20773662361267317187731403)
            ·
              refine ⟨31160493541900975781597105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20773662361267317187731403 31160493541900975781597105)
              ·
                refine ⟨23370370156425731836197829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31160493541900975781597105 23370370156425731836197829)
                ·
                  refine ⟨4381944404329824719287093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23370370156425731836197829 4381944404329824719287093)
                  ·
                    refine ⟨410807287905921067433165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4381944404329824719287093 410807287905921067433165)
                    ·
                      rfl

theorem cell23_2400133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_2400133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400133 prefixEnd_2400133 := by exact prefixLift 2400133
  have htrace : WordTrace (prefixWord ++ tailWord_2400133) baseStart_2400133 baseEnd_2400133 := by
    simpa [prefixWord, tailWord_2400133, baseEnd_2400133] using wordTrace_append hprefix tailTrace_2400133
  have hstable : (prefixWord ++ tailWord_2400133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400133).length < 2 ^ (prefixWord ++ tailWord_2400133).sum := by decide
  have hdescent : baseEnd_2400133 < baseStart_2400133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400153 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 1, 3, 4]
def baseStart_2400153 : Nat := 118140960795 + 2400153 * 2 ^ 59
def prefixEnd_2400153 : Nat := 4983230072969 + 3 ^ 40 * 2400153 * 2
def baseEnd_2400153 : Nat := 1232432133330853124049403

theorem tailTrace_2400153 : CollatzResearch.WordTrace tailWord_2400153 prefixEnd_2400153 1232432133330853124049403 := by
  unfold tailWord_2400153
  simp only [CollatzResearch.WordTrace]
  refine ⟨87540771673663069342629113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58360514449108712895086075 87540771673663069342629113)
  ·
    refine ⟨65655578755247302006971835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87540771673663069342629113 65655578755247302006971835)
    ·
      refine ⟨98483368132870953010457753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65655578755247302006971835 98483368132870953010457753)
      ·
        refine ⟨73862526099653214757843315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98483368132870953010457753 73862526099653214757843315)
        ·
          refine ⟨110793789149479822136764973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73862526099653214757843315 110793789149479822136764973)
          ·
            refine ⟨41547670931054933301286865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110793789149479822136764973 41547670931054933301286865)
            ·
              refine ⟨31160753198291199975965149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41547670931054933301286865 31160753198291199975965149)
              ·
                refine ⟨11685282449359199990986931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31160753198291199975965149 11685282449359199990986931)
                ·
                  refine ⟨17527923674038799986480397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11685282449359199990986931 17527923674038799986480397)
                  ·
                    refine ⟨6572971377764549994930149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17527923674038799986480397 6572971377764549994930149)
                    ·
                      refine ⟨1232432133330853124049403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6572971377764549994930149 1232432133330853124049403)
                      ·
                        rfl

theorem cell23_2400153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_2400153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400153 prefixEnd_2400153 := by exact prefixLift 2400153
  have htrace : WordTrace (prefixWord ++ tailWord_2400153) baseStart_2400153 baseEnd_2400153 := by
    simpa [prefixWord, tailWord_2400153, baseEnd_2400153] using wordTrace_append hprefix tailTrace_2400153
  have hstable : (prefixWord ++ tailWord_2400153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400153).length < 2 ^ (prefixWord ++ tailWord_2400153).sum := by decide
  have hdescent : baseEnd_2400153 < baseStart_2400153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400183 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 4]
def baseStart_2400183 : Nat := 118140960795 + 2400183 * 2 ^ 59
def prefixEnd_2400183 : Nat := 4983230072969 + 3 ^ 40 * 2400183 * 2
def baseEnd_2400183 : Nat := 1232447537750488006674265

theorem tailTrace_2400183 : CollatzResearch.WordTrace tailWord_2400183 prefixEnd_2400183 1232447537750488006674265 := by
  unfold tailWord_2400183
  simp only [CollatzResearch.WordTrace]
  refine ⟨87541865863554384466221203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58361243909036256310814135 87541865863554384466221203)
  ·
    refine ⟨131312798795331576699331805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87541865863554384466221203 131312798795331576699331805)
    ·
      refine ⟨49242299548249341262249427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131312798795331576699331805 49242299548249341262249427)
      ·
        refine ⟨73863449322374011893374141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49242299548249341262249427 73863449322374011893374141)
        ·
          refine ⟨27698793495890254460015303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73863449322374011893374141 27698793495890254460015303)
          ·
            refine ⟨41548190243835381690022955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27698793495890254460015303 41548190243835381690022955)
            ·
              refine ⟨62322285365753072535034433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41548190243835381690022955 62322285365753072535034433)
              ·
                refine ⟨46741714024314804401275825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62322285365753072535034433 46741714024314804401275825)
                ·
                  refine ⟨35056285518236103300956869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46741714024314804401275825 35056285518236103300956869)
                  ·
                    refine ⟨6573053534669269368929413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35056285518236103300956869 6573053534669269368929413)
                    ·
                      refine ⟨1232447537750488006674265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6573053534669269368929413 1232447537750488006674265)
                      ·
                        rfl

theorem cell23_2400183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_2400183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400183 prefixEnd_2400183 := by exact prefixLift 2400183
  have htrace : WordTrace (prefixWord ++ tailWord_2400183) baseStart_2400183 baseEnd_2400183 := by
    simpa [prefixWord, tailWord_2400183, baseEnd_2400183] using wordTrace_append hprefix tailTrace_2400183
  have hstable : (prefixWord ++ tailWord_2400183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400183).length < 2 ^ (prefixWord ++ tailWord_2400183).sum := by decide
  have hdescent : baseEnd_2400183 < baseStart_2400183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400227 : List Nat := [1, 1, 1, 6, 1, 4, 1, 2, 6]
def baseStart_2400227 : Nat := 118140960795 + 2400227 * 2 ^ 59
def prefixEnd_2400227 : Nat := 4983230072969 + 3 ^ 40 * 2400227 * 2
def baseEnd_2400227 : Nat := 136941125655476203836007

theorem tailTrace_2400227 : CollatzResearch.WordTrace tailWord_2400227 prefixEnd_2400227 136941125655476203836007 := by
  unfold tailWord_2400227
  simp only [CollatzResearch.WordTrace]
  refine ⟨87543470675394979980822935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58362313783596653320548623 87543470675394979980822935)
  ·
    refine ⟨131315206013092469971234403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87543470675394979980822935 131315206013092469971234403)
    ·
      refine ⟨196972809019638704956851605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131315206013092469971234403 196972809019638704956851605)
      ·
        refine ⟨9233100422795564294852419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 196972809019638704956851605 9233100422795564294852419)
        ·
          refine ⟨13849650634193346442278629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9233100422795564294852419 13849650634193346442278629)
          ·
            refine ⟨2596809493911252457927243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13849650634193346442278629 2596809493911252457927243)
            ·
              refine ⟨3895214240866878686890865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2596809493911252457927243 3895214240866878686890865)
              ·
                refine ⟨2921410680650159015168149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3895214240866878686890865 2921410680650159015168149)
                ·
                  refine ⟨136941125655476203836007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2921410680650159015168149 136941125655476203836007)
                  ·
                    rfl

theorem cell23_2400227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 6].length) (baseStart_2400227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400227 prefixEnd_2400227 := by exact prefixLift 2400227
  have htrace : WordTrace (prefixWord ++ tailWord_2400227) baseStart_2400227 baseEnd_2400227 := by
    simpa [prefixWord, tailWord_2400227, baseEnd_2400227] using wordTrace_append hprefix tailTrace_2400227
  have hstable : (prefixWord ++ tailWord_2400227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400227).length < 2 ^ (prefixWord ++ tailWord_2400227).sum := by decide
  have hdescent : baseEnd_2400227 < baseStart_2400227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400257 : List Nat := [1, 2, 4, 1, 2, 1, 4, 2, 1, 5]
def baseStart_2400257 : Nat := 118140960795 + 2400257 * 2 ^ 59
def prefixEnd_2400257 : Nat := 4983230072969 + 3 ^ 40 * 2400257 * 2
def baseEnd_2400257 : Nat := 410828511772973572382975

theorem tailTrace_2400257 : CollatzResearch.WordTrace tailWord_2400257 prefixEnd_2400257 410828511772973572382975 := by
  unfold tailWord_2400257
  simp only [CollatzResearch.WordTrace]
  refine ⟨87544564865286295104415025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58363043243524196736276683 87544564865286295104415025)
  ·
    refine ⟨65658423648964721328311269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87544564865286295104415025 65658423648964721328311269)
    ·
      refine ⟨12310954434180885249058363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65658423648964721328311269 12310954434180885249058363)
      ·
        refine ⟨18466431651271327873587545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12310954434180885249058363 18466431651271327873587545)
        ·
          refine ⟨13849823738453495905190659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18466431651271327873587545 13849823738453495905190659)
          ·
            refine ⟨20774735607680243857785989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13849823738453495905190659 20774735607680243857785989)
            ·
              refine ⟨3895262926440045723334873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20774735607680243857785989 3895262926440045723334873)
              ·
                refine ⟨2921447194830034292501155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3895262926440045723334873 2921447194830034292501155)
                ·
                  refine ⟨4382170792245051438751733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2921447194830034292501155 4382170792245051438751733)
                  ·
                    refine ⟨410828511772973572382975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4382170792245051438751733 410828511772973572382975)
                    ·
                      rfl

theorem cell23_2400257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_2400257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400257 prefixEnd_2400257 := by exact prefixLift 2400257
  have htrace : WordTrace (prefixWord ++ tailWord_2400257) baseStart_2400257 baseEnd_2400257 := by
    simpa [prefixWord, tailWord_2400257, baseEnd_2400257] using wordTrace_append hprefix tailTrace_2400257
  have hstable : (prefixWord ++ tailWord_2400257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400257).length < 2 ^ (prefixWord ++ tailWord_2400257).sum := by decide
  have hdescent : baseEnd_2400257 < baseStart_2400257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400270 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 3, 6]
def baseStart_2400270 : Nat := 118140960795 + 2400270 * 2 ^ 59
def prefixEnd_2400270 : Nat := 4983230072969 + 3 ^ 40 * 2400270 * 2
def baseEnd_2400270 : Nat := 410830736855809722095455

theorem tailTrace_2400270 : CollatzResearch.WordTrace tailWord_2400270 prefixEnd_2400270 410830736855809722095455 := by
  unfold tailWord_2400270
  simp only [CollatzResearch.WordTrace]
  refine ⟨10943129876779899790579783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58363359342826132216425509 10943129876779899790579783)
  ·
    refine ⟨16414694815169849685869675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10943129876779899790579783 16414694815169849685869675)
    ·
      refine ⟨24622042222754774528804513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16414694815169849685869675 24622042222754774528804513)
      ·
        refine ⟨18466531667066080896603385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24622042222754774528804513 18466531667066080896603385)
        ·
          refine ⟨13849898750299560672452539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18466531667066080896603385 13849898750299560672452539)
          ·
            refine ⟨20774848125449341008678809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13849898750299560672452539 20774848125449341008678809)
            ·
              refine ⟨15581136094087005756509107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20774848125449341008678809 15581136094087005756509107)
              ·
                refine ⟨23371704141130508634763661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15581136094087005756509107 23371704141130508634763661)
                ·
                  refine ⟨8764389052923940738036373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23371704141130508634763661 8764389052923940738036373)
                  ·
                    refine ⟨410830736855809722095455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8764389052923940738036373 410830736855809722095455)
                    ·
                      rfl

theorem cell23_2400270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_2400270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400270 prefixEnd_2400270 := by exact prefixLift 2400270
  have htrace : WordTrace (prefixWord ++ tailWord_2400270) baseStart_2400270 baseEnd_2400270 := by
    simpa [prefixWord, tailWord_2400270, baseEnd_2400270] using wordTrace_append hprefix tailTrace_2400270
  have hstable : (prefixWord ++ tailWord_2400270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400270).length < 2 ^ (prefixWord ++ tailWord_2400270).sum := by decide
  have hdescent : baseEnd_2400270 < baseStart_2400270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400287 : List Nat := [1, 1, 2, 4, 1, 2, 2, 4, 2, 4]
def baseStart_2400287 : Nat := 118140960795 + 2400287 * 2 ^ 59
def prefixEnd_2400287 : Nat := 4983230072969 + 3 ^ 40 * 2400287 * 2
def baseEnd_2400287 : Nat := 410833646579518533257929

theorem tailTrace_2400287 : CollatzResearch.WordTrace tailWord_2400287 prefixEnd_2400287 410833646579518533257929 := by
  unfold tailWord_2400287
  simp only [CollatzResearch.WordTrace]
  refine ⟨87545659055177610228007115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58363772703451740152004743 87545659055177610228007115)
  ·
    refine ⟨131318488582766415342010673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87545659055177610228007115 131318488582766415342010673)
    ·
      refine ⟨98488866437074811506508005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131318488582766415342010673 98488866437074811506508005)
      ·
        refine ⟨18466662456951527157470251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98488866437074811506508005 18466662456951527157470251)
        ·
          refine ⟨27699993685427290736205377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18466662456951527157470251 27699993685427290736205377)
          ·
            refine ⟨20774995264070468052154033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27699993685427290736205377 20774995264070468052154033)
            ·
              refine ⟨15581246448052851039115525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20774995264070468052154033 15581246448052851039115525)
              ·
                refine ⟨2921483709009909569834161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15581246448052851039115525 2921483709009909569834161)
                ·
                  refine ⟨2191112781757432177375621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2921483709009909569834161 2191112781757432177375621)
                  ·
                    refine ⟨410833646579518533257929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2191112781757432177375621 410833646579518533257929)
                    ·
                      rfl

theorem cell23_2400287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 4].length) (baseStart_2400287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400287 prefixEnd_2400287 := by exact prefixLift 2400287
  have htrace : WordTrace (prefixWord ++ tailWord_2400287) baseStart_2400287 baseEnd_2400287 := by
    simpa [prefixWord, tailWord_2400287, baseEnd_2400287] using wordTrace_append hprefix tailTrace_2400287
  have hstable : (prefixWord ++ tailWord_2400287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400287).length < 2 ^ (prefixWord ++ tailWord_2400287).sum := by decide
  have hdescent : baseEnd_2400287 < baseStart_2400287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400290 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_2400290 : Nat := 118140960795 + 2400290 * 2 ^ 59
def prefixEnd_2400290 : Nat := 4983230072969 + 3 ^ 40 * 2400290 * 2
def baseEnd_2400290 : Nat := 1232502480180519088036273

theorem tailTrace_2400290 : CollatzResearch.WordTrace tailWord_2400290 prefixEnd_2400290 1232502480180519088036273 := by
  unfold tailWord_2400290
  simp only [CollatzResearch.WordTrace]
  refine ⟨21886442118541685435091581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58363845649444494493577549 21886442118541685435091581)
  ·
    refine ⟨8207415794453132038159343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21886442118541685435091581 8207415794453132038159343)
    ·
      refine ⟨12311123691679698057239015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8207415794453132038159343 12311123691679698057239015)
      ·
        refine ⟨18466685537519547085858523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12311123691679698057239015 18466685537519547085858523)
        ·
          refine ⟨27700028306279320628787785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18466685537519547085858523 27700028306279320628787785)
          ·
            refine ⟨20775021229709490471590839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27700028306279320628787785 20775021229709490471590839)
            ·
              refine ⟨31162531844564235707386259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20775021229709490471590839 31162531844564235707386259)
              ·
                refine ⟨46743797766846353561079389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31162531844564235707386259 46743797766846353561079389)
                ·
                  refine ⟨17528924162567382585404771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46743797766846353561079389 17528924162567382585404771)
                  ·
                    refine ⟨26293386243851073878107157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17528924162567382585404771 26293386243851073878107157)
                    ·
                      refine ⟨1232502480180519088036273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26293386243851073878107157 1232502480180519088036273)
                      ·
                        rfl

theorem cell23_2400290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_2400290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400290 prefixEnd_2400290 := by exact prefixLift 2400290
  have htrace : WordTrace (prefixWord ++ tailWord_2400290) baseStart_2400290 baseEnd_2400290 := by
    simpa [prefixWord, tailWord_2400290, baseEnd_2400290] using wordTrace_append hprefix tailTrace_2400290
  have hstable : (prefixWord ++ tailWord_2400290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400290).length < 2 ^ (prefixWord ++ tailWord_2400290).sum := by decide
  have hdescent : baseEnd_2400290 < baseStart_2400290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400304 : List Nat := [2, 1, 1, 1, 2, 5, 4, 1, 2, 4]
def baseStart_2400304 : Nat := 118140960795 + 2400304 * 2 ^ 59
def prefixEnd_2400304 : Nat := 4983230072969 + 3 ^ 40 * 2400304 * 2
def baseEnd_2400304 : Nat := 410836556303227344420403

theorem tailTrace_2400304 : CollatzResearch.WordTrace tailWord_2400304 prefixEnd_2400304 410836556303227344420403 := by
  unfold tailWord_2400304
  simp only [CollatzResearch.WordTrace]
  refine ⟨43773139548058011065687983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58364186064077348087583977 43773139548058011065687983)
  ·
    refine ⟨65659709322087016598531975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43773139548058011065687983 65659709322087016598531975)
    ·
      refine ⟨98489563983130524897797963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65659709322087016598531975 98489563983130524897797963)
      ·
        refine ⟨147734345974695787346696945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98489563983130524897797963 147734345974695787346696945)
        ·
          refine ⟨110800759481021840510022709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147734345974695787346696945 110800759481021840510022709)
          ·
            refine ⟨10387571201345797547814629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110800759481021840510022709 10387571201345797547814629)
            ·
              refine ⟨1947669600252337040215243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10387571201345797547814629 1947669600252337040215243)
              ·
                refine ⟨2921504400378505560322865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1947669600252337040215243 2921504400378505560322865)
                ·
                  refine ⟨2191128300283879170242149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2921504400378505560322865 2191128300283879170242149)
                  ·
                    refine ⟨410836556303227344420403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2191128300283879170242149 410836556303227344420403)
                    ·
                      rfl

theorem cell23_2400304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 2, 4].length) (baseStart_2400304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400304 prefixEnd_2400304 := by exact prefixLift 2400304
  have htrace : WordTrace (prefixWord ++ tailWord_2400304) baseStart_2400304 baseEnd_2400304 := by
    simpa [prefixWord, tailWord_2400304, baseEnd_2400304] using wordTrace_append hprefix tailTrace_2400304
  have hstable : (prefixWord ++ tailWord_2400304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400304).length < 2 ^ (prefixWord ++ tailWord_2400304).sum := by decide
  have hdescent : baseEnd_2400304 < baseStart_2400304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400308 : List Nat := [2, 5, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_2400308 : Nat := 118140960795 + 2400308 * 2 ^ 59
def prefixEnd_2400308 : Nat := 4983230072969 + 3 ^ 40 * 2400308 * 2
def baseEnd_2400308 : Nat := 410837240944100005870397

theorem tailTrace_2400308 : CollatzResearch.WordTrace tailWord_2400308 prefixEnd_2400308 410837240944100005870397 := by
  unfold tailWord_2400308
  simp only [CollatzResearch.WordTrace]
  refine ⟨43773212494050765407260789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58364283325401020543014385 43773212494050765407260789)
  ·
    refine ⟨4103738671317259256930699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43773212494050765407260789 4103738671317259256930699)
    ·
      refine ⟨6155608006975888885396049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4103738671317259256930699 6155608006975888885396049)
      ·
        refine ⟨4616706005231916664047037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6155608006975888885396049 4616706005231916664047037)
        ·
          refine ⟨1731264751961968749017639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4616706005231916664047037 1731264751961968749017639)
          ·
            refine ⟨2596897127942953123526459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1731264751961968749017639 2596897127942953123526459)
            ·
              refine ⟨3895345691914429685289689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2596897127942953123526459 3895345691914429685289689)
              ·
                refine ⟨2921509268935822263967267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3895345691914429685289689 2921509268935822263967267)
                ·
                  refine ⟨4382263903403733395950901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2921509268935822263967267 4382263903403733395950901)
                  ·
                    refine ⟨410837240944100005870397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4382263903403733395950901 410837240944100005870397)
                    ·
                      rfl

theorem cell23_2400308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_2400308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400308 prefixEnd_2400308 := by exact prefixLift 2400308
  have htrace : WordTrace (prefixWord ++ tailWord_2400308) baseStart_2400308 baseEnd_2400308 := by
    simpa [prefixWord, tailWord_2400308, baseEnd_2400308] using wordTrace_append hprefix tailTrace_2400308
  have hstable : (prefixWord ++ tailWord_2400308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400308).length < 2 ^ (prefixWord ++ tailWord_2400308).sum := by decide
  have hdescent : baseEnd_2400308 < baseStart_2400308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400327 : List Nat := [1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 3]
def baseStart_2400327 : Nat := 118140960795 + 2400327 * 2 ^ 59
def prefixEnd_2400327 : Nat := 4983230072969 + 3 ^ 40 * 2400327 * 2
def baseEnd_2400327 : Nat := 1232521478964735443273603

theorem tailTrace_2400327 : CollatzResearch.WordTrace tailWord_2400327 prefixEnd_2400327 1232521478964735443273603 := by
  unfold tailWord_2400327
  simp only [CollatzResearch.WordTrace]
  refine ⟨87547117975032697059463235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58364745316688464706308823 87547117975032697059463235)
  ·
    refine ⟨131320676962549045589194853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87547117975032697059463235 131320676962549045589194853)
    ·
      refine ⟨24622626930477946047974035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131320676962549045589194853 24622626930477946047974035)
      ·
        refine ⟨36933940395716919071961053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24622626930477946047974035 36933940395716919071961053)
        ·
          refine ⟨13850227648393844651985395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36933940395716919071961053 13850227648393844651985395)
          ·
            refine ⟨20775341472590766977978093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13850227648393844651985395 20775341472590766977978093)
            ·
              refine ⟨7790753052221537616741785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20775341472590766977978093 7790753052221537616741785)
              ·
                refine ⟨5843064789166153212556339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7790753052221537616741785 5843064789166153212556339)
                ·
                  refine ⟨8764597183749229818834509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5843064789166153212556339 8764597183749229818834509)
                  ·
                    refine ⟨3286723943905961182062941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8764597183749229818834509 3286723943905961182062941)
                    ·
                      refine ⟨1232521478964735443273603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3286723943905961182062941 1232521478964735443273603)
                      ·
                        rfl

theorem cell23_2400327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_2400327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400327 prefixEnd_2400327 := by exact prefixLift 2400327
  have htrace : WordTrace (prefixWord ++ tailWord_2400327) baseStart_2400327 baseEnd_2400327 := by
    simpa [prefixWord, tailWord_2400327, baseEnd_2400327] using wordTrace_append hprefix tailTrace_2400327
  have hstable : (prefixWord ++ tailWord_2400327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400327).length < 2 ^ (prefixWord ++ tailWord_2400327).sum := by decide
  have hdescent : baseEnd_2400327 < baseStart_2400327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400344 : List Nat := [2, 1, 2, 2, 1, 4, 1, 4, 2, 1, 3]
def baseStart_2400344 : Nat := 118140960795 + 2400344 * 2 ^ 59
def prefixEnd_2400344 : Nat := 4983230072969 + 3 ^ 40 * 2400344 * 2
def baseEnd_2400344 : Nat := 1232530208135861876761025

theorem tailTrace_2400344 : CollatzResearch.WordTrace tailWord_2400344 prefixEnd_2400344 1232530208135861876761025 := by
  unfold tailWord_2400344
  simp only [CollatzResearch.WordTrace]
  refine ⟨43773869007985554481416043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58365158677314072641888057 43773869007985554481416043)
  ·
    refine ⟨65660803511978331722124065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43773869007985554481416043 65660803511978331722124065)
    ·
      refine ⟨49245602633983748791593049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65660803511978331722124065 49245602633983748791593049)
      ·
        refine ⟨36934201975487811593694787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49245602633983748791593049 36934201975487811593694787)
        ·
          refine ⟨55401302963231717390542181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36934201975487811593694787 55401302963231717390542181)
          ·
            refine ⟨10387744305605947010726659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55401302963231717390542181 10387744305605947010726659)
            ·
              refine ⟨15581616458408920516089989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10387744305605947010726659 15581616458408920516089989)
              ·
                refine ⟨2921553085951672596766873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15581616458408920516089989 2921553085951672596766873)
                ·
                  refine ⟨2191164814463754447575155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2921553085951672596766873 2191164814463754447575155)
                  ·
                    refine ⟨3286747221695631671362733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2191164814463754447575155 3286747221695631671362733)
                    ·
                      refine ⟨1232530208135861876761025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3286747221695631671362733 1232530208135861876761025)
                      ·
                        rfl

theorem cell23_2400344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_2400344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400344 prefixEnd_2400344 := by exact prefixLift 2400344
  have htrace : WordTrace (prefixWord ++ tailWord_2400344) baseStart_2400344 baseEnd_2400344 := by
    simpa [prefixWord, tailWord_2400344, baseEnd_2400344] using wordTrace_append hprefix tailTrace_2400344
  have hstable : (prefixWord ++ tailWord_2400344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400344).length < 2 ^ (prefixWord ++ tailWord_2400344).sum := by decide
  have hdescent : baseEnd_2400344 < baseStart_2400344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400384 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 4, 2, 2]
def baseStart_2400384 : Nat := 118140960795 + 2400384 * 2 ^ 59
def prefixEnd_2400384 : Nat := 4983230072969 + 3 ^ 40 * 2400384 * 2
def baseEnd_2400384 : Nat := 1232550747362041720260841

theorem tailTrace_2400384 : CollatzResearch.WordTrace tailWord_2400384 prefixEnd_2400384 1232550747362041720260841 := by
  unfold tailWord_2400384
  simp only [CollatzResearch.WordTrace]
  refine ⟨43774598467913097897144103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58366131290550797196192137 43774598467913097897144103)
  ·
    refine ⟨65661897701869646845716155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43774598467913097897144103 65661897701869646845716155)
    ·
      refine ⟨98492846552804470268574233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65661897701869646845716155 98492846552804470268574233)
      ·
        refine ⟨73869634914603352701430675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98492846552804470268574233 73869634914603352701430675)
        ·
          refine ⟨110804452371905029052146013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73869634914603352701430675 110804452371905029052146013)
          ·
            refine ⟨41551669639464385894554755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110804452371905029052146013 41551669639464385894554755)
            ·
              refine ⟨62327504459196578841832133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41551669639464385894554755 62327504459196578841832133)
              ·
                refine ⟨11686407086099358532843525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62327504459196578841832133 11686407086099358532843525)
                ·
                  refine ⟨2191201328643629724908161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11686407086099358532843525 2191201328643629724908161)
                  ·
                    refine ⟨1643400996482722293681121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2191201328643629724908161 1643400996482722293681121)
                    ·
                      refine ⟨1232550747362041720260841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1643400996482722293681121 1232550747362041720260841)
                      ·
                        rfl

theorem cell23_2400384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 4, 2, 2].length) (baseStart_2400384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400384 prefixEnd_2400384 := by exact prefixLift 2400384
  have htrace : WordTrace (prefixWord ++ tailWord_2400384) baseStart_2400384 baseEnd_2400384 := by
    simpa [prefixWord, tailWord_2400384, baseEnd_2400384] using wordTrace_append hprefix tailTrace_2400384
  have hstable : (prefixWord ++ tailWord_2400384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400384).length < 2 ^ (prefixWord ++ tailWord_2400384).sum := by decide
  have hdescent : baseEnd_2400384 < baseStart_2400384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400418 : List Nat := [3, 3, 1, 3, 1, 3, 1, 1, 1, 4, 2]
def baseStart_2400418 : Nat := 118140960795 + 2400418 * 2 ^ 59
def prefixEnd_2400418 : Nat := 4983230072969 + 3 ^ 40 * 2400418 * 2
def baseEnd_2400418 : Nat := 1232568205704294587235685

theorem tailTrace_2400418 : CollatzResearch.WordTrace tailWord_2400418 prefixEnd_2400418 1232568205704294587235685 := by
  unfold tailWord_2400418
  simp only [CollatzResearch.WordTrace]
  refine ⟨21887609254425754900256477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58366958011802013067350605 21887609254425754900256477)
  ·
    refine ⟨8207853470409658087596179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21887609254425754900256477 8207853470409658087596179)
    ·
      refine ⟨12311780205614487131394269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8207853470409658087596179 12311780205614487131394269)
      ·
        refine ⟨4616917577105432674272851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12311780205614487131394269 4616917577105432674272851)
        ·
          refine ⟨6925376365658149011409277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4616917577105432674272851 6925376365658149011409277)
          ·
            refine ⟨2597016137121805879278479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6925376365658149011409277 2597016137121805879278479)
            ·
              refine ⟨3895524205682708818917719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2597016137121805879278479 3895524205682708818917719)
              ·
                refine ⟨5843286308524063228376579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3895524205682708818917719 5843286308524063228376579)
                ·
                  refine ⟨8764929462786094842564869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5843286308524063228376579 8764929462786094842564869)
                  ·
                    refine ⟨1643424274272392782980913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8764929462786094842564869 1643424274272392782980913)
                    ·
                      refine ⟨1232568205704294587235685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1643424274272392782980913 1232568205704294587235685)
                      ·
                        rfl

theorem cell23_2400418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_2400418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400418 prefixEnd_2400418 := by exact prefixLift 2400418
  have htrace : WordTrace (prefixWord ++ tailWord_2400418) baseStart_2400418 baseEnd_2400418 := by
    simpa [prefixWord, tailWord_2400418, baseEnd_2400418] using wordTrace_append hprefix tailTrace_2400418
  have hstable : (prefixWord ++ tailWord_2400418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400418).length < 2 ^ (prefixWord ++ tailWord_2400418).sum := by decide
  have hdescent : baseEnd_2400418 < baseStart_2400418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400427 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 5, 7, 2]
def baseStart_2400427 : Nat := 118140960795 + 2400427 * 2 ^ 59
def prefixEnd_2400427 : Nat := 4983230072969 + 3 ^ 40 * 2400427 * 2
def baseEnd_2400427 : Nat := 1232572827030185052023143

theorem tailTrace_2400427 : CollatzResearch.WordTrace tailWord_2400427 prefixEnd_2400427 1232572827030185052023143 := by
  unfold tailWord_2400427
  simp only [CollatzResearch.WordTrace]
  refine ⟨87550765274670414138103535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58367176849780276092069023 87550765274670414138103535)
  ·
    refine ⟨131326147912005621207155303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87550765274670414138103535 131326147912005621207155303)
    ·
      refine ⟨196989221868008431810732955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131326147912005621207155303 196989221868008431810732955)
      ·
        refine ⟨295483832802012647716099433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196989221868008431810732955 295483832802012647716099433)
        ·
          refine ⟨221612874601509485787074575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295483832802012647716099433 221612874601509485787074575)
          ·
            refine ⟨332419311902264228680611863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221612874601509485787074575 332419311902264228680611863)
            ·
              refine ⟨498628967853396343020917795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332419311902264228680611863 498628967853396343020917795)
              ·
                refine ⟨747943451780094514531376693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498628967853396343020917795 747943451780094514531376693)
                ·
                  refine ⟨70119698604383860737316565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 747943451780094514531376693 70119698604383860737316565)
                  ·
                    refine ⟨1643430436040246736030857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 70119698604383860737316565 1643430436040246736030857)
                    ·
                      refine ⟨1232572827030185052023143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1643430436040246736030857 1232572827030185052023143)
                      ·
                        rfl

theorem cell23_2400427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 7, 2].length) (baseStart_2400427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400427 prefixEnd_2400427 := by exact prefixLift 2400427
  have htrace : WordTrace (prefixWord ++ tailWord_2400427) baseStart_2400427 baseEnd_2400427 := by
    simpa [prefixWord, tailWord_2400427, baseEnd_2400427] using wordTrace_append hprefix tailTrace_2400427
  have hstable : (prefixWord ++ tailWord_2400427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400427).length < 2 ^ (prefixWord ++ tailWord_2400427).sum := by decide
  have hdescent : baseEnd_2400427 < baseStart_2400427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400474 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2]
def baseStart_2400474 : Nat := 118140960795 + 2400474 * 2 ^ 59
def prefixEnd_2400474 : Nat := 4983230072969 + 3 ^ 40 * 2400474 * 2
def baseEnd_2400474 : Nat := 1232596960620946368135427

theorem tailTrace_2400474 : CollatzResearch.WordTrace tailWord_2400474 prefixEnd_2400474 1232596960620946368135427 := by
  unfold tailWord_2400474
  simp only [CollatzResearch.WordTrace]
  refine ⟨21888119876375035291266119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58368319670333427443376317 21888119876375035291266119)
  ·
    refine ⟨32832179814562552936899179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21888119876375035291266119 32832179814562552936899179)
    ·
      refine ⟨49248269721843829405348769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32832179814562552936899179 49248269721843829405348769)
      ·
        refine ⟨36936202291382872054011577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49248269721843829405348769 36936202291382872054011577)
        ·
          refine ⟨27702151718537154040508683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36936202291382872054011577 27702151718537154040508683)
          ·
            refine ⟨41553227577805731060763025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27702151718537154040508683 41553227577805731060763025)
            ·
              refine ⟨31164920683354298295572269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41553227577805731060763025 31164920683354298295572269)
              ·
                refine ⟨11686845256257861860839601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31164920683354298295572269 11686845256257861860839601)
                ·
                  refine ⟨8765133942193396395629701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11686845256257861860839601 8765133942193396395629701)
                  ·
                    refine ⟨1643462614161261824180569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8765133942193396395629701 1643462614161261824180569)
                    ·
                      refine ⟨1232596960620946368135427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1643462614161261824180569 1232596960620946368135427)
                      ·
                        rfl

theorem cell23_2400474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2].length) (baseStart_2400474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400474 prefixEnd_2400474 := by exact prefixLift 2400474
  have htrace : WordTrace (prefixWord ++ tailWord_2400474) baseStart_2400474 baseEnd_2400474 := by
    simpa [prefixWord, tailWord_2400474, baseEnd_2400474] using wordTrace_append hprefix tailTrace_2400474
  have hstable : (prefixWord ++ tailWord_2400474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400474).length < 2 ^ (prefixWord ++ tailWord_2400474).sum := by decide
  have hdescent : baseEnd_2400474 < baseStart_2400474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400544 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 3, 5]
def baseStart_2400544 : Nat := 118140960795 + 2400544 * 2 ^ 59
def prefixEnd_2400544 : Nat := 4983230072969 + 3 ^ 40 * 2400544 * 2
def baseEnd_2400544 : Nat := 410877634755587031420035

theorem tailTrace_2400544 : CollatzResearch.WordTrace tailWord_2400544 prefixEnd_2400544 410877634755587031420035 := by
  unfold tailWord_2400544
  simp only [CollatzResearch.WordTrace]
  refine ⟨43777516307623271560056343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58370021743497695413408457 43777516307623271560056343)
  ·
    refine ⟨65666274461434907340084515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43777516307623271560056343 65666274461434907340084515)
    ·
      refine ⟨98499411692152361010126773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65666274461434907340084515 98499411692152361010126773)
      ·
        refine ⟨9234319846139283844699385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98499411692152361010126773 9234319846139283844699385)
        ·
          refine ⟨6925739884604462883524539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9234319846139283844699385 6925739884604462883524539)
          ·
            refine ⟨10388609826906694325286809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6925739884604462883524539 10388609826906694325286809)
            ·
              refine ⟨7791457370180020743965107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10388609826906694325286809 7791457370180020743965107)
              ·
                refine ⟨11687186055270031115947661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7791457370180020743965107 11687186055270031115947661)
                ·
                  refine ⟨4382694770726261668480373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11687186055270031115947661 4382694770726261668480373)
                  ·
                    refine ⟨410877634755587031420035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4382694770726261668480373 410877634755587031420035)
                    ·
                      rfl

theorem cell23_2400544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 3, 5].length) (baseStart_2400544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400544 prefixEnd_2400544 := by exact prefixLift 2400544
  have htrace : WordTrace (prefixWord ++ tailWord_2400544) baseStart_2400544 baseEnd_2400544 := by
    simpa [prefixWord, tailWord_2400544, baseEnd_2400544] using wordTrace_append hprefix tailTrace_2400544
  have hstable : (prefixWord ++ tailWord_2400544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400544).length < 2 ^ (prefixWord ++ tailWord_2400544).sum := by decide
  have hdescent : baseEnd_2400544 < baseStart_2400544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400561 : List Nat := [1, 2, 2, 3, 4, 1, 1, 3, 1, 5]
def baseStart_2400561 : Nat := 118140960795 + 2400561 * 2 ^ 59
def prefixEnd_2400561 : Nat := 4983230072969 + 3 ^ 40 * 2400561 * 2
def baseEnd_2400561 : Nat := 410880544479295842582509

theorem tailTrace_2400561 : CollatzResearch.WordTrace tailWord_2400561 prefixEnd_2400561 410880544479295842582509 := by
  unfold tailWord_2400561
  simp only [CollatzResearch.WordTrace]
  refine ⟨87555652656184955023481537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58370435104123303348987691 87555652656184955023481537)
  ·
    refine ⟨65666739492138716267611153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87555652656184955023481537 65666739492138716267611153)
    ·
      refine ⟨49250054619104037200708365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65666739492138716267611153 49250054619104037200708365)
      ·
        refine ⟨18468770482164013950265637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49250054619104037200708365 18468770482164013950265637)
        ·
          refine ⟨3462894465405752615674807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18468770482164013950265637 3462894465405752615674807)
          ·
            refine ⟨5194341698108628923512211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3462894465405752615674807 5194341698108628923512211)
            ·
              refine ⟨7791512547162943385268317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5194341698108628923512211 7791512547162943385268317)
              ·
                refine ⟨2921817205186103769475619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7791512547162943385268317 2921817205186103769475619)
                ·
                  refine ⟨4382725807779155654213429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2921817205186103769475619 4382725807779155654213429)
                  ·
                    refine ⟨410880544479295842582509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4382725807779155654213429 410880544479295842582509)
                    ·
                      rfl

theorem cell23_2400561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 5].length) (baseStart_2400561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400561 prefixEnd_2400561 := by exact prefixLift 2400561
  have htrace : WordTrace (prefixWord ++ tailWord_2400561) baseStart_2400561 baseEnd_2400561 := by
    simpa [prefixWord, tailWord_2400561, baseEnd_2400561] using wordTrace_append hprefix tailTrace_2400561
  have hstable : (prefixWord ++ tailWord_2400561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400561).length < 2 ^ (prefixWord ++ tailWord_2400561).sum := by decide
  have hdescent : baseEnd_2400561 < baseStart_2400561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400567 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 5]
def baseStart_2400567 : Nat := 118140960795 + 2400567 * 2 ^ 59
def prefixEnd_2400567 : Nat := 4983230072969 + 3 ^ 40 * 2400567 * 2
def baseEnd_2400567 : Nat := 1232644714321814504272499

theorem tailTrace_2400567 : CollatzResearch.WordTrace tailWord_2400567 prefixEnd_2400567 1232644714321814504272499 := by
  unfold tailWord_2400567
  simp only [CollatzResearch.WordTrace]
  refine ⟨87555871494163218048199955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58370580996108812032133303 87555871494163218048199955)
  ·
    refine ⟨131333807241244827072299933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87555871494163218048199955 131333807241244827072299933)
    ·
      refine ⟨49250177715466810152112475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131333807241244827072299933 49250177715466810152112475)
      ·
        refine ⟨73875266573200215228168713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49250177715466810152112475 73875266573200215228168713)
        ·
          refine ⟨55406449929900161421126535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73875266573200215228168713 55406449929900161421126535)
          ·
            refine ⟨83109674894850242131689803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55406449929900161421126535 83109674894850242131689803)
            ·
              refine ⟨124664512342275363197534705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83109674894850242131689803 124664512342275363197534705)
              ·
                refine ⟨93498384256706522398151029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124664512342275363197534705 93498384256706522398151029)
                ·
                  refine ⟨8765473524066236474826659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93498384256706522398151029 8765473524066236474826659)
                  ·
                    refine ⟨13148210286099354712239989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8765473524066236474826659 13148210286099354712239989)
                    ·
                      refine ⟨1232644714321814504272499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13148210286099354712239989 1232644714321814504272499)
                      ·
                        rfl

theorem cell23_2400567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_2400567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400567 prefixEnd_2400567 := by exact prefixLift 2400567
  have htrace : WordTrace (prefixWord ++ tailWord_2400567) baseStart_2400567 baseEnd_2400567 := by
    simpa [prefixWord, tailWord_2400567, baseEnd_2400567] using wordTrace_append hprefix tailTrace_2400567
  have hstable : (prefixWord ++ tailWord_2400567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400567).length < 2 ^ (prefixWord ++ tailWord_2400567).sum := by decide
  have hdescent : baseEnd_2400567 < baseStart_2400567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400584 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 5, 2, 3]
def baseStart_2400584 : Nat := 118140960795 + 2400584 * 2 ^ 59
def prefixEnd_2400584 : Nat := 4983230072969 + 3 ^ 40 * 2400584 * 2
def baseEnd_2400584 : Nat := 1232653443492940937759921

theorem tailTrace_2400584 : CollatzResearch.WordTrace tailWord_2400584 prefixEnd_2400584 1232653443492940937759921 := by
  unfold tailWord_2400584
  simp only [CollatzResearch.WordTrace]
  refine ⟨43778245767550814975784403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58370994356734419967712537 43778245767550814975784403)
  ·
    refine ⟨65667368651326222463676605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43778245767550814975784403 65667368651326222463676605)
    ·
      refine ⟨24625263244247333423878727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65667368651326222463676605 24625263244247333423878727)
      ·
        refine ⟨36937894866371000135818091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24625263244247333423878727 36937894866371000135818091)
        ·
          refine ⟨55406842299556500203727137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36937894866371000135818091 55406842299556500203727137)
          ·
            refine ⟨41555131724667375152795353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55406842299556500203727137 41555131724667375152795353)
            ·
              refine ⟨31166348793500531364596515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41555131724667375152795353 31166348793500531364596515)
              ·
                refine ⟨46749523190250797046894773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31166348793500531364596515 46749523190250797046894773)
                ·
                  refine ⟨4382767799086012223146385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46749523190250797046894773 4382767799086012223146385)
                  ·
                    refine ⟨3287075849314509167359789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4382767799086012223146385 3287075849314509167359789)
                    ·
                      refine ⟨1232653443492940937759921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3287075849314509167359789 1232653443492940937759921)
                      ·
                        rfl

theorem cell23_2400584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_2400584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400584 prefixEnd_2400584 := by exact prefixLift 2400584
  have htrace : WordTrace (prefixWord ++ tailWord_2400584) baseStart_2400584 baseEnd_2400584 := by
    simpa [prefixWord, tailWord_2400584, baseEnd_2400584] using wordTrace_append hprefix tailTrace_2400584
  have hstable : (prefixWord ++ tailWord_2400584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400584).length < 2 ^ (prefixWord ++ tailWord_2400584).sum := by decide
  have hdescent : baseEnd_2400584 < baseStart_2400584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400618 : List Nat := [3, 1, 3, 3, 1, 1, 2, 3, 1, 2, 3]
def baseStart_2400618 : Nat := 118140960795 + 2400618 * 2 ^ 59
def prefixEnd_2400618 : Nat := 4983230072969 + 3 ^ 40 * 2400618 * 2
def baseEnd_2400618 : Nat := 1232670901835193804734765

theorem tailTrace_2400618 : CollatzResearch.WordTrace tailWord_2400618 prefixEnd_2400618 1232670901835193804734765 := by
  unfold tailWord_2400618
  simp only [CollatzResearch.WordTrace]
  refine ⟨21889432904244613439576627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58371821077985635838871005 21889432904244613439576627)
  ·
    refine ⟨32834149356366920159364941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21889432904244613439576627 32834149356366920159364941)
    ·
      refine ⟨12312806008637595059761853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32834149356366920159364941 12312806008637595059761853)
      ·
        refine ⟨4617302253239098147410695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12312806008637595059761853 4617302253239098147410695)
        ·
          refine ⟨6925953379858647221116043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4617302253239098147410695 6925953379858647221116043)
          ·
            refine ⟨10388930069787970831674065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6925953379858647221116043 10388930069787970831674065)
            ·
              refine ⟨7791697552340978123755549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10388930069787970831674065 7791697552340978123755549)
              ·
                refine ⟨2921886582127866796408331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7791697552340978123755549 2921886582127866796408331)
                ·
                  refine ⟨4382829873191800194612497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2921886582127866796408331 4382829873191800194612497)
                  ·
                    refine ⟨3287122404893850145959373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4382829873191800194612497 3287122404893850145959373)
                    ·
                      refine ⟨1232670901835193804734765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3287122404893850145959373 1232670901835193804734765)
                      ·
                        rfl

theorem cell23_2400618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_2400618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400618 prefixEnd_2400618 := by exact prefixLift 2400618
  have htrace : WordTrace (prefixWord ++ tailWord_2400618) baseStart_2400618 baseEnd_2400618 := by
    simpa [prefixWord, tailWord_2400618, baseEnd_2400618] using wordTrace_append hprefix tailTrace_2400618
  have hstable : (prefixWord ++ tailWord_2400618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400618).length < 2 ^ (prefixWord ++ tailWord_2400618).sum := by decide
  have hdescent : baseEnd_2400618 < baseStart_2400618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400648 : List Nat := [2, 1, 3, 3, 1, 1, 3, 3, 2, 1, 3]
def baseStart_2400648 : Nat := 118140960795 + 2400648 * 2 ^ 59
def prefixEnd_2400648 : Nat := 4983230072969 + 3 ^ 40 * 2400648 * 2
def baseEnd_2400648 : Nat := 1232686306254828687359627

theorem tailTrace_2400648 : CollatzResearch.WordTrace tailWord_2400648 prefixEnd_2400648 1232686306254828687359627 := by
  unfold tailWord_2400648
  simp only [CollatzResearch.WordTrace]
  refine ⟨43779412903434884440949299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58372550537913179254599065 43779412903434884440949299)
  ·
    refine ⟨65669119355152326661423949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43779412903434884440949299 65669119355152326661423949)
    ·
      refine ⟨24625919758182122498033981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65669119355152326661423949 24625919758182122498033981)
      ·
        refine ⟨9234719909318295936762743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24625919758182122498033981 9234719909318295936762743)
        ·
          refine ⟨13852079863977443905144115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9234719909318295936762743 13852079863977443905144115)
          ·
            refine ⟨20778119795966165857716173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13852079863977443905144115 20778119795966165857716173)
            ·
              refine ⟨7791794923487312196643565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20778119795966165857716173 7791794923487312196643565)
              ·
                refine ⟨2921923096307742073741337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7791794923487312196643565 2921923096307742073741337)
                ·
                  refine ⟨2191442322230806555306003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2921923096307742073741337 2191442322230806555306003)
                  ·
                    refine ⟨3287163483346209832959005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2191442322230806555306003 3287163483346209832959005)
                    ·
                      refine ⟨1232686306254828687359627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3287163483346209832959005 1232686306254828687359627)
                      ·
                        rfl

theorem cell23_2400648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_2400648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400648 prefixEnd_2400648 := by exact prefixLift 2400648
  have htrace : WordTrace (prefixWord ++ tailWord_2400648) baseStart_2400648 baseEnd_2400648 := by
    simpa [prefixWord, tailWord_2400648, baseEnd_2400648] using wordTrace_append hprefix tailTrace_2400648
  have hstable : (prefixWord ++ tailWord_2400648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400648).length < 2 ^ (prefixWord ++ tailWord_2400648).sum := by decide
  have hdescent : baseEnd_2400648 < baseStart_2400648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400662 : List Nat := [5, 3, 1, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_2400662 : Nat := 118140960795 + 2400662 * 2 ^ 59
def prefixEnd_2400662 : Nat := 4983230072969 + 3 ^ 40 * 2400662 * 2
def baseEnd_2400662 : Nat := 1232693494983991632584563

theorem tailTrace_2400662 : CollatzResearch.WordTrace tailWord_2400662 prefixEnd_2400662 1232693494983991632584563 := by
  unfold tailWord_2400662
  simp only [CollatzResearch.WordTrace]
  refine ⟨5472458526801190579556765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58372890952546032848605493 5472458526801190579556765)
  ·
    refine ⟨2052171947550446467333787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5472458526801190579556765 2052171947550446467333787)
    ·
      refine ⟨3078257921325669701000681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2052171947550446467333787 3078257921325669701000681)
      ·
        refine ⟨2308693440994252275750511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3078257921325669701000681 2308693440994252275750511)
        ·
          refine ⟨3463040161491378413625767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2308693440994252275750511 3463040161491378413625767)
          ·
            refine ⟨5194560242237067620438651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3463040161491378413625767 5194560242237067620438651)
            ·
              refine ⟨7791840363355601430657977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5194560242237067620438651 7791840363355601430657977)
              ·
                refine ⟨5843880272516701072993483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7791840363355601430657977 5843880272516701072993483)
                ·
                  refine ⟨8765820408775051609490225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5843880272516701072993483 8765820408775051609490225)
                  ·
                    refine ⟨6574365306581288707117669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8765820408775051609490225 6574365306581288707117669)
                    ·
                      refine ⟨1232693494983991632584563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6574365306581288707117669 1232693494983991632584563)
                      ·
                        rfl

theorem cell23_2400662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_2400662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400662 prefixEnd_2400662 := by exact prefixLift 2400662
  have htrace : WordTrace (prefixWord ++ tailWord_2400662) baseStart_2400662 baseEnd_2400662 := by
    simpa [prefixWord, tailWord_2400662, baseEnd_2400662] using wordTrace_append hprefix tailTrace_2400662
  have hstable : (prefixWord ++ tailWord_2400662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400662).length < 2 ^ (prefixWord ++ tailWord_2400662).sum := by decide
  have hdescent : baseEnd_2400662 < baseStart_2400662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400675 : List Nat := [1, 1, 1, 4, 1, 5, 3, 1, 1, 3, 2]
def baseStart_2400675 : Nat := 118140960795 + 2400675 * 2 ^ 59
def prefixEnd_2400675 : Nat := 4983230072969 + 3 ^ 40 * 2400675 * 2
def baseEnd_2400675 : Nat := 1232700170232500081722003

theorem tailTrace_2400675 : CollatzResearch.WordTrace tailWord_2400675 prefixEnd_2400675 1232700170232500081722003 := by
  unfold tailWord_2400675
  simp only [CollatzResearch.WordTrace]
  refine ⟨87559810577771952493131479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58373207051847968328754319 87559810577771952493131479)
  ·
    refine ⟨131339715866657928739697219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87559810577771952493131479 131339715866657928739697219)
    ·
      refine ⟨197009573799986893109545829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131339715866657928739697219 197009573799986893109545829)
      ·
        refine ⟨36939295087497542458039843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197009573799986893109545829 36939295087497542458039843)
        ·
          refine ⟨55408942631246313687059765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36939295087497542458039843 55408942631246313687059765)
          ·
            refine ⟨5194588371679341908161853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55408942631246313687059765 5194588371679341908161853)
            ·
              refine ⟨1947970639379753215560695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5194588371679341908161853 1947970639379753215560695)
              ·
                refine ⟨2921955959069629823341043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1947970639379753215560695 2921955959069629823341043)
                ·
                  refine ⟨4382933938604444735011565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2921955959069629823341043 4382933938604444735011565)
                  ·
                    refine ⟨1643600226976666775629337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4382933938604444735011565 1643600226976666775629337)
                    ·
                      refine ⟨1232700170232500081722003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1643600226976666775629337 1232700170232500081722003)
                      ·
                        rfl

theorem cell23_2400675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 1, 3, 2].length) (baseStart_2400675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400675 prefixEnd_2400675 := by exact prefixLift 2400675
  have htrace : WordTrace (prefixWord ++ tailWord_2400675) baseStart_2400675 baseEnd_2400675 := by
    simpa [prefixWord, tailWord_2400675, baseEnd_2400675] using wordTrace_append hprefix tailTrace_2400675
  have hstable : (prefixWord ++ tailWord_2400675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400675).length < 2 ^ (prefixWord ++ tailWord_2400675).sum := by decide
  have hdescent : baseEnd_2400675 < baseStart_2400675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400684 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 4]
def baseStart_2400684 : Nat := 118140960795 + 2400684 * 2 ^ 59
def prefixEnd_2400684 : Nat := 4983230072969 + 3 ^ 40 * 2400684 * 2
def baseEnd_2400684 : Nat := 1232704791558390546509461

theorem tailTrace_2400684 : CollatzResearch.WordTrace tailWord_2400684 prefixEnd_2400684 1232704791558390546509461 := by
  unfold tailWord_2400684
  simp only [CollatzResearch.WordTrace]
  refine ⟨43780069417369673515104553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58373425889826231353472737 43780069417369673515104553)
  ·
    refine ⟨32835052063027255136328415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43780069417369673515104553 32835052063027255136328415)
    ·
      refine ⟨49252578094540882704492623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32835052063027255136328415 49252578094540882704492623)
      ·
        refine ⟨73878867141811324056738935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49252578094540882704492623 73878867141811324056738935)
        ·
          refine ⟨110818300712716986085108403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73878867141811324056738935 110818300712716986085108403)
          ·
            refine ⟨166227451069075479127662605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110818300712716986085108403 166227451069075479127662605)
            ·
              refine ⟨62335294150903304672873477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166227451069075479127662605 62335294150903304672873477)
              ·
                refine ⟨11687867653294369626163777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62335294150903304672873477 11687867653294369626163777)
                ·
                  refine ⟨8765900739970777219622833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11687867653294369626163777 8765900739970777219622833)
                  ·
                    refine ⟨6574425554978082914717125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8765900739970777219622833 6574425554978082914717125)
                    ·
                      refine ⟨1232704791558390546509461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6574425554978082914717125 1232704791558390546509461)
                      ·
                        rfl

theorem cell23_2400684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_2400684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400684 prefixEnd_2400684 := by exact prefixLift 2400684
  have htrace : WordTrace (prefixWord ++ tailWord_2400684) baseStart_2400684 baseEnd_2400684 := by
    simpa [prefixWord, tailWord_2400684, baseEnd_2400684] using wordTrace_append hprefix tailTrace_2400684
  have hstable : (prefixWord ++ tailWord_2400684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400684).length < 2 ^ (prefixWord ++ tailWord_2400684).sum := by decide
  have hdescent : baseEnd_2400684 < baseStart_2400684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400701 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 2, 2, 4]
def baseStart_2400701 : Nat := 118140960795 + 2400701 * 2 ^ 59
def prefixEnd_2400701 : Nat := 4983230072969 + 3 ^ 40 * 2400701 * 2
def baseEnd_2400701 : Nat := 1232713520729516979996883

theorem tailTrace_2400701 : CollatzResearch.WordTrace tailWord_2400701 prefixEnd_2400701 1232713520729516979996883 := by
  unfold tailWord_2400701
  simp only [CollatzResearch.WordTrace]
  refine ⟨87560758875677758933577957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58373839250451839289051971 87560758875677758933577957)
  ·
    refine ⟨16417642289189579800045867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87560758875677758933577957 16417642289189579800045867)
    ·
      refine ⟨24626463433784369700068801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16417642289189579800045867 24626463433784369700068801)
      ·
        refine ⟨18469847575338277275051601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24626463433784369700068801 18469847575338277275051601)
        ·
          refine ⟨13852385681503707956288701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18469847575338277275051601 13852385681503707956288701)
          ·
            refine ⟨5194644630563890483608263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13852385681503707956288701 5194644630563890483608263)
            ·
              refine ⟨7791966945845835725412395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5194644630563890483608263 7791966945845835725412395)
              ·
                refine ⟨11687950418768753588118593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7791966945845835725412395 11687950418768753588118593)
                ·
                  refine ⟨8765962814076565191088945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11687950418768753588118593 8765962814076565191088945)
                  ·
                    refine ⟨6574472110557423893316709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8765962814076565191088945 6574472110557423893316709)
                    ·
                      refine ⟨1232713520729516979996883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6574472110557423893316709 1232713520729516979996883)
                      ·
                        rfl

theorem cell23_2400701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_2400701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400701 prefixEnd_2400701 := by exact prefixLift 2400701
  have htrace : WordTrace (prefixWord ++ tailWord_2400701) baseStart_2400701 baseEnd_2400701 := by
    simpa [prefixWord, tailWord_2400701, baseEnd_2400701] using wordTrace_append hprefix tailTrace_2400701
  have hstable : (prefixWord ++ tailWord_2400701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400701).length < 2 ^ (prefixWord ++ tailWord_2400701).sum := by decide
  have hdescent : baseEnd_2400701 < baseStart_2400701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400739 : List Nat := [1, 1, 1, 6, 4, 1, 1, 2, 2, 2, 2]
def baseStart_2400739 : Nat := 118140960795 + 2400739 * 2 ^ 59
def prefixEnd_2400739 : Nat := 4983230072969 + 3 ^ 40 * 2400739 * 2
def baseEnd_2400739 : Nat := 1232733032994387831321709

theorem tailTrace_2400739 : CollatzResearch.WordTrace tailWord_2400739 prefixEnd_2400739 1232733032994387831321709 := by
  unfold tailWord_2400739
  simp only [CollatzResearch.WordTrace]
  refine ⟨87562144849540091423461271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58374763233026727615640847 87562144849540091423461271)
  ·
    refine ⟨131343217274310137135191907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87562144849540091423461271 131343217274310137135191907)
    ·
      refine ⟨197014825911465205702787861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131343217274310137135191907 197014825911465205702787861)
      ·
        refine ⟨9235069964599931517318181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 197014825911465205702787861 9235069964599931517318181)
        ·
          refine ⟨1731575618362487159497159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9235069964599931517318181 1731575618362487159497159)
          ·
            refine ⟨2597363427543730739245739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1731575618362487159497159 2597363427543730739245739)
            ·
              refine ⟨3896045141315596108868609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2597363427543730739245739 3896045141315596108868609)
              ·
                refine ⟨2922033855986697081651457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3896045141315596108868609 2922033855986697081651457)
                ·
                  refine ⟨2191525391990022811238593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2922033855986697081651457 2191525391990022811238593)
                  ·
                    refine ⟨1643644043992517108428945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2191525391990022811238593 1643644043992517108428945)
                    ·
                      refine ⟨1232733032994387831321709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1643644043992517108428945 1232733032994387831321709)
                      ·
                        rfl

theorem cell23_2400739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_2400739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400739 prefixEnd_2400739 := by exact prefixLift 2400739
  have htrace : WordTrace (prefixWord ++ tailWord_2400739) baseStart_2400739 baseEnd_2400739 := by
    simpa [prefixWord, tailWord_2400739, baseEnd_2400739] using wordTrace_append hprefix tailTrace_2400739
  have hstable : (prefixWord ++ tailWord_2400739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400739).length < 2 ^ (prefixWord ++ tailWord_2400739).sum := by decide
  have hdescent : baseEnd_2400739 < baseStart_2400739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400771 : List Nat := [1, 1, 1, 3, 2, 1, 3, 4, 3, 4]
def baseStart_2400771 : Nat := 118140960795 + 2400771 * 2 ^ 59
def prefixEnd_2400771 : Nat := 4983230072969 + 3 ^ 40 * 2400771 * 2
def baseEnd_2400771 : Nat := 410916488125110568707187

theorem tailTrace_2400771 : CollatzResearch.WordTrace tailWord_2400771 prefixEnd_2400771 410916488125110568707187 := by
  unfold tailWord_2400771
  simp only [CollatzResearch.WordTrace]
  refine ⟨87563311985424160888626167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58375541323616107259084111 87563311985424160888626167)
  ·
    refine ⟨131344967978136241332939251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87563311985424160888626167 131344967978136241332939251)
    ·
      refine ⟨197017451967204361999408877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131344967978136241332939251 197017451967204361999408877)
      ·
        refine ⟨73881544487701635749778329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197017451967204361999408877 73881544487701635749778329)
        ·
          refine ⟨55411158365776226812333747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73881544487701635749778329 55411158365776226812333747)
          ·
            refine ⟨83116737548664340218500621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55411158365776226812333747 83116737548664340218500621)
            ·
              refine ⟨31168776580749127581937733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83116737548664340218500621 31168776580749127581937733)
              ·
                refine ⟨5844145608890461421613325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31168776580749127581937733 5844145608890461421613325)
                ·
                  refine ⟨2191554603333923033104997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5844145608890461421613325 2191554603333923033104997)
                  ·
                    refine ⟨410916488125110568707187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2191554603333923033104997 410916488125110568707187)
                    ·
                      rfl

theorem cell23_2400771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 4].length) (baseStart_2400771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400771 prefixEnd_2400771 := by exact prefixLift 2400771
  have htrace : WordTrace (prefixWord ++ tailWord_2400771) baseStart_2400771 baseEnd_2400771 := by
    simpa [prefixWord, tailWord_2400771, baseEnd_2400771] using wordTrace_append hprefix tailTrace_2400771
  have hstable : (prefixWord ++ tailWord_2400771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400771).length < 2 ^ (prefixWord ++ tailWord_2400771).sum := by decide
  have hdescent : baseEnd_2400771 < baseStart_2400771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400801 : List Nat := [1, 2, 3, 2, 2, 1, 2, 4, 6]
def baseStart_2400801 : Nat := 118140960795 + 2400801 * 2 ^ 59
def prefixEnd_2400801 : Nat := 4983230072969 + 3 ^ 40 * 2400801 * 2
def baseEnd_2400801 : Nat := 136973874310551843194047

theorem tailTrace_2400801 : CollatzResearch.WordTrace tailWord_2400801 prefixEnd_2400801 136973874310551843194047 := by
  unfold tailWord_2400801
  simp only [CollatzResearch.WordTrace]
  refine ⟨87564406175315476012218257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58376270783543650674812171 87564406175315476012218257)
  ·
    refine ⟨65673304631486607009163693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87564406175315476012218257 65673304631486607009163693)
    ·
      refine ⟨24627489236807477628436385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65673304631486607009163693 24627489236807477628436385)
      ·
        refine ⟨18470616927605608221327289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24627489236807477628436385 18470616927605608221327289)
        ·
          refine ⟨13852962695704206165995467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18470616927605608221327289 13852962695704206165995467)
          ·
            refine ⟨20779444043556309248993201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13852962695704206165995467 20779444043556309248993201)
            ·
              refine ⟨15584583032667231936744901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20779444043556309248993201 15584583032667231936744901)
              ·
                refine ⟨2922109318625105988139669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15584583032667231936744901 2922109318625105988139669)
                ·
                  refine ⟨136973874310551843194047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2922109318625105988139669 136973874310551843194047)
                  ·
                    rfl

theorem cell23_2400801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 6].length) (baseStart_2400801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400801 prefixEnd_2400801 := by exact prefixLift 2400801
  have htrace : WordTrace (prefixWord ++ tailWord_2400801) baseStart_2400801 baseEnd_2400801 := by
    simpa [prefixWord, tailWord_2400801, baseEnd_2400801] using wordTrace_append hprefix tailTrace_2400801
  have hstable : (prefixWord ++ tailWord_2400801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400801).length < 2 ^ (prefixWord ++ tailWord_2400801).sum := by decide
  have hdescent : baseEnd_2400801 < baseStart_2400801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400818 : List Nat := [3, 2, 1, 1, 2, 1, 6, 1, 6]
def baseStart_2400818 : Nat := 118140960795 + 2400818 * 2 ^ 59
def prefixEnd_2400818 : Nat := 4983230072969 + 3 ^ 40 * 2400818 * 2
def baseEnd_2400818 : Nat := 136974844218454780248205

theorem tailTrace_2400818 : CollatzResearch.WordTrace tailWord_2400818 prefixEnd_2400818 136974844218454780248205 := by
  unfold tailWord_2400818
  simp only [CollatzResearch.WordTrace]
  refine ⟨21891256554063471978896777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58376684144169258610391405 21891256554063471978896777)
  ·
    refine ⟨16418442415547603984172583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21891256554063471978896777 16418442415547603984172583)
    ·
      refine ⟨24627663623321405976258875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16418442415547603984172583 24627663623321405976258875)
      ·
        refine ⟨36941495434982108964388313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24627663623321405976258875 36941495434982108964388313)
        ·
          refine ⟨27706121576236581723291235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36941495434982108964388313 27706121576236581723291235)
          ·
            refine ⟨41559182364354872584936853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27706121576236581723291235 41559182364354872584936853)
            ·
              refine ⟨1948086673329134652418915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41559182364354872584936853 1948086673329134652418915)
              ·
                refine ⟨2922130009993701978628373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1948086673329134652418915 2922130009993701978628373)
                ·
                  refine ⟨136974844218454780248205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2922130009993701978628373 136974844218454780248205)
                  ·
                    rfl

theorem cell23_2400818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_2400818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400818 prefixEnd_2400818 := by exact prefixLift 2400818
  have htrace : WordTrace (prefixWord ++ tailWord_2400818) baseStart_2400818 baseEnd_2400818 := by
    simpa [prefixWord, tailWord_2400818, baseEnd_2400818] using wordTrace_append hprefix tailTrace_2400818
  have hstable : (prefixWord ++ tailWord_2400818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400818).length < 2 ^ (prefixWord ++ tailWord_2400818).sum := by decide
  have hdescent : baseEnd_2400818 < baseStart_2400818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400831 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 3, 5]
def baseStart_2400831 : Nat := 118140960795 + 2400831 * 2 ^ 59
def prefixEnd_2400831 : Nat := 4983230072969 + 3 ^ 40 * 2400831 * 2
def baseEnd_2400831 : Nat := 410926757738200490457095

theorem tailTrace_2400831 : CollatzResearch.WordTrace tailWord_2400831 prefixEnd_2400831 410926757738200490457095 := by
  unfold tailWord_2400831
  simp only [CollatzResearch.WordTrace]
  refine ⟨87565500365206791135810347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58377000243471194090540231 87565500365206791135810347)
  ·
    refine ⟨131348250547810186703715521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87565500365206791135810347 131348250547810186703715521)
    ·
      refine ⟨98511187910857640027786641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131348250547810186703715521 98511187910857640027786641)
      ·
        refine ⟨73883390933143230020839981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98511187910857640027786641 73883390933143230020839981)
        ·
          refine ⟨27706271599928711257814993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73883390933143230020839981 27706271599928711257814993)
          ·
            refine ⟨20779703699946533443361245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27706271599928711257814993 20779703699946533443361245)
            ·
              refine ⟨7792388887479950041260467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20779703699946533443361245 7792388887479950041260467)
              ·
                refine ⟨11688583331219925061890701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7792388887479950041260467 11688583331219925061890701)
                ·
                  refine ⟨4383218749207471898209013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11688583331219925061890701 4383218749207471898209013)
                  ·
                    refine ⟨410926757738200490457095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4383218749207471898209013 410926757738200490457095)
                    ·
                      rfl

theorem cell23_2400831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 5].length) (baseStart_2400831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400831 prefixEnd_2400831 := by exact prefixLift 2400831
  have htrace : WordTrace (prefixWord ++ tailWord_2400831) baseStart_2400831 baseEnd_2400831 := by
    simpa [prefixWord, tailWord_2400831, baseEnd_2400831] using wordTrace_append hprefix tailTrace_2400831
  have hstable : (prefixWord ++ tailWord_2400831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400831).length < 2 ^ (prefixWord ++ tailWord_2400831).sum := by decide
  have hdescent : baseEnd_2400831 < baseStart_2400831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400871 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_2400871 : Nat := 118140960795 + 2400871 * 2 ^ 59
def prefixEnd_2400871 : Nat := 4983230072969 + 3 ^ 40 * 2400871 * 2
def baseEnd_2400871 : Nat := 1232800812440781314871101

theorem tailTrace_2400871 : CollatzResearch.WordTrace tailWord_2400871 prefixEnd_2400871 1232800812440781314871101 := by
  unfold tailWord_2400871
  simp only [CollatzResearch.WordTrace]
  refine ⟨87566959285061877967266467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58377972856707918644844311 87566959285061877967266467)
  ·
    refine ⟨131350438927592816950899701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87566959285061877967266467 131350438927592816950899701)
    ·
      refine ⟨12314103649461826589146847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131350438927592816950899701 12314103649461826589146847)
      ·
        refine ⟨18471155474192739883720271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12314103649461826589146847 18471155474192739883720271)
        ·
          refine ⟨27706733211289109825580407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18471155474192739883720271 27706733211289109825580407)
          ·
            refine ⟨41560099816933664738370611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27706733211289109825580407 41560099816933664738370611)
            ·
              refine ⟨62340149725400497107555917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41560099816933664738370611 62340149725400497107555917)
              ·
                refine ⟨23377556147025186415333469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62340149725400497107555917 23377556147025186415333469)
                ·
                  refine ⟨8766583555134444905750051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23377556147025186415333469 8766583555134444905750051)
                  ·
                    refine ⟨13149875332701667358625077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8766583555134444905750051 13149875332701667358625077)
                    ·
                      refine ⟨1232800812440781314871101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13149875332701667358625077 1232800812440781314871101)
                      ·
                        rfl

theorem cell23_2400871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_2400871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400871 prefixEnd_2400871 := by exact prefixLift 2400871
  have htrace : WordTrace (prefixWord ++ tailWord_2400871) baseStart_2400871 baseEnd_2400871 := by
    simpa [prefixWord, tailWord_2400871, baseEnd_2400871] using wordTrace_append hprefix tailTrace_2400871
  have hstable : (prefixWord ++ tailWord_2400871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400871).length < 2 ^ (prefixWord ++ tailWord_2400871).sum := by decide
  have hdescent : baseEnd_2400871 < baseStart_2400871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
