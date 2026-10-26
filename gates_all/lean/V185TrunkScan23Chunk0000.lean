import V185TrunkScan22Incremental

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5 : List Nat := [1, 3, 1, 1, 2, 4, 2, 3, 1, 1, 4]
def baseStart_5 : Nat := 118140960795 + 5 * 2 ^ 59
def prefixEnd_5 : Nat := 4983230072969 + 3 ^ 40 * 5 * 2
def baseEnd_5 : Nat := 2567403377714137483

theorem tailTrace_5 : CollatzResearch.WordTrace tailWord_5 prefixEnd_5 2567403377714137483 := by
  unfold tailWord_5
  simp only [CollatzResearch.WordTrace]
  refine ⟨182364989360699041469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121576659573799360979 182364989360699041469)
  ·
    refine ⟨68386871010262140551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182364989360699041469 68386871010262140551)
    ·
      refine ⟨102580306515393210827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68386871010262140551 102580306515393210827)
      ·
        refine ⟨153870459773089816241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102580306515393210827 153870459773089816241)
        ·
          refine ⟨115402844829817362181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153870459773089816241 115402844829817362181)
          ·
            refine ⟨21638033405590755409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115402844829817362181 21638033405590755409)
            ·
              refine ⟨16228525054193066557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21638033405590755409 16228525054193066557)
              ·
                refine ⟨6085696895322399959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16228525054193066557 6085696895322399959)
                ·
                  refine ⟨9128545342983599939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6085696895322399959 9128545342983599939)
                  ·
                    refine ⟨13692818014475399909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9128545342983599939 13692818014475399909)
                    ·
                      refine ⟨2567403377714137483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13692818014475399909 2567403377714137483)
                      ·
                        rfl

theorem cell23_5_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 1, 4].length) (baseStart_5 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5 prefixEnd_5 := by exact prefixLift 5
  have htrace : WordTrace (prefixWord ++ tailWord_5) baseStart_5 baseEnd_5 := by
    simpa [prefixWord, tailWord_5, baseEnd_5] using wordTrace_append hprefix tailTrace_5
  have hstable : (prefixWord ++ tailWord_5).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5).length < 2 ^ (prefixWord ++ tailWord_5).sum := by decide
  have hdescent : baseEnd_5 < baseStart_5 := by decide
  rcases family_descends (prefixWord ++ tailWord_5) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28 : List Nat := [2, 2, 3, 1, 3, 1, 1, 10]
def baseStart_28 : Nat := 118140960795 + 28 * 2 ^ 59
def prefixEnd_28 : Nat := 4983230072969 + 3 ^ 40 * 28 * 2
def baseEnd_28 : Nat := 532498460412005551

theorem tailTrace_28 : CollatzResearch.WordTrace tailWord_28 prefixEnd_28 532498460412005551 := by
  unfold tailWord_28
  simp only [CollatzResearch.WordTrace]
  refine ⟨510621953017813564369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 680829270690418085825 510621953017813564369)
  ·
    refine ⟨382966464763360173277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 510621953017813564369 382966464763360173277)
    ·
      refine ⟨143612424286260064979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382966464763360173277 143612424286260064979)
      ·
        refine ⟨215418636429390097469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143612424286260064979 215418636429390097469)
        ·
          refine ⟨80781988661021286551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215418636429390097469 80781988661021286551)
          ·
            refine ⟨121172982991531929827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80781988661021286551 121172982991531929827)
            ·
              refine ⟨181759474487297894741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121172982991531929827 181759474487297894741)
              ·
                refine ⟨532498460412005551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 181759474487297894741 532498460412005551)
                ·
                  rfl

theorem cell23_28_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 10].length) (baseStart_28 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_28 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_28 prefixEnd_28 := by exact prefixLift 28
  have htrace : WordTrace (prefixWord ++ tailWord_28) baseStart_28 baseEnd_28 := by
    simpa [prefixWord, tailWord_28, baseEnd_28] using wordTrace_append hprefix tailTrace_28
  have hstable : (prefixWord ++ tailWord_28).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28).length < 2 ^ (prefixWord ++ tailWord_28).sum := by decide
  have hdescent : baseEnd_28 < baseStart_28 := by decide
  rcases family_descends (prefixWord ++ tailWord_28) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_42 : Nat := 118140960795 + 42 * 2 ^ 59
def prefixEnd_42 : Nat := 4983230072969 + 3 ^ 40 * 42 * 2
def baseEnd_42 : Nat := 21566187594069374813

theorem tailTrace_42 : CollatzResearch.WordTrace tailWord_42 prefixEnd_42 21566187594069374813 := by
  unfold tailWord_42
  simp only [CollatzResearch.WordTrace]
  refine ⟨382966463829004534595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1021243903544012092253 382966463829004534595)
  ·
    refine ⟨574449695743506801893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 382966463829004534595 574449695743506801893)
    ·
      refine ⟨107709317951907525355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 574449695743506801893 107709317951907525355)
      ·
        refine ⟨161563976927861288033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107709317951907525355 161563976927861288033)
        ·
          refine ⟨121172982695895966025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161563976927861288033 121172982695895966025)
          ·
            refine ⟨90879737021921974519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121172982695895966025 90879737021921974519)
            ·
              refine ⟨136319605532882961779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90879737021921974519 136319605532882961779)
              ·
                refine ⟨204479408299324442669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136319605532882961779 204479408299324442669)
                ·
                  refine ⟨76679778112246666001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 204479408299324442669 76679778112246666001)
                  ·
                    refine ⟨57509833584184999501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76679778112246666001 57509833584184999501)
                    ·
                      refine ⟨21566187594069374813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 57509833584184999501 21566187594069374813)
                      ·
                        rfl

theorem cell23_42_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_42 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42 prefixEnd_42 := by exact prefixLift 42
  have htrace : WordTrace (prefixWord ++ tailWord_42) baseStart_42 baseEnd_42 := by
    simpa [prefixWord, tailWord_42, baseEnd_42] using wordTrace_append hprefix tailTrace_42
  have hstable : (prefixWord ++ tailWord_42).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42).length < 2 ^ (prefixWord ++ tailWord_42).sum := by decide
  have hdescent : baseEnd_42 < baseStart_42 := by decide
  rcases family_descends (prefixWord ++ tailWord_42) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 6, 1, 3]
def baseStart_55 : Nat := 118140960795 + 55 * 2 ^ 59
def prefixEnd_55 : Nat := 4983230072969 + 3 ^ 40 * 55 * 2
def baseEnd_55 : Nat := 28241436102518512253

theorem tailTrace_55 : CollatzResearch.WordTrace tailWord_55 prefixEnd_55 28241436102518512253 := by
  unfold tailWord_55
  simp only [CollatzResearch.WordTrace]
  refine ⟨2006014808219238361619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1337343205479492241079 2006014808219238361619)
  ·
    refine ⟨3009022212328857542429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2006014808219238361619 3009022212328857542429)
    ·
      refine ⟨1128383329623321578411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3009022212328857542429 1128383329623321578411)
      ·
        refine ⟨1692574994434982367617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1128383329623321578411 1692574994434982367617)
        ·
          refine ⟨1269431245826236775713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1692574994434982367617 1269431245826236775713)
          ·
            refine ⟨952073434369677581785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1269431245826236775713 952073434369677581785)
            ·
              refine ⟨714055075777258186339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 952073434369677581785 714055075777258186339)
              ·
                refine ⟨1071082613665887279509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 714055075777258186339 1071082613665887279509)
                ·
                  refine ⟨50206997515588466227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1071082613665887279509 50206997515588466227)
                  ·
                    refine ⟨75310496273382699341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50206997515588466227 75310496273382699341)
                    ·
                      refine ⟨28241436102518512253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 75310496273382699341 28241436102518512253)
                      ·
                        rfl

theorem cell23_55_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 1, 3].length) (baseStart_55 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_55 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_55 prefixEnd_55 := by exact prefixLift 55
  have htrace : WordTrace (prefixWord ++ tailWord_55) baseStart_55 baseEnd_55 := by
    simpa [prefixWord, tailWord_55, baseEnd_55] using wordTrace_append hprefix tailTrace_55
  have hstable : (prefixWord ++ tailWord_55).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55).length < 2 ^ (prefixWord ++ tailWord_55).sum := by decide
  have hdescent : baseEnd_55 < baseStart_55 := by decide
  rcases family_descends (prefixWord ++ tailWord_55) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 1, 8]
def baseStart_88 : Nat := 118140960795 + 88 * 2 ^ 59
def prefixEnd_88 : Nat := 4983230072969 + 3 ^ 40 * 88 * 2
def baseEnd_88 : Nat := 15062099233629799867

theorem tailTrace_88 : CollatzResearch.WordTrace tailWord_88 prefixEnd_88 15062099233629799867 := by
  unfold tailWord_88
  simp only [CollatzResearch.WordTrace]
  refine ⟨1604811844332937156459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2139749125777249541945 1604811844332937156459)
  ·
    refine ⟨2407217766499405734689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1604811844332937156459 2407217766499405734689)
    ·
      refine ⟨1805413324874554301017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2407217766499405734689 1805413324874554301017)
      ·
        refine ⟨1354059993655915725763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1805413324874554301017 1354059993655915725763)
        ·
          refine ⟨2031089990483873588645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1354059993655915725763 2031089990483873588645)
          ·
            refine ⟨380829373215726297871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2031089990483873588645 380829373215726297871)
            ·
              refine ⟨571244059823589446807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380829373215726297871 571244059823589446807)
              ·
                refine ⟨856866089735384170211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 571244059823589446807 856866089735384170211)
                ·
                  refine ⟨1285299134603076255317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 856866089735384170211 1285299134603076255317)
                  ·
                    refine ⟨15062099233629799867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1285299134603076255317 15062099233629799867)
                    ·
                      rfl

theorem cell23_88_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_88 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88 prefixEnd_88 := by exact prefixLift 88
  have htrace : WordTrace (prefixWord ++ tailWord_88) baseStart_88 baseEnd_88 := by
    simpa [prefixWord, tailWord_88, baseEnd_88] using wordTrace_append hprefix tailTrace_88
  have hstable : (prefixWord ++ tailWord_88).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88).length < 2 ^ (prefixWord ++ tailWord_88).sum := by decide
  have hdescent : baseEnd_88 < baseStart_88 := by decide
  rcases family_descends (prefixWord ++ tailWord_88) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112 : List Nat := [2, 1, 1, 1, 5, 2, 2, 2, 1, 4, 2]
def baseStart_112 : Nat := 118140960795 + 112 * 2 ^ 59
def prefixEnd_112 : Nat := 4983230072969 + 3 ^ 40 * 112 * 2
def baseEnd_112 : Nat := 57509833408795499491

theorem tailTrace_112 : CollatzResearch.WordTrace tailWord_112 prefixEnd_112 57509833408795499491 := by
  unfold tailWord_112
  simp only [CollatzResearch.WordTrace]
  refine ⟨2042487800858986593295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2723317067811982124393 2042487800858986593295)
  ·
    refine ⟨3063731701288479889943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2042487800858986593295 3063731701288479889943)
    ·
      refine ⟨4595597551932719834915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3063731701288479889943 4595597551932719834915)
      ·
        refine ⟨6893396327899079752373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4595597551932719834915 6893396327899079752373)
        ·
          refine ⟨646255905740538726785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6893396327899079752373 646255905740538726785)
          ·
            refine ⟨484691929305404045089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 646255905740538726785 484691929305404045089)
            ·
              refine ⟨363518946979053033817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484691929305404045089 363518946979053033817)
              ·
                refine ⟨272639210234289775363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 363518946979053033817 272639210234289775363)
                ·
                  refine ⟨408958815351434663045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272639210234289775363 408958815351434663045)
                  ·
                    refine ⟨76679777878393999321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 408958815351434663045 76679777878393999321)
                    ·
                      refine ⟨57509833408795499491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 76679777878393999321 57509833408795499491)
                      ·
                        rfl

theorem cell23_112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 1, 4, 2].length) (baseStart_112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112 prefixEnd_112 := by exact prefixLift 112
  have htrace : WordTrace (prefixWord ++ tailWord_112) baseStart_112 baseEnd_112 := by
    simpa [prefixWord, tailWord_112, baseEnd_112] using wordTrace_append hprefix tailTrace_112
  have hstable : (prefixWord ++ tailWord_112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112).length < 2 ^ (prefixWord ++ tailWord_112).sum := by decide
  have hdescent : baseEnd_112 < baseStart_112 := by decide
  rcases family_descends (prefixWord ++ tailWord_112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 2, 2, 4]
def baseStart_125 : Nat := 118140960795 + 125 * 2 ^ 59
def prefixEnd_125 : Nat := 4983230072969 + 3 ^ 40 * 125 * 2
def baseEnd_125 : Nat := 64185081917244636931

theorem tailTrace_125 : CollatzResearch.WordTrace tailWord_125 prefixEnd_125 64185081917244636931 := by
  unfold tailWord_125
  simp only [CollatzResearch.WordTrace]
  refine ⟨4559124554621193409829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3039416369747462273219 4559124554621193409829)
  ·
    refine ⟨854835853991473764343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4559124554621193409829 854835853991473764343)
    ·
      refine ⟨1282253780987210646515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 854835853991473764343 1282253780987210646515)
      ·
        refine ⟨1923380671480815969773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1282253780987210646515 1923380671480815969773)
        ·
          refine ⟨721267751805305988665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1923380671480815969773 721267751805305988665)
          ·
            refine ⟨540950813853979491499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 721267751805305988665 540950813853979491499)
            ·
              refine ⟨811426220780969237249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540950813853979491499 811426220780969237249)
              ·
                refine ⟨608569665585726927937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 811426220780969237249 608569665585726927937)
                ·
                  refine ⟨456427249189295195953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 608569665585726927937 456427249189295195953)
                  ·
                    refine ⟨342320436891971396965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 456427249189295195953 342320436891971396965)
                    ·
                      refine ⟨64185081917244636931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 342320436891971396965 64185081917244636931)
                      ·
                        rfl

theorem cell23_125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125 prefixEnd_125 := by exact prefixLift 125
  have htrace : WordTrace (prefixWord ++ tailWord_125) baseStart_125 baseEnd_125 := by
    simpa [prefixWord, tailWord_125, baseEnd_125] using wordTrace_append hprefix tailTrace_125
  have hstable : (prefixWord ++ tailWord_125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125).length < 2 ^ (prefixWord ++ tailWord_125).sum := by decide
  have hdescent : baseEnd_125 < baseStart_125 := by decide
  rcases family_descends (prefixWord ++ tailWord_125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165 : List Nat := [1, 3, 1, 2, 1, 3, 2, 3, 2, 5]
def baseStart_165 : Nat := 118140960795 + 165 * 2 ^ 59
def prefixEnd_165 : Nat := 4983230072969 + 3 ^ 40 * 165 * 2
def baseEnd_165 : Nat := 28241436032362712249

theorem tailTrace_165 : CollatzResearch.WordTrace tailWord_165 prefixEnd_165 28241436032362712249 := by
  unfold tailWord_165
  simp only [CollatzResearch.WordTrace]
  refine ⟨6018044409708024865949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4012029606472016577299 6018044409708024865949)
  ·
    refine ⟨2256766653640509324731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6018044409708024865949 2256766653640509324731)
    ·
      refine ⟨3385149980460763987097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2256766653640509324731 3385149980460763987097)
      ·
        refine ⟨2538862485345572990323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3385149980460763987097 2538862485345572990323)
        ·
          refine ⟨3808293728018359485485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2538862485345572990323 3808293728018359485485)
          ·
            refine ⟨1428110148006884807057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3808293728018359485485 1428110148006884807057)
            ·
              refine ⟨1071082611005163605293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1428110148006884807057 1071082611005163605293)
              ·
                refine ⟨401655979126936351985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1071082611005163605293 401655979126936351985)
                ·
                  refine ⟨301241984345202263989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 401655979126936351985 301241984345202263989)
                  ·
                    refine ⟨28241436032362712249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 301241984345202263989 28241436032362712249)
                    ·
                      rfl

theorem cell23_165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165 prefixEnd_165 := by exact prefixLift 165
  have htrace : WordTrace (prefixWord ++ tailWord_165) baseStart_165 baseEnd_165 := by
    simpa [prefixWord, tailWord_165, baseEnd_165] using wordTrace_append hprefix tailTrace_165
  have hstable : (prefixWord ++ tailWord_165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165).length < 2 ^ (prefixWord ++ tailWord_165).sum := by decide
  have hdescent : baseEnd_165 < baseStart_165 := by decide
  rcases family_descends (prefixWord ++ tailWord_165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 1, 6, 2]
def baseStart_202 : Nat := 118140960795 + 202 * 2 ^ 59
def prefixEnd_202 : Nat := 4983230072969 + 3 ^ 40 * 202 * 2
def baseEnd_202 : Nat := 103723092313443374077

theorem tailTrace_202 : CollatzResearch.WordTrace tailWord_202 prefixEnd_202 103723092313443374077 := by
  unfold tailWord_202
  simp only [CollatzResearch.WordTrace]
  refine ⟨1841886318915835990715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4911696850442229308573 1841886318915835990715)
  ·
    refine ⟨2762829478373753986073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1841886318915835990715 2762829478373753986073)
    ·
      refine ⟨2072122108780315489555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2762829478373753986073 2072122108780315489555)
      ·
        refine ⟨3108183163170473234333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2072122108780315489555 3108183163170473234333)
        ·
          refine ⟨1165568686188927462875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3108183163170473234333 1165568686188927462875)
          ·
            refine ⟨1748353029283391194313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165568686188927462875 1748353029283391194313)
            ·
              refine ⟨1311264771962543395735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1748353029283391194313 1311264771962543395735)
              ·
                refine ⟨1966897157943815093603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1311264771962543395735 1966897157943815093603)
                ·
                  refine ⟨2950345736915722640405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966897157943815093603 2950345736915722640405)
                  ·
                    refine ⟨138297456417924498769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2950345736915722640405 138297456417924498769)
                    ·
                      refine ⟨103723092313443374077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 138297456417924498769 103723092313443374077)
                      ·
                        rfl

theorem cell23_202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 1, 6, 2].length) (baseStart_202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_202 prefixEnd_202 := by exact prefixLift 202
  have htrace : WordTrace (prefixWord ++ tailWord_202) baseStart_202 baseEnd_202 := by
    simpa [prefixWord, tailWord_202, baseEnd_202] using wordTrace_append hprefix tailTrace_202
  have hstable : (prefixWord ++ tailWord_202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202).length < 2 ^ (prefixWord ++ tailWord_202).sum := by decide
  have hdescent : baseEnd_202 < baseStart_202 := by decide
  rcases family_descends (prefixWord ++ tailWord_202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242 : List Nat := [3, 2, 1, 3, 2, 1, 1, 4, 6]
def baseStart_242 : Nat := 118140960795 + 242 * 2 ^ 59
def prefixEnd_242 : Nat := 4983230072969 + 3 ^ 40 * 242 * 2
def baseEnd_242 : Nat := 13806924277031874877

theorem tailTrace_242 : CollatzResearch.WordTrace tailWord_242 prefixEnd_242 13806924277031874877 := by
  unfold tailWord_242
  simp only [CollatzResearch.WordTrace]
  refine ⟨2206616282687543854745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5884310087166783612653 2206616282687543854745)
  ·
    refine ⟨1654962212015657891059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2206616282687543854745 1654962212015657891059)
    ·
      refine ⟨2482443318023486836589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1654962212015657891059 2482443318023486836589)
      ·
        refine ⟨930916244258807563721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2482443318023486836589 930916244258807563721)
        ·
          refine ⟨698187183194105672791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 930916244258807563721 698187183194105672791)
          ·
            refine ⟨1047280774791158509187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698187183194105672791 1047280774791158509187)
            ·
              refine ⟨1570921162186737763781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1047280774791158509187 1570921162186737763781)
              ·
                refine ⟨294547717910013330709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1570921162186737763781 294547717910013330709)
                ·
                  refine ⟨13806924277031874877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 294547717910013330709 13806924277031874877)
                  ·
                    rfl

theorem cell23_242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242 prefixEnd_242 := by exact prefixLift 242
  have htrace : WordTrace (prefixWord ++ tailWord_242) baseStart_242 baseEnd_242 := by
    simpa [prefixWord, tailWord_242, baseEnd_242] using wordTrace_append hprefix tailTrace_242
  have hstable : (prefixWord ++ tailWord_242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242).length < 2 ^ (prefixWord ++ tailWord_242).sum := by decide
  have hdescent : baseEnd_242 < baseStart_242 := by decide
  rcases family_descends (prefixWord ++ tailWord_242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 5, 5]
def baseStart_255 : Nat := 118140960795 + 255 * 2 ^ 59
def prefixEnd_255 : Nat := 4983230072969 + 3 ^ 40 * 255 * 2
def baseEnd_255 : Nat := 43645855667245337111

theorem tailTrace_255 : CollatzResearch.WordTrace tailWord_255 prefixEnd_255 43645855667245337111 := by
  unfold tailWord_255
  simp only [CollatzResearch.WordTrace]
  refine ⟨9300614083653395642219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6200409389102263761479 9300614083653395642219)
  ·
    refine ⟨13950921125480093463329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9300614083653395642219 13950921125480093463329)
    ·
      refine ⟨10463190844110070097497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13950921125480093463329 10463190844110070097497)
      ·
        refine ⟨7847393133082552573123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10463190844110070097497 7847393133082552573123)
        ·
          refine ⟨11771089699623828859685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7847393133082552573123 11771089699623828859685)
          ·
            refine ⟨2207079318679467911191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11771089699623828859685 2207079318679467911191)
            ·
              refine ⟨3310618978019201866787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2207079318679467911191 3310618978019201866787)
              ·
                refine ⟨4965928467028802800181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3310618978019201866787 4965928467028802800181)
                ·
                  refine ⟨465555793783950262517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4965928467028802800181 465555793783950262517)
                  ·
                    refine ⟨43645855667245337111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 465555793783950262517 43645855667245337111)
                    ·
                      rfl

theorem cell23_255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 5].length) (baseStart_255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_255 prefixEnd_255 := by exact prefixLift 255
  have htrace : WordTrace (prefixWord ++ tailWord_255) baseStart_255 baseEnd_255 := by
    simpa [prefixWord, tailWord_255, baseEnd_255] using wordTrace_append hprefix tailTrace_255
  have hstable : (prefixWord ++ tailWord_255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255).length < 2 ^ (prefixWord ++ tailWord_255).sum := by decide
  have hdescent : baseEnd_255 < baseStart_255 := by decide
  rcases family_descends (prefixWord ++ tailWord_255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 1, 5, 2]
def baseStart_279 : Nat := 118140960795 + 279 * 2 ^ 59
def prefixEnd_279 : Nat := 4983230072969 + 3 ^ 40 * 279 * 2
def baseEnd_279 : Nat := 143261102709642111223

theorem tailTrace_279 : CollatzResearch.WordTrace tailWord_279 prefixEnd_279 143261102709642111223 := by
  unfold tailWord_279
  simp only [CollatzResearch.WordTrace]
  refine ⟨10175965996705494515891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6783977331136996343927 10175965996705494515891)
  ·
    refine ⟨15263948995058241773837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10175965996705494515891 15263948995058241773837)
    ·
      refine ⟨5723980873146840665189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15263948995058241773837 5723980873146840665189)
      ·
        refine ⟨1073246413715032624723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5723980873146840665189 1073246413715032624723)
        ·
          refine ⟨1609869620572548937085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1073246413715032624723 1609869620572548937085)
          ·
            refine ⟨603701107714705851407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1609869620572548937085 603701107714705851407)
            ·
              refine ⟨905551661572058777111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 603701107714705851407 905551661572058777111)
              ·
                refine ⟨1358327492358088165667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 905551661572058777111 1358327492358088165667)
                ·
                  refine ⟨2037491238537132248501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1358327492358088165667 2037491238537132248501)
                  ·
                    refine ⟨191014803612856148297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2037491238537132248501 191014803612856148297)
                    ·
                      refine ⟨143261102709642111223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 191014803612856148297 143261102709642111223)
                      ·
                        rfl

theorem cell23_279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279 prefixEnd_279 := by exact prefixLift 279
  have htrace : WordTrace (prefixWord ++ tailWord_279) baseStart_279 baseEnd_279 := by
    simpa [prefixWord, tailWord_279, baseEnd_279] using wordTrace_append hprefix tailTrace_279
  have hstable : (prefixWord ++ tailWord_279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279).length < 2 ^ (prefixWord ++ tailWord_279).sum := by decide
  have hdescent : baseEnd_279 < baseStart_279 := by decide
  rcases family_descends (prefixWord ++ tailWord_279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289 : List Nat := [1, 2, 3, 2, 1, 1, 6, 1, 1, 5]
def baseStart_289 : Nat := 118140960795 + 289 * 2 ^ 59
def prefixEnd_289 : Nat := 4983230072969 + 3 ^ 40 * 289 * 2
def baseEnd_289 : Nat := 49465303084867662059

theorem tailTrace_289 : CollatzResearch.WordTrace tailWord_289 prefixEnd_289 49465303084867662059 := by
  unfold tailWord_289
  simp only [CollatzResearch.WordTrace]
  refine ⟨10540695960477202379921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7027130640318134919947 10540695960477202379921)
  ·
    refine ⟨7905521970357901784941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10540695960477202379921 7905521970357901784941)
    ·
      refine ⟨2964570738884213169353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7905521970357901784941 2964570738884213169353)
      ·
        refine ⟨2223428054163159877015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2964570738884213169353 2223428054163159877015)
        ·
          refine ⟨3335142081244739815523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2223428054163159877015 3335142081244739815523)
          ·
            refine ⟨5002713121867109723285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3335142081244739815523 5002713121867109723285)
            ·
              refine ⟨234502177587520768279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5002713121867109723285 234502177587520768279)
              ·
                refine ⟨351753266381281152419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234502177587520768279 351753266381281152419)
                ·
                  refine ⟨527629899571921728629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 351753266381281152419 527629899571921728629)
                  ·
                    refine ⟨49465303084867662059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 527629899571921728629 49465303084867662059)
                    ·
                      rfl

theorem cell23_289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_289 prefixEnd_289 := by exact prefixLift 289
  have htrace : WordTrace (prefixWord ++ tailWord_289) baseStart_289 baseEnd_289 := by
    simpa [prefixWord, tailWord_289, baseEnd_289] using wordTrace_append hprefix tailTrace_289
  have hstable : (prefixWord ++ tailWord_289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289).length < 2 ^ (prefixWord ++ tailWord_289).sum := by decide
  have hdescent : baseEnd_289 < baseStart_289 := by decide
  rcases family_descends (prefixWord ++ tailWord_289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 5, 2, 3]
def baseStart_312 : Nat := 118140960795 + 312 * 2 ^ 59
def prefixEnd_312 : Nat := 4983230072969 + 3 ^ 40 * 312 * 2
def baseEnd_312 : Nat := 160205964308012998571

theorem tailTrace_312 : CollatzResearch.WordTrace tailWord_312 prefixEnd_312 160205964308012998571 := by
  unfold tailWord_312
  simp only [CollatzResearch.WordTrace]
  refine ⟨5689787438576065233595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7586383251434753644793 5689787438576065233595)
  ·
    refine ⟨8534681157864097850393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5689787438576065233595 8534681157864097850393)
    ·
      refine ⟨6401010868398073387795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8534681157864097850393 6401010868398073387795)
      ·
        refine ⟨9601516302597110081693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6401010868398073387795 9601516302597110081693)
        ·
          refine ⟨3600568613473916280635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9601516302597110081693 3600568613473916280635)
          ·
            refine ⟨5400852920210874420953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3600568613473916280635 5400852920210874420953)
            ·
              refine ⟨4050639690158155815715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5400852920210874420953 4050639690158155815715)
              ·
                refine ⟨6075959535237233723573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4050639690158155815715 6075959535237233723573)
                ·
                  refine ⟨569621206428490661585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6075959535237233723573 569621206428490661585)
                  ·
                    refine ⟨427215904821367996189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 569621206428490661585 427215904821367996189)
                    ·
                      refine ⟨160205964308012998571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 427215904821367996189 160205964308012998571)
                      ·
                        rfl

theorem cell23_312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 5, 2, 3].length) (baseStart_312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312 prefixEnd_312 := by exact prefixLift 312
  have htrace : WordTrace (prefixWord ++ tailWord_312) baseStart_312 baseEnd_312 := by
    simpa [prefixWord, tailWord_312, baseEnd_312] using wordTrace_append hprefix tailTrace_312
  have hstable : (prefixWord ++ tailWord_312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312).length < 2 ^ (prefixWord ++ tailWord_312).sum := by decide
  have hdescent : baseEnd_312 < baseStart_312 := by decide
  rcases family_descends (prefixWord ++ tailWord_312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 1, 9]
def baseStart_345 : Nat := 118140960795 + 345 * 2 ^ 59
def prefixEnd_345 : Nat := 4983230072969 + 3 ^ 40 * 345 * 2
def baseEnd_345 : Nat := 59050275302127961973

theorem tailTrace_345 : CollatzResearch.WordTrace tailWord_345 prefixEnd_345 59050275302127961973 := by
  unfold tailWord_345
  simp only [CollatzResearch.WordTrace]
  refine ⟨12583183757598766418489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8388789171732510945659 12583183757598766418489)
  ·
    refine ⟨9437387818199074813867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12583183757598766418489 9437387818199074813867)
    ·
      refine ⟨14156081727298612220801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9437387818199074813867 14156081727298612220801)
      ·
        refine ⟨10617061295473959165601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14156081727298612220801 10617061295473959165601)
        ·
          refine ⟨7962795971605469374201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10617061295473959165601 7962795971605469374201)
          ·
            refine ⟨5972096978704102030651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7962795971605469374201 5972096978704102030651)
            ·
              refine ⟨8958145468056153045977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5972096978704102030651 8958145468056153045977)
              ·
                refine ⟨6718609101042114784483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8958145468056153045977 6718609101042114784483)
                ·
                  refine ⟨10077913651563172176725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6718609101042114784483 10077913651563172176725)
                  ·
                    refine ⟨59050275302127961973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 10077913651563172176725 59050275302127961973)
                    ·
                      rfl

theorem cell23_345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 9].length) (baseStart_345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345 prefixEnd_345 := by exact prefixLift 345
  have htrace : WordTrace (prefixWord ++ tailWord_345) baseStart_345 baseEnd_345 := by
    simpa [prefixWord, tailWord_345, baseEnd_345] using wordTrace_append hprefix tailTrace_345
  have hstable : (prefixWord ++ tailWord_345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345).length < 2 ^ (prefixWord ++ tailWord_345).sum := by decide
  have hdescent : baseEnd_345 < baseStart_345 := by decide
  rcases family_descends (prefixWord ++ tailWord_345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 3, 3, 2]
def baseStart_369 : Nat := 118140960795 + 369 * 2 ^ 59
def prefixEnd_369 : Nat := 4983230072969 + 3 ^ 40 * 369 * 2
def baseEnd_369 : Nat := 189474361614289985809

theorem tailTrace_369 : CollatzResearch.WordTrace tailWord_369 prefixEnd_369 189474361614289985809 := by
  unfold tailWord_369
  simp only [CollatzResearch.WordTrace]
  refine ⟨13458535670650865292161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8972357113767243528107 13458535670650865292161)
  ·
    refine ⟨10093901752988148969121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13458535670650865292161 10093901752988148969121)
    ·
      refine ⟨7570426314741111726841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10093901752988148969121 7570426314741111726841)
      ·
        refine ⟨5677819736055833795131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7570426314741111726841 5677819736055833795131)
        ·
          refine ⟨8516729604083750692697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5677819736055833795131 8516729604083750692697)
          ·
            refine ⟨6387547203062813019523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8516729604083750692697 6387547203062813019523)
            ·
              refine ⟨9581320804594219529285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6387547203062813019523 9581320804594219529285)
              ·
                refine ⟨1796497650861416161741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9581320804594219529285 1796497650861416161741)
                ·
                  refine ⟨673686619073031060653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1796497650861416161741 673686619073031060653)
                  ·
                    refine ⟨252632482152386647745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 673686619073031060653 252632482152386647745)
                    ·
                      refine ⟨189474361614289985809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 252632482152386647745 189474361614289985809)
                      ·
                        rfl

theorem cell23_369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 3, 2].length) (baseStart_369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369 prefixEnd_369 := by exact prefixLift 369
  have htrace : WordTrace (prefixWord ++ tailWord_369) baseStart_369 baseEnd_369 := by
    simpa [prefixWord, tailWord_369, baseEnd_369] using wordTrace_append hprefix tailTrace_369
  have hstable : (prefixWord ++ tailWord_369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369).length < 2 ^ (prefixWord ++ tailWord_369).sum := by decide
  have hdescent : baseEnd_369 < baseStart_369 := by decide
  rcases family_descends (prefixWord ++ tailWord_369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433 : List Nat := [1, 2, 2, 4, 1, 2, 2, 3, 2, 2, 2]
def baseStart_433 : Nat := 118140960795 + 433 * 2 ^ 59
def prefixEnd_433 : Nat := 4983230072969 + 3 ^ 40 * 433 * 2
def baseEnd_433 : Nat := 222337123502039585515

theorem tailTrace_433 : CollatzResearch.WordTrace tailWord_433 prefixEnd_433 222337123502039585515 := by
  unfold tailWord_433
  simp only [CollatzResearch.WordTrace]
  refine ⟨15792807438789795621953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10528538292526530414635 15792807438789795621953)
  ·
    refine ⟨11844605579092346716465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15792807438789795621953 11844605579092346716465)
    ·
      refine ⟨8883454184319260037349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11844605579092346716465 8883454184319260037349)
      ·
        refine ⟨1665647659559861257003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8883454184319260037349 1665647659559861257003)
        ·
          refine ⟨2498471489339791885505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1665647659559861257003 2498471489339791885505)
          ·
            refine ⟨1873853617004843914129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2498471489339791885505 1873853617004843914129)
            ·
              refine ⟨1405390212753632935597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1873853617004843914129 1405390212753632935597)
              ·
                refine ⟨527021329782612350849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1405390212753632935597 527021329782612350849)
                ·
                  refine ⟨395265997336959263137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527021329782612350849 395265997336959263137)
                  ·
                    refine ⟨296449498002719447353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 395265997336959263137 296449498002719447353)
                    ·
                      refine ⟨222337123502039585515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 296449498002719447353 222337123502039585515)
                      ·
                        rfl

theorem cell23_433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433 prefixEnd_433 := by exact prefixLift 433
  have htrace : WordTrace (prefixWord ++ tailWord_433) baseStart_433 baseEnd_433 := by
    simpa [prefixWord, tailWord_433, baseEnd_433] using wordTrace_append hprefix tailTrace_433
  have hstable : (prefixWord ++ tailWord_433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433).length < 2 ^ (prefixWord ++ tailWord_433).sum := by decide
  have hdescent : baseEnd_433 < baseStart_433 := by decide
  rcases family_descends (prefixWord ++ tailWord_433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456 : List Nat := [2, 1, 3, 1, 3, 3, 2, 3, 5]
def baseStart_456 : Nat := 118140960795 + 456 * 2 ^ 59
def prefixEnd_456 : Nat := 4983230072969 + 3 ^ 40 * 456 * 2
def baseEnd_456 : Nat := 26016353172827733101

theorem tailTrace_456 : CollatzResearch.WordTrace tailWord_456 prefixEnd_456 26016353172827733101 := by
  unfold tailWord_456
  simp only [CollatzResearch.WordTrace]
  refine ⟨8315843177732361854611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11087790903643149139481 8315843177732361854611)
  ·
    refine ⟨12473764766598542781917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8315843177732361854611 12473764766598542781917)
    ·
      refine ⟨4677661787474453543219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12473764766598542781917 4677661787474453543219)
      ·
        refine ⟨7016492681211680314829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4677661787474453543219 7016492681211680314829)
        ·
          refine ⟨2631184755454380118061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7016492681211680314829 2631184755454380118061)
          ·
            refine ⟨986694283295392544273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2631184755454380118061 986694283295392544273)
            ·
              refine ⟨740020712471544408205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 986694283295392544273 740020712471544408205)
              ·
                refine ⟨277507767176829153077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 740020712471544408205 277507767176829153077)
                ·
                  refine ⟨26016353172827733101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 277507767176829153077 26016353172827733101)
                  ·
                    rfl

theorem cell23_456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 5].length) (baseStart_456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456 prefixEnd_456 := by exact prefixLift 456
  have htrace : WordTrace (prefixWord ++ tailWord_456) baseStart_456 baseEnd_456 := by
    simpa [prefixWord, tailWord_456, baseEnd_456] using wordTrace_append hprefix tailTrace_456
  have hstable : (prefixWord ++ tailWord_456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456).length < 2 ^ (prefixWord ++ tailWord_456).sum := by decide
  have hdescent : baseEnd_456 < baseStart_456 := by decide
  rcases family_descends (prefixWord ++ tailWord_456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 1, 6, 2]
def baseStart_489 : Nat := 118140960795 + 489 * 2 ^ 59
def prefixEnd_489 : Nat := 4983230072969 + 3 ^ 40 * 489 * 2
def baseEnd_489 : Nat := 251092040153820485257

theorem tailTrace_489 : CollatzResearch.WordTrace tailWord_489 prefixEnd_489 251092040153820485257 := by
  unfold tailWord_489
  simp only [CollatzResearch.WordTrace]
  refine ⟨17835295235911359660521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11890196823940906440347 17835295235911359660521)
  ·
    refine ⟨13376471426933519745391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17835295235911359660521 13376471426933519745391)
    ·
      refine ⟨20064707140400279618087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13376471426933519745391 20064707140400279618087)
      ·
        refine ⟨30097060710600419427131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20064707140400279618087 30097060710600419427131)
        ·
          refine ⟨45145591065900629140697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30097060710600419427131 45145591065900629140697)
          ·
            refine ⟨33859193299425471855523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45145591065900629140697 33859193299425471855523)
            ·
              refine ⟨50788789949138207783285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33859193299425471855523 50788789949138207783285)
              ·
                refine ⟨4761449057731706979683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50788789949138207783285 4761449057731706979683)
                ·
                  refine ⟨7142173586597560469525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4761449057731706979683 7142173586597560469525)
                  ·
                    refine ⟨334789386871760647009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7142173586597560469525 334789386871760647009)
                    ·
                      refine ⟨251092040153820485257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 334789386871760647009 251092040153820485257)
                      ·
                        rfl

theorem cell23_489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 6, 2].length) (baseStart_489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_489 prefixEnd_489 := by exact prefixLift 489
  have htrace : WordTrace (prefixWord ++ tailWord_489) baseStart_489 baseEnd_489 := by
    simpa [prefixWord, tailWord_489, baseEnd_489] using wordTrace_append hprefix tailTrace_489
  have hstable : (prefixWord ++ tailWord_489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489).length < 2 ^ (prefixWord ++ tailWord_489).sum := by decide
  have hdescent : baseEnd_489 < baseStart_489 := by decide
  rcases family_descends (prefixWord ++ tailWord_489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499 : List Nat := [1, 1, 1, 2, 2, 2, 3, 4, 3, 4]
def baseStart_499 : Nat := 118140960795 + 499 * 2 ^ 59
def prefixEnd_499 : Nat := 4983230072969 + 3 ^ 40 * 499 * 2
def baseEnd_499 : Nat := 85408948899593786737

theorem tailTrace_499 : CollatzResearch.WordTrace tailWord_499 prefixEnd_499 85408948899593786737 := by
  unfold tailWord_499
  simp only [CollatzResearch.WordTrace]
  refine ⟨18200025199683067524551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12133350133122045016367 18200025199683067524551)
  ·
    refine ⟨27300037799524601286827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18200025199683067524551 27300037799524601286827)
    ·
      refine ⟨40950056699286901930241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27300037799524601286827 40950056699286901930241)
      ·
        refine ⟨30712542524465176447681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40950056699286901930241 30712542524465176447681)
        ·
          refine ⟨23034406893348882335761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30712542524465176447681 23034406893348882335761)
          ·
            refine ⟨17275805170011661751821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23034406893348882335761 17275805170011661751821)
            ·
              refine ⟨6478426938754373156933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17275805170011661751821 6478426938754373156933)
              ·
                refine ⟨1214705051016444966925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6478426938754373156933 1214705051016444966925)
                ·
                  refine ⟨455514394131166862597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1214705051016444966925 455514394131166862597)
                  ·
                    refine ⟨85408948899593786737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 455514394131166862597 85408948899593786737)
                    ·
                      rfl

theorem cell23_499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 4].length) (baseStart_499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499 prefixEnd_499 := by exact prefixLift 499
  have htrace : WordTrace (prefixWord ++ tailWord_499) baseStart_499 baseEnd_499 := by
    simpa [prefixWord, tailWord_499, baseEnd_499] using wordTrace_append hprefix tailTrace_499
  have hstable : (prefixWord ++ tailWord_499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499).length < 2 ^ (prefixWord ++ tailWord_499).sum := by decide
  have hdescent : baseEnd_499 < baseStart_499 := by decide
  rcases family_descends (prefixWord ++ tailWord_499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 1, 4, 3]
def baseStart_509 : Nat := 118140960795 + 509 * 2 ^ 59
def prefixEnd_509 : Nat := 4983230072969 + 3 ^ 40 * 509 * 2
def baseEnd_509 : Nat := 261361653243742235165

theorem tailTrace_509 : CollatzResearch.WordTrace tailWord_509 prefixEnd_509 261361653243742235165 := by
  unfold tailWord_509
  simp only [CollatzResearch.WordTrace]
  refine ⟨18564755163454775388581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12376503442303183592387 18564755163454775388581)
  ·
    refine ⟨3480891593147770385359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18564755163454775388581 3480891593147770385359)
    ·
      refine ⟨5221337389721655578039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3480891593147770385359 5221337389721655578039)
      ·
        refine ⟨7832006084582483367059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5221337389721655578039 7832006084582483367059)
        ·
          refine ⟨11748009126873725050589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7832006084582483367059 11748009126873725050589)
          ·
            refine ⟨4405503422577646893971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11748009126873725050589 4405503422577646893971)
            ·
              refine ⟨6608255133866470340957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4405503422577646893971 6608255133866470340957)
              ·
                refine ⟨2478095675199926377859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6608255133866470340957 2478095675199926377859)
                ·
                  refine ⟨3717143512799889566789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2478095675199926377859 3717143512799889566789)
                  ·
                    refine ⟨696964408649979293773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3717143512799889566789 696964408649979293773)
                    ·
                      refine ⟨261361653243742235165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 696964408649979293773 261361653243742235165)
                      ·
                        rfl

theorem cell23_509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509 prefixEnd_509 := by exact prefixLift 509
  have htrace : WordTrace (prefixWord ++ tailWord_509) baseStart_509 baseEnd_509 := by
    simpa [prefixWord, tailWord_509, baseEnd_509] using wordTrace_append hprefix tailTrace_509
  have hstable : (prefixWord ++ tailWord_509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509).length < 2 ^ (prefixWord ++ tailWord_509).sum := by decide
  have hdescent : baseEnd_509 < baseStart_509 := by decide
  rcases family_descends (prefixWord ++ tailWord_509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3]
def baseStart_526 : Nat := 118140960795 + 526 * 2 ^ 59
def prefixEnd_526 : Nat := 4983230072969 + 3 ^ 40 * 526 * 2
def baseEnd_526 : Nat := 270090824370175722587

theorem tailTrace_526 : CollatzResearch.WordTrace tailWord_526 prefixEnd_526 270090824370175722587 := by
  unfold tailWord_526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2398099512733334844679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12789864067911119171621 2398099512733334844679)
  ·
    refine ⟨3597149269100002267019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2398099512733334844679 3597149269100002267019)
    ·
      refine ⟨5395723903650003400529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3597149269100002267019 5395723903650003400529)
      ·
        refine ⟨4046792927737502550397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5395723903650003400529 4046792927737502550397)
        ·
          refine ⟨1517547347901563456399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4046792927737502550397 1517547347901563456399)
          ·
            refine ⟨2276321021852345184599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1517547347901563456399 2276321021852345184599)
            ·
              refine ⟨3414481532778517776899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2276321021852345184599 3414481532778517776899)
              ·
                refine ⟨5121722299167776665349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3414481532778517776899 5121722299167776665349)
                ·
                  refine ⟨960322931093958124753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5121722299167776665349 960322931093958124753)
                  ·
                    refine ⟨720242198320468593565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 960322931093958124753 720242198320468593565)
                    ·
                      refine ⟨270090824370175722587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 720242198320468593565 270090824370175722587)
                      ·
                        rfl

theorem cell23_526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_526 prefixEnd_526 := by exact prefixLift 526
  have htrace : WordTrace (prefixWord ++ tailWord_526) baseStart_526 baseEnd_526 := by
    simpa [prefixWord, tailWord_526, baseEnd_526] using wordTrace_append hprefix tailTrace_526
  have hstable : (prefixWord ++ tailWord_526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526).length < 2 ^ (prefixWord ++ tailWord_526).sum := by decide
  have hdescent : baseEnd_526 < baseStart_526 := by decide
  rcases family_descends (prefixWord ++ tailWord_526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556 : List Nat := [2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 3]
def baseStart_556 : Nat := 118140960795 + 556 * 2 ^ 59
def prefixEnd_556 : Nat := 4983230072969 + 3 ^ 40 * 556 * 2
def baseEnd_556 : Nat := 285495244005058347449

theorem tailTrace_556 : CollatzResearch.WordTrace tailWord_556 prefixEnd_556 285495244005058347449 := by
  unfold tailWord_556
  simp only [CollatzResearch.WordTrace]
  refine ⟨10139492996590901174761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13519323995454534899681 10139492996590901174761)
  ·
    refine ⟨7604619747443175881071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10139492996590901174761 7604619747443175881071)
    ·
      refine ⟨11406929621164763821607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7604619747443175881071 11406929621164763821607)
      ·
        refine ⟨17110394431747145732411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11406929621164763821607 17110394431747145732411)
        ·
          refine ⟨25665591647620718598617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17110394431747145732411 25665591647620718598617)
          ·
            refine ⟨19249193735715538948963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25665591647620718598617 19249193735715538948963)
            ·
              refine ⟨28873790603573308423445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19249193735715538948963 28873790603573308423445)
              ·
                refine ⟨1353458934542498832349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28873790603573308423445 1353458934542498832349)
                ·
                  refine ⟨507547100453437062131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1353458934542498832349 507547100453437062131)
                  ·
                    refine ⟨761320650680155593197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 507547100453437062131 761320650680155593197)
                    ·
                      refine ⟨285495244005058347449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 761320650680155593197 285495244005058347449)
                      ·
                        rfl

theorem cell23_556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 3].length) (baseStart_556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556 prefixEnd_556 := by exact prefixLift 556
  have htrace : WordTrace (prefixWord ++ tailWord_556) baseStart_556 baseEnd_556 := by
    simpa [prefixWord, tailWord_556, baseEnd_556] using wordTrace_append hprefix tailTrace_556
  have hstable : (prefixWord ++ tailWord_556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556).length < 2 ^ (prefixWord ++ tailWord_556).sum := by decide
  have hdescent : baseEnd_556 < baseStart_556 := by decide
  rcases family_descends (prefixWord ++ tailWord_556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557 : List Nat := [1, 5, 4, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_557 : Nat := 118140960795 + 557 * 2 ^ 59
def prefixEnd_557 : Nat := 4983230072969 + 3 ^ 40 * 557 * 2
def baseEnd_557 : Nat := 286008724659554434945

theorem tailTrace_557 : CollatzResearch.WordTrace tailWord_557 prefixEnd_557 286008724659554434945 := by
  unfold tailWord_557
  simp only [CollatzResearch.WordTrace]
  refine ⟨20315458989558973135925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13543639326372648757283 20315458989558973135925)
  ·
    refine ⟨1904574280271153731493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20315458989558973135925 1904574280271153731493)
    ·
      refine ⟨357107677550841324655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1904574280271153731493 357107677550841324655)
      ·
        refine ⟨535661516326261986983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357107677550841324655 535661516326261986983)
        ·
          refine ⟨803492274489392980475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535661516326261986983 803492274489392980475)
          ·
            refine ⟨1205238411734089470713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 803492274489392980475 1205238411734089470713)
            ·
              refine ⟨903928808800567103035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1205238411734089470713 903928808800567103035)
              ·
                refine ⟨1355893213200850654553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 903928808800567103035 1355893213200850654553)
                ·
                  refine ⟨1016919909900637990915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1355893213200850654553 1016919909900637990915)
                  ·
                    refine ⟨1525379864850956986373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1016919909900637990915 1525379864850956986373)
                    ·
                      refine ⟨286008724659554434945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1525379864850956986373 286008724659554434945)
                      ·
                        rfl

theorem cell23_557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557 prefixEnd_557 := by exact prefixLift 557
  have htrace : WordTrace (prefixWord ++ tailWord_557) baseStart_557 baseEnd_557 := by
    simpa [prefixWord, tailWord_557, baseEnd_557] using wordTrace_append hprefix tailTrace_557
  have hstable : (prefixWord ++ tailWord_557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557).length < 2 ^ (prefixWord ++ tailWord_557).sum := by decide
  have hdescent : baseEnd_557 < baseStart_557 := by decide
  rcases family_descends (prefixWord ++ tailWord_557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583 : List Nat := [1, 1, 4, 1, 4, 1, 2, 2, 2, 3, 2]
def baseStart_583 : Nat := 118140960795 + 583 * 2 ^ 59
def prefixEnd_583 : Nat := 4983230072969 + 3 ^ 40 * 583 * 2
def baseEnd_583 : Nat := 299359221676452709825

theorem tailTrace_583 : CollatzResearch.WordTrace tailWord_583 prefixEnd_583 299359221676452709825 := by
  unfold tailWord_583
  simp only [CollatzResearch.WordTrace]
  refine ⟨21263756895365413582403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14175837930243609054935 21263756895365413582403)
  ·
    refine ⟨31895635343048120373605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21263756895365413582403 31895635343048120373605)
    ·
      refine ⟨5980431626821522570051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31895635343048120373605 5980431626821522570051)
      ·
        refine ⟨8970647440232283855077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5980431626821522570051 8970647440232283855077)
        ·
          refine ⟨1681996395043553222827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8970647440232283855077 1681996395043553222827)
          ·
            refine ⟨2522994592565329834241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1681996395043553222827 2522994592565329834241)
            ·
              refine ⟨1892245944423997375681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2522994592565329834241 1892245944423997375681)
              ·
                refine ⟨1419184458317998031761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1892245944423997375681 1419184458317998031761)
                ·
                  refine ⟨1064388343738498523821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1419184458317998031761 1064388343738498523821)
                  ·
                    refine ⟨399145628901936946433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1064388343738498523821 399145628901936946433)
                    ·
                      refine ⟨299359221676452709825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 399145628901936946433 299359221676452709825)
                      ·
                        rfl

theorem cell23_583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 3, 2].length) (baseStart_583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583 prefixEnd_583 := by exact prefixLift 583
  have htrace : WordTrace (prefixWord ++ tailWord_583) baseStart_583 baseEnd_583 := by
    simpa [prefixWord, tailWord_583, baseEnd_583] using wordTrace_append hprefix tailTrace_583
  have hstable : (prefixWord ++ tailWord_583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583).length < 2 ^ (prefixWord ++ tailWord_583).sum := by decide
  have hdescent : baseEnd_583 < baseStart_583 := by decide
  rcases family_descends (prefixWord ++ tailWord_583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_596 : Nat := 118140960795 + 596 * 2 ^ 59
def prefixEnd_596 : Nat := 4983230072969 + 3 ^ 40 * 596 * 2
def baseEnd_596 : Nat := 306034470184901847265

theorem tailTrace_596 : CollatzResearch.WordTrace tailWord_596 prefixEnd_596 306034470184901847265 := by
  unfold tailWord_596
  simp only [CollatzResearch.WordTrace]
  refine ⟨10868952924134316902821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14491937232179089203761 10868952924134316902821)
  ·
    refine ⟨2037928673275184419279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10868952924134316902821 2037928673275184419279)
    ·
      refine ⟨3056893009912776628919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2037928673275184419279 3056893009912776628919)
      ·
        refine ⟨4585339514869164943379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3056893009912776628919 4585339514869164943379)
        ·
          refine ⟨6878009272303747415069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4585339514869164943379 6878009272303747415069)
          ·
            refine ⟨2579253477113905280651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6878009272303747415069 2579253477113905280651)
            ·
              refine ⟨3868880215670857920977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2579253477113905280651 3868880215670857920977)
              ·
                refine ⟨2901660161753143440733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3868880215670857920977 2901660161753143440733)
                ·
                  refine ⟨1088122560657428790275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2901660161753143440733 1088122560657428790275)
                  ·
                    refine ⟨1632183840986143185413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1088122560657428790275 1632183840986143185413)
                    ·
                      refine ⟨306034470184901847265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1632183840986143185413 306034470184901847265)
                      ·
                        rfl

theorem cell23_596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596 prefixEnd_596 := by exact prefixLift 596
  have htrace : WordTrace (prefixWord ++ tailWord_596) baseStart_596 baseEnd_596 := by
    simpa [prefixWord, tailWord_596, baseEnd_596] using wordTrace_append hprefix tailTrace_596
  have hstable : (prefixWord ++ tailWord_596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596).length < 2 ^ (prefixWord ++ tailWord_596).sum := by decide
  have hdescent : baseEnd_596 < baseStart_596 := by decide
  rcases family_descends (prefixWord ++ tailWord_596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 5]
def baseStart_599 : Nat := 118140960795 + 599 * 2 ^ 59
def prefixEnd_599 : Nat := 4983230072969 + 3 ^ 40 * 599 * 2
def baseEnd_599 : Nat := 307574912148390109751

theorem tailTrace_599 : CollatzResearch.WordTrace tailWord_599 prefixEnd_599 307574912148390109751 := by
  unfold tailWord_599
  simp only [CollatzResearch.WordTrace]
  refine ⟨21847324837400146164851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14564883224933430776567 21847324837400146164851)
  ·
    refine ⟨32770987256100219247277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21847324837400146164851 32770987256100219247277)
    ·
      refine ⟨12289120221037582217729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32770987256100219247277 12289120221037582217729)
      ·
        refine ⟨9216840165778186663297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12289120221037582217729 9216840165778186663297)
        ·
          refine ⟨6912630124333639997473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9216840165778186663297 6912630124333639997473)
          ·
            refine ⟨5184472593250229998105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6912630124333639997473 5184472593250229998105)
            ·
              refine ⟨3888354444937672498579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5184472593250229998105 3888354444937672498579)
              ·
                refine ⟨5832531667406508747869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3888354444937672498579 5832531667406508747869)
                ·
                  refine ⟨2187199375277440780451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5832531667406508747869 2187199375277440780451)
                  ·
                    refine ⟨3280799062916161170677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2187199375277440780451 3280799062916161170677)
                    ·
                      refine ⟨307574912148390109751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3280799062916161170677 307574912148390109751)
                      ·
                        rfl

theorem cell23_599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599 prefixEnd_599 := by exact prefixLift 599
  have htrace : WordTrace (prefixWord ++ tailWord_599) baseStart_599 baseEnd_599 := by
    simpa [prefixWord, tailWord_599, baseEnd_599] using wordTrace_append hprefix tailTrace_599
  have hstable : (prefixWord ++ tailWord_599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599).length < 2 ^ (prefixWord ++ tailWord_599).sum := by decide
  have hdescent : baseEnd_599 < baseStart_599 := by decide
  rcases family_descends (prefixWord ++ tailWord_599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630 : List Nat := [5, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4]
def baseStart_630 : Nat := 118140960795 + 630 * 2 ^ 59
def prefixEnd_630 : Nat := 4983230072969 + 3 ^ 40 * 630 * 2
def baseEnd_630 : Nat := 323492812437768822109

theorem tailTrace_630 : CollatzResearch.WordTrace tailWord_630 prefixEnd_630 323492812437768822109 := by
  unfold tailWord_630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1436124232818277533959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15318658483394960362229 1436124232818277533959)
  ·
    refine ⟨2154186349227416300939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1436124232818277533959 2154186349227416300939)
    ·
      refine ⟨3231279523841124451409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2154186349227416300939 3231279523841124451409)
      ·
        refine ⟨2423459642880843338557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3231279523841124451409 2423459642880843338557)
        ·
          refine ⟨908797366080316251959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2423459642880843338557 908797366080316251959)
          ·
            refine ⟨1363196049120474377939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 908797366080316251959 1363196049120474377939)
            ·
              refine ⟨2044794073680711566909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1363196049120474377939 2044794073680711566909)
              ·
                refine ⟨766797777630266837591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2044794073680711566909 766797777630266837591)
                ·
                  refine ⟨1150196666445400256387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 766797777630266837591 1150196666445400256387)
                  ·
                    refine ⟨1725294999668100384581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1150196666445400256387 1725294999668100384581)
                    ·
                      refine ⟨323492812437768822109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1725294999668100384581 323492812437768822109)
                      ·
                        rfl

theorem cell23_630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630 prefixEnd_630 := by exact prefixLift 630
  have htrace : WordTrace (prefixWord ++ tailWord_630) baseStart_630 baseEnd_630 := by
    simpa [prefixWord, tailWord_630, baseEnd_630] using wordTrace_append hprefix tailTrace_630
  have hstable : (prefixWord ++ tailWord_630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630).length < 2 ^ (prefixWord ++ tailWord_630).sum := by decide
  have hdescent : baseEnd_630 < baseStart_630 := by decide
  rcases family_descends (prefixWord ++ tailWord_630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633 : List Nat := [1, 2, 1, 3, 3, 3, 1, 3, 1, 2, 3]
def baseStart_633 : Nat := 118140960795 + 633 * 2 ^ 59
def prefixEnd_633 : Nat := 4983230072969 + 3 ^ 40 * 633 * 2
def baseEnd_633 : Nat := 325033254401257084595

theorem tailTrace_633 : CollatzResearch.WordTrace tailWord_633 prefixEnd_633 325033254401257084595 := by
  unfold tailWord_633
  simp only [CollatzResearch.WordTrace]
  refine ⟨23087406714223952902553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15391604476149301935035 23087406714223952902553)
  ·
    refine ⟨17315555035667964676915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23087406714223952902553 17315555035667964676915)
    ·
      refine ⟨25973332553501947015373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17315555035667964676915 25973332553501947015373)
      ·
        refine ⟨9739999707563230130765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25973332553501947015373 9739999707563230130765)
        ·
          refine ⟨3652499890336211299037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9739999707563230130765 3652499890336211299037)
          ·
            refine ⟨1369687458876079237139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3652499890336211299037 1369687458876079237139)
            ·
              refine ⟨2054531188314118855709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1369687458876079237139 2054531188314118855709)
              ·
                refine ⟨770449195617794570891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2054531188314118855709 770449195617794570891)
                ·
                  refine ⟨1155673793426691856337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 770449195617794570891 1155673793426691856337)
                  ·
                    refine ⟨866755345070018892253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1155673793426691856337 866755345070018892253)
                    ·
                      refine ⟨325033254401257084595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 866755345070018892253 325033254401257084595)
                      ·
                        rfl

theorem cell23_633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633 prefixEnd_633 := by exact prefixLift 633
  have htrace : WordTrace (prefixWord ++ tailWord_633) baseStart_633 baseEnd_633 := by
    simpa [prefixWord, tailWord_633, baseEnd_633] using wordTrace_append hprefix tailTrace_633
  have hstable : (prefixWord ++ tailWord_633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633).length < 2 ^ (prefixWord ++ tailWord_633).sum := by decide
  have hdescent : baseEnd_633 < baseStart_633 := by decide
  rcases family_descends (prefixWord ++ tailWord_633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660 : List Nat := [2, 4, 2, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_660 : Nat := 118140960795 + 660 * 2 ^ 59
def prefixEnd_660 : Nat := 4983230072969 + 3 ^ 40 * 660 * 2
def baseEnd_660 : Nat := 338897232072651446971

theorem tailTrace_660 : CollatzResearch.WordTrace tailWord_660 prefixEnd_660 338897232072651446971 := by
  unfold tailWord_660
  simp only [CollatzResearch.WordTrace]
  refine ⟨12036088808203782067717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16048118410938376090289 12036088808203782067717)
  ·
    refine ⟨2256766651538209137697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12036088808203782067717 2256766651538209137697)
    ·
      refine ⟨1692574988653656853273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2256766651538209137697 1692574988653656853273)
      ·
        refine ⟨1269431241490242639955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1692574988653656853273 1269431241490242639955)
        ·
          refine ⟨1904146862235363959933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1269431241490242639955 1904146862235363959933)
          ·
            refine ⟨714055073338261484975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1904146862235363959933 714055073338261484975)
            ·
              refine ⟨1071082610007392227463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714055073338261484975 1071082610007392227463)
              ·
                refine ⟨1606623915011088341195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1071082610007392227463 1606623915011088341195)
                ·
                  refine ⟨2409935872516632511793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1606623915011088341195 2409935872516632511793)
                  ·
                    refine ⟨1807451904387474383845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2409935872516632511793 1807451904387474383845)
                    ·
                      refine ⟨338897232072651446971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1807451904387474383845 338897232072651446971)
                      ·
                        rfl

theorem cell23_660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660 prefixEnd_660 := by exact prefixLift 660
  have htrace : WordTrace (prefixWord ++ tailWord_660) baseStart_660 baseEnd_660 := by
    simpa [prefixWord, tailWord_660, baseEnd_660] using wordTrace_append hprefix tailTrace_660
  have hstable : (prefixWord ++ tailWord_660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660).length < 2 ^ (prefixWord ++ tailWord_660).sum := by decide
  have hdescent : baseEnd_660 < baseStart_660 := by decide
  rcases family_descends (prefixWord ++ tailWord_660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724 : List Nat := [2, 4, 1, 3, 2, 2, 1, 2, 1, 3, 2]
def baseStart_724 : Nat := 118140960795 + 724 * 2 ^ 59
def prefixEnd_724 : Nat := 4983230072969 + 3 ^ 40 * 724 * 2
def baseEnd_724 : Nat := 371759993960401046677

theorem tailTrace_724 : CollatzResearch.WordTrace tailWord_724 prefixEnd_724 371759993960401046677 := by
  unfold tailWord_724
  simp only [CollatzResearch.WordTrace]
  refine ⟨13203224692273247232613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17604299589697662976817 13203224692273247232613)
  ·
    refine ⟨2475604629801233856115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13203224692273247232613 2475604629801233856115)
    ·
      refine ⟨3713406944701850784173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2475604629801233856115 3713406944701850784173)
      ·
        refine ⟨1392527604263194044065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3713406944701850784173 1392527604263194044065)
        ·
          refine ⟨1044395703197395533049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1392527604263194044065 1044395703197395533049)
          ·
            refine ⟨783296777398046649787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1044395703197395533049 783296777398046649787)
            ·
              refine ⟨1174945166097069974681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783296777398046649787 1174945166097069974681)
              ·
                refine ⟨881208874572802481011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1174945166097069974681 881208874572802481011)
                ·
                  refine ⟨1321813311859203721517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 881208874572802481011 1321813311859203721517)
                  ·
                    refine ⟨495679991947201395569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1321813311859203721517 495679991947201395569)
                    ·
                      refine ⟨371759993960401046677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 495679991947201395569 371759993960401046677)
                      ·
                        rfl

theorem cell23_724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_724 prefixEnd_724 := by exact prefixLift 724
  have htrace : WordTrace (prefixWord ++ tailWord_724) baseStart_724 baseEnd_724 := by
    simpa [prefixWord, tailWord_724, baseEnd_724] using wordTrace_append hprefix tailTrace_724
  have hstable : (prefixWord ++ tailWord_724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724).length < 2 ^ (prefixWord ++ tailWord_724).sum := by decide
  have hdescent : baseEnd_724 < baseStart_724 := by decide
  rcases family_descends (prefixWord ++ tailWord_724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 3]
def baseStart_736 : Nat := 118140960795 + 736 * 2 ^ 59
def prefixEnd_736 : Nat := 4983230072969 + 3 ^ 40 * 736 * 2
def baseEnd_736 : Nat := 377921761814354096621

theorem tailTrace_736 : CollatzResearch.WordTrace tailWord_736 prefixEnd_736 377921761814354096621 := by
  unfold tailWord_736
  simp only [CollatzResearch.WordTrace]
  refine ⟨13422062670536271951031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17896083560715029268041 13422062670536271951031)
  ·
    refine ⟨20133094005804407926547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13422062670536271951031 20133094005804407926547)
    ·
      refine ⟨30199641008706611889821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20133094005804407926547 30199641008706611889821)
      ·
        refine ⟨11324865378264979458683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30199641008706611889821 11324865378264979458683)
        ·
          refine ⟨16987298067397469188025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11324865378264979458683 16987298067397469188025)
          ·
            refine ⟨12740473550548101891019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16987298067397469188025 12740473550548101891019)
            ·
              refine ⟨19110710325822152836529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12740473550548101891019 19110710325822152836529)
              ·
                refine ⟨14333032744366614627397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19110710325822152836529 14333032744366614627397)
                ·
                  refine ⟨2687443639568740242637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14333032744366614627397 2687443639568740242637)
                  ·
                    refine ⟨1007791364838277590989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2687443639568740242637 1007791364838277590989)
                    ·
                      refine ⟨377921761814354096621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1007791364838277590989 377921761814354096621)
                      ·
                        rfl

theorem cell23_736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_736 prefixEnd_736 := by exact prefixLift 736
  have htrace : WordTrace (prefixWord ++ tailWord_736) baseStart_736 baseEnd_736 := by
    simpa [prefixWord, tailWord_736, baseEnd_736] using wordTrace_append hprefix tailTrace_736
  have hstable : (prefixWord ++ tailWord_736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736).length < 2 ^ (prefixWord ++ tailWord_736).sum := by decide
  have hdescent : baseEnd_736 < baseStart_736 := by decide
  rcases family_descends (prefixWord ++ tailWord_736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_770 : Nat := 118140960795 + 770 * 2 ^ 59
def prefixEnd_770 : Nat := 4983230072969 + 3 ^ 40 * 770 * 2
def baseEnd_770 : Nat := 395380104067221071465

theorem tailTrace_770 : CollatzResearch.WordTrace tailWord_770 prefixEnd_770 395380104067221071465 := by
  unfold tailWord_770
  simp only [CollatzResearch.WordTrace]
  refine ⟨7021051804474087659941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18722804811930900426509 7021051804474087659941)
  ·
    refine ⟨1316447213338891436239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7021051804474087659941 1316447213338891436239)
    ·
      refine ⟨1974670820008337154359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1316447213338891436239 1974670820008337154359)
      ·
        refine ⟨2962006230012505731539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1974670820008337154359 2962006230012505731539)
        ·
          refine ⟨4443009345018758597309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2962006230012505731539 4443009345018758597309)
          ·
            refine ⟨1666128504382034473991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4443009345018758597309 1666128504382034473991)
            ·
              refine ⟨2499192756573051710987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1666128504382034473991 2499192756573051710987)
              ·
                refine ⟨3748789134859577566481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2499192756573051710987 3748789134859577566481)
                ·
                  refine ⟨2811591851144683174861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3748789134859577566481 2811591851144683174861)
                  ·
                    refine ⟨1054346944179256190573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2811591851144683174861 1054346944179256190573)
                    ·
                      refine ⟨395380104067221071465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1054346944179256190573 395380104067221071465)
                      ·
                        rfl

theorem cell23_770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770 prefixEnd_770 := by exact prefixLift 770
  have htrace : WordTrace (prefixWord ++ tailWord_770) baseStart_770 baseEnd_770 := by
    simpa [prefixWord, tailWord_770, baseEnd_770] using wordTrace_append hprefix tailTrace_770
  have hstable : (prefixWord ++ tailWord_770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770).length < 2 ^ (prefixWord ++ tailWord_770).sum := by decide
  have hdescent : baseEnd_770 < baseStart_770 := by decide
  rcases family_descends (prefixWord ++ tailWord_770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 2, 9]
def baseStart_846 : Nat := 118140960795 + 846 * 2 ^ 59
def prefixEnd_846 : Nat := 4983230072969 + 3 ^ 40 * 846 * 2
def baseEnd_846 : Nat := 144801544602974573705

theorem tailTrace_846 : CollatzResearch.WordTrace tailWord_846 prefixEnd_846 144801544602974573705 := by
  unfold tailWord_846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3857019367820166300799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20570769961707553604261 3857019367820166300799)
  ·
    refine ⟨5785529051730249451199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3857019367820166300799 5785529051730249451199)
    ·
      refine ⟨8678293577595374176799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5785529051730249451199 8678293577595374176799)
      ·
        refine ⟨13017440366393061265199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8678293577595374176799 13017440366393061265199)
        ·
          refine ⟨19526160549589591897799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13017440366393061265199 19526160549589591897799)
          ·
            refine ⟨29289240824384387846699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19526160549589591897799 29289240824384387846699)
            ·
              refine ⟨43933861236576581770049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29289240824384387846699 43933861236576581770049)
              ·
                refine ⟨32950395927432436327537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43933861236576581770049 32950395927432436327537)
                ·
                  refine ⟨24712796945574327245653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32950395927432436327537 24712796945574327245653)
                  ·
                    refine ⟨144801544602974573705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 24712796945574327245653 144801544602974573705)
                    ·
                      rfl

theorem cell23_846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846 prefixEnd_846 := by exact prefixLift 846
  have htrace : WordTrace (prefixWord ++ tailWord_846) baseStart_846 baseEnd_846 := by
    simpa [prefixWord, tailWord_846, baseEnd_846] using wordTrace_append hprefix tailTrace_846
  have hstable : (prefixWord ++ tailWord_846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846).length < 2 ^ (prefixWord ++ tailWord_846).sum := by decide
  have hdescent : baseEnd_846 < baseStart_846 := by decide
  rcases family_descends (prefixWord ++ tailWord_846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863 : List Nat := [1, 1, 2, 3, 1, 3, 1, 5, 1, 5]
def baseStart_863 : Nat := 118140960795 + 863 * 2 ^ 59
def prefixEnd_863 : Nat := 4983230072969 + 3 ^ 40 * 863 * 2
def baseEnd_863 : Nat := 147711268311785736179

theorem tailTrace_863 : CollatzResearch.WordTrace tailWord_863 prefixEnd_863 147711268311785736179 := by
  unfold tailWord_863
  simp only [CollatzResearch.WordTrace]
  refine ⟨31476195880973233775243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20984130587315489183495 31476195880973233775243)
  ·
    refine ⟨47214293821459850662865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31476195880973233775243 47214293821459850662865)
    ·
      refine ⟨35410720366094887997149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47214293821459850662865 35410720366094887997149)
      ·
        refine ⟨13279020137285582998931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35410720366094887997149 13279020137285582998931)
        ·
          refine ⟨19918530205928374498397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13279020137285582998931 19918530205928374498397)
          ·
            refine ⟨7469448827223140436899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19918530205928374498397 7469448827223140436899)
            ·
              refine ⟨11204173240834710655349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7469448827223140436899 11204173240834710655349)
              ·
                refine ⟨1050391241328254123939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11204173240834710655349 1050391241328254123939)
                ·
                  refine ⟨1575586861992381185909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1050391241328254123939 1575586861992381185909)
                  ·
                    refine ⟨147711268311785736179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1575586861992381185909 147711268311785736179)
                    ·
                      rfl

theorem cell23_863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 5].length) (baseStart_863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863 prefixEnd_863 := by exact prefixLift 863
  have htrace : WordTrace (prefixWord ++ tailWord_863) baseStart_863 baseEnd_863 := by
    simpa [prefixWord, tailWord_863, baseEnd_863] using wordTrace_append hprefix tailTrace_863
  have hstable : (prefixWord ++ tailWord_863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863).length < 2 ^ (prefixWord ++ tailWord_863).sum := by decide
  have hdescent : baseEnd_863 < baseStart_863 := by decide
  rcases family_descends (prefixWord ++ tailWord_863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914 : List Nat := [3, 2, 3, 2, 2, 1, 3, 1, 1, 5]
def baseStart_914 : Nat := 118140960795 + 914 * 2 ^ 59
def prefixEnd_914 : Nat := 4983230072969 + 3 ^ 40 * 914 * 2
def baseEnd_914 : Nat := 156440439438219223601

theorem tailTrace_914 : CollatzResearch.WordTrace tailWord_914 prefixEnd_914 156440439438219223601 := by
  unfold tailWord_914
  simp only [CollatzResearch.WordTrace]
  refine ⟨8334079674052235970449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22224212464139295921197 8334079674052235970449)
  ·
    refine ⟨6250559755539176977837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8334079674052235970449 6250559755539176977837)
    ·
      refine ⟨2343959908327191366689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6250559755539176977837 2343959908327191366689)
      ·
        refine ⟨1757969931245393525017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2343959908327191366689 1757969931245393525017)
        ·
          refine ⟨1318477448434045143763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1757969931245393525017 1318477448434045143763)
          ·
            refine ⟨1977716172651067715645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1318477448434045143763 1977716172651067715645)
            ·
              refine ⟨741643564744150393367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1977716172651067715645 741643564744150393367)
              ·
                refine ⟨1112465347116225590051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 741643564744150393367 1112465347116225590051)
                ·
                  refine ⟨1668698020674338385077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1112465347116225590051 1668698020674338385077)
                  ·
                    refine ⟨156440439438219223601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1668698020674338385077 156440439438219223601)
                    ·
                      rfl

theorem cell23_914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_914 prefixEnd_914 := by exact prefixLift 914
  have htrace : WordTrace (prefixWord ++ tailWord_914) baseStart_914 baseEnd_914 := by
    simpa [prefixWord, tailWord_914, baseEnd_914] using wordTrace_append hprefix tailTrace_914
  have hstable : (prefixWord ++ tailWord_914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914).length < 2 ^ (prefixWord ++ tailWord_914).sum := by decide
  have hdescent : baseEnd_914 < baseStart_914 := by decide
  rcases family_descends (prefixWord ++ tailWord_914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917 : List Nat := [1, 3, 2, 1, 1, 5, 3, 1, 1, 1, 4]
def baseStart_917 : Nat := 118140960795 + 917 * 2 ^ 59
def prefixEnd_917 : Nat := 4983230072969 + 3 ^ 40 * 917 * 2
def baseEnd_917 : Nat := 470861760278145933289

theorem tailTrace_917 : CollatzResearch.WordTrace tailWord_917 prefixEnd_917 470861760278145933289 := by
  unfold tailWord_917
  simp only [CollatzResearch.WordTrace]
  refine ⟨33445737685340456241005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22297158456893637494003 33445737685340456241005)
  ·
    refine ⟨12542151632002671090377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33445737685340456241005 12542151632002671090377)
    ·
      refine ⟨9406613724002003317783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12542151632002671090377 9406613724002003317783)
      ·
        refine ⟨14109920586003004976675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9406613724002003317783 14109920586003004976675)
        ·
          refine ⟨21164880879004507465013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14109920586003004976675 21164880879004507465013)
          ·
            refine ⟨1984207582406672574845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21164880879004507465013 1984207582406672574845)
            ·
              refine ⟨744077843402502215567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1984207582406672574845 744077843402502215567)
              ·
                refine ⟨1116116765103753323351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744077843402502215567 1116116765103753323351)
                ·
                  refine ⟨1674175147655629985027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1116116765103753323351 1674175147655629985027)
                  ·
                    refine ⟨2511262721483444977541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1674175147655629985027 2511262721483444977541)
                    ·
                      refine ⟨470861760278145933289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2511262721483444977541 470861760278145933289)
                      ·
                        rfl

theorem cell23_917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 1, 1, 4].length) (baseStart_917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917 prefixEnd_917 := by exact prefixLift 917
  have htrace : WordTrace (prefixWord ++ tailWord_917) baseStart_917 baseEnd_917 := by
    simpa [prefixWord, tailWord_917, baseEnd_917] using wordTrace_append hprefix tailTrace_917
  have hstable : (prefixWord ++ tailWord_917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917).length < 2 ^ (prefixWord ++ tailWord_917).sum := by decide
  have hdescent : baseEnd_917 < baseStart_917 := by decide
  rcases family_descends (prefixWord ++ tailWord_917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927 : List Nat := [1, 1, 2, 5, 2, 2, 2, 2, 2, 4]
def baseStart_927 : Nat := 118140960795 + 927 * 2 ^ 59
def prefixEnd_927 : Nat := 4983230072969 + 3 ^ 40 * 927 * 2
def baseEnd_927 : Nat := 158665522274368936081

theorem tailTrace_927 : CollatzResearch.WordTrace tailWord_927 prefixEnd_927 158665522274368936081 := by
  unfold tailWord_927
  simp only [CollatzResearch.WordTrace]
  refine ⟨33810467649112164105035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22540311766074776070023 33810467649112164105035)
  ·
    refine ⟨50715701473668246157553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33810467649112164105035 50715701473668246157553)
    ·
      refine ⟨38036776105251184618165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50715701473668246157553 38036776105251184618165)
      ·
        refine ⟨3565947759867298557953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38036776105251184618165 3565947759867298557953)
        ·
          refine ⟨2674460819900473918465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3565947759867298557953 2674460819900473918465)
          ·
            refine ⟨2005845614925355438849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2674460819900473918465 2005845614925355438849)
            ·
              refine ⟨1504384211194016579137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2005845614925355438849 1504384211194016579137)
              ·
                refine ⟨1128288158395512434353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1504384211194016579137 1128288158395512434353)
                ·
                  refine ⟨846216118796634325765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1128288158395512434353 846216118796634325765)
                  ·
                    refine ⟨158665522274368936081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 846216118796634325765 158665522274368936081)
                    ·
                      rfl

theorem cell23_927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 4].length) (baseStart_927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927 prefixEnd_927 := by exact prefixLift 927
  have htrace : WordTrace (prefixWord ++ tailWord_927) baseStart_927 baseEnd_927 := by
    simpa [prefixWord, tailWord_927, baseEnd_927] using wordTrace_append hprefix tailTrace_927
  have hstable : (prefixWord ++ tailWord_927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927).length < 2 ^ (prefixWord ++ tailWord_927).sum := by decide
  have hdescent : baseEnd_927 < baseStart_927 := by decide
  rcases family_descends (prefixWord ++ tailWord_927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977 : List Nat := [1, 2, 2, 1, 2, 1, 5, 3, 1, 3, 2]
def baseStart_977 : Nat := 118140960795 + 977 * 2 ^ 59
def prefixEnd_977 : Nat := 4983230072969 + 3 ^ 40 * 977 * 2
def baseEnd_977 : Nat := 501670599547911183013

theorem tailTrace_977 : CollatzResearch.WordTrace tailWord_977 prefixEnd_977 501670599547911183013 := by
  unfold tailWord_977
  simp only [CollatzResearch.WordTrace]
  refine ⟨35634117467970703425185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23756078311980468950123 35634117467970703425185)
  ·
    refine ⟨26725588100978027568889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35634117467970703425185 26725588100978027568889)
    ·
      refine ⟨20044191075733520676667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26725588100978027568889 20044191075733520676667)
      ·
        refine ⟨30066286613600281015001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20044191075733520676667 30066286613600281015001)
        ·
          refine ⟨22549714960200210761251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30066286613600281015001 22549714960200210761251)
          ·
            refine ⟨33824572440300316141877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22549714960200210761251 33824572440300316141877)
            ·
              refine ⟨3171053666278154638301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33824572440300316141877 3171053666278154638301)
              ·
                refine ⟨1189145124854307989363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3171053666278154638301 1189145124854307989363)
                ·
                  refine ⟨1783717687281461984045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1189145124854307989363 1783717687281461984045)
                  ·
                    refine ⟨668894132730548244017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1783717687281461984045 668894132730548244017)
                    ·
                      refine ⟨501670599547911183013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 668894132730548244017 501670599547911183013)
                      ·
                        rfl

theorem cell23_977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 3, 2].length) (baseStart_977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977 prefixEnd_977 := by exact prefixLift 977
  have htrace : WordTrace (prefixWord ++ tailWord_977) baseStart_977 baseEnd_977 := by
    simpa [prefixWord, tailWord_977, baseEnd_977] using wordTrace_append hprefix tailTrace_977
  have hstable : (prefixWord ++ tailWord_977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977).length < 2 ^ (prefixWord ++ tailWord_977).sum := by decide
  have hdescent : baseEnd_977 < baseStart_977 := by decide
  rcases family_descends (prefixWord ++ tailWord_977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984 : List Nat := [2, 1, 2, 2, 2, 5, 1, 2, 2, 1, 3]
def baseStart_984 : Nat := 118140960795 + 984 * 2 ^ 59
def prefixEnd_984 : Nat := 4983230072969 + 3 ^ 40 * 984 * 2
def baseEnd_984 : Nat := 505264964129383795481

theorem tailTrace_984 : CollatzResearch.WordTrace tailWord_984 prefixEnd_984 505264964129383795481 := by
  unfold tailWord_984
  simp only [CollatzResearch.WordTrace]
  refine ⟨17944714221305449465003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23926285628407265953337 17944714221305449465003)
  ·
    refine ⟨26917071331958174197505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17944714221305449465003 26917071331958174197505)
    ·
      refine ⟨20187803498968630648129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26917071331958174197505 20187803498968630648129)
      ·
        refine ⟨15140852624226472986097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20187803498968630648129 15140852624226472986097)
        ·
          refine ⟨11355639468169854739573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15140852624226472986097 11355639468169854739573)
          ·
            refine ⟨1064591200140923881835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11355639468169854739573 1064591200140923881835)
            ·
              refine ⟨1596886800211385822753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1064591200140923881835 1596886800211385822753)
              ·
                refine ⟨1197665100158539367065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1596886800211385822753 1197665100158539367065)
                ·
                  refine ⟨898248825118904525299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1197665100158539367065 898248825118904525299)
                  ·
                    refine ⟨1347373237678356787949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 898248825118904525299 1347373237678356787949)
                    ·
                      refine ⟨505264964129383795481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1347373237678356787949 505264964129383795481)
                      ·
                        rfl

theorem cell23_984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984 prefixEnd_984 := by exact prefixLift 984
  have htrace : WordTrace (prefixWord ++ tailWord_984) baseStart_984 baseEnd_984 := by
    simpa [prefixWord, tailWord_984, baseEnd_984] using wordTrace_append hprefix tailTrace_984
  have hstable : (prefixWord ++ tailWord_984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984).length < 2 ^ (prefixWord ++ tailWord_984).sum := by decide
  have hdescent : baseEnd_984 < baseStart_984 := by decide
  rcases family_descends (prefixWord ++ tailWord_984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 4, 1, 5]
def baseStart_993 : Nat := 118140960795 + 993 * 2 ^ 59
def prefixEnd_993 : Nat := 4983230072969 + 3 ^ 40 * 993 * 2
def baseEnd_993 : Nat := 509886290019848582939

theorem tailTrace_993 : CollatzResearch.WordTrace tailWord_993 prefixEnd_993 509886290019848582939 := by
  unfold tailWord_993
  simp only [CollatzResearch.WordTrace]
  refine ⟨36217685410005436007633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24145123606670290671755 36217685410005436007633)
  ·
    refine ⟨27163264057504077005725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36217685410005436007633 27163264057504077005725)
    ·
      refine ⟨10186224021564028877147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27163264057504077005725 10186224021564028877147)
      ·
        refine ⟨15279336032346043315721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10186224021564028877147 15279336032346043315721)
        ·
          refine ⟨11459502024259532486791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15279336032346043315721 11459502024259532486791)
          ·
            refine ⟨17189253036389298730187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11459502024259532486791 17189253036389298730187)
            ·
              refine ⟨25783879554583948095281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17189253036389298730187 25783879554583948095281)
              ·
                refine ⟨19337909665937961071461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25783879554583948095281 19337909665937961071461)
                ·
                  refine ⟨3625858062363367700899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19337909665937961071461 3625858062363367700899)
                  ·
                    refine ⟨5438787093545051551349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3625858062363367700899 5438787093545051551349)
                    ·
                      refine ⟨509886290019848582939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5438787093545051551349 509886290019848582939)
                      ·
                        rfl

theorem cell23_993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993 prefixEnd_993 := by exact prefixLift 993
  have htrace : WordTrace (prefixWord ++ tailWord_993) baseStart_993 baseEnd_993 := by
    simpa [prefixWord, tailWord_993, baseEnd_993] using wordTrace_append hprefix tailTrace_993
  have hstable : (prefixWord ++ tailWord_993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993).length < 2 ^ (prefixWord ++ tailWord_993).sum := by decide
  have hdescent : baseEnd_993 < baseStart_993 := by decide
  rcases family_descends (prefixWord ++ tailWord_993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007 : List Nat := [1, 1, 2, 1, 4, 3, 3, 1, 1, 4, 2]
def baseStart_1007 : Nat := 118140960795 + 1007 * 2 ^ 59
def prefixEnd_1007 : Nat := 4983230072969 + 3 ^ 40 * 1007 * 2
def baseEnd_1007 : Nat := 517075019182793807875

theorem tailTrace_1007 : CollatzResearch.WordTrace tailWord_1007 prefixEnd_1007 517075019182793807875 := by
  unfold tailWord_1007
  simp only [CollatzResearch.WordTrace]
  refine ⟨36728307359285827017275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24485538239523884678183 36728307359285827017275)
  ·
    refine ⟨55092461038928740525913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36728307359285827017275 55092461038928740525913)
    ·
      refine ⟨41319345779196555394435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55092461038928740525913 41319345779196555394435)
      ·
        refine ⟨61979018668794833091653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41319345779196555394435 61979018668794833091653)
        ·
          refine ⟨11621066000399031204685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61979018668794833091653 11621066000399031204685)
          ·
            refine ⟨4357899750149636701757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11621066000399031204685 4357899750149636701757)
            ·
              refine ⟨1634212406306113763159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4357899750149636701757 1634212406306113763159)
              ·
                refine ⟨2451318609459170644739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1634212406306113763159 2451318609459170644739)
                ·
                  refine ⟨3676977914188755967109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2451318609459170644739 3676977914188755967109)
                  ·
                    refine ⟨689433358910391743833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3676977914188755967109 689433358910391743833)
                    ·
                      refine ⟨517075019182793807875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 689433358910391743833 517075019182793807875)
                      ·
                        rfl

theorem cell23_1007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 4, 2].length) (baseStart_1007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007 prefixEnd_1007 := by exact prefixLift 1007
  have htrace : WordTrace (prefixWord ++ tailWord_1007) baseStart_1007 baseEnd_1007 := by
    simpa [prefixWord, tailWord_1007, baseEnd_1007] using wordTrace_append hprefix tailTrace_1007
  have hstable : (prefixWord ++ tailWord_1007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007).length < 2 ^ (prefixWord ++ tailWord_1007).sum := by decide
  have hdescent : baseEnd_1007 < baseStart_1007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047 : List Nat := [1, 1, 3, 5, 1, 3, 1, 1, 7]
def baseStart_1047 : Nat := 118140960795 + 1047 * 2 ^ 59
def prefixEnd_1047 : Nat := 4983230072969 + 3 ^ 40 * 1047 * 2
def baseEnd_1047 : Nat := 59734916151404145299

theorem tailTrace_1047 : CollatzResearch.WordTrace tailWord_1047 prefixEnd_1047 59734916151404145299 := by
  unfold tailWord_1047
  simp only [CollatzResearch.WordTrace]
  refine ⟨38187227214372658473395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25458151476248438982263 38187227214372658473395)
  ·
    refine ⟨57280840821558987710093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38187227214372658473395 57280840821558987710093)
    ·
      refine ⟨21480315308084620391285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57280840821558987710093 21480315308084620391285)
      ·
        refine ⟨2013779560132933161683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21480315308084620391285 2013779560132933161683)
        ·
          refine ⟨3020669340199399742525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2013779560132933161683 3020669340199399742525)
          ·
            refine ⟨1132751002574774903447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3020669340199399742525 1132751002574774903447)
            ·
              refine ⟨1699126503862162355171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132751002574774903447 1699126503862162355171)
              ·
                refine ⟨2548689755793243532757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1699126503862162355171 2548689755793243532757)
                ·
                  refine ⟨59734916151404145299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2548689755793243532757 59734916151404145299)
                  ·
                    rfl

theorem cell23_1047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 7].length) (baseStart_1047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047 prefixEnd_1047 := by exact prefixLift 1047
  have htrace : WordTrace (prefixWord ++ tailWord_1047) baseStart_1047 baseEnd_1047 := by
    simpa [prefixWord, tailWord_1047, baseEnd_1047] using wordTrace_append hprefix tailTrace_1047
  have hstable : (prefixWord ++ tailWord_1047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047).length < 2 ^ (prefixWord ++ tailWord_1047).sum := by decide
  have hdescent : baseEnd_1047 < baseStart_1047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058 : List Nat := [3, 3, 1, 1, 1, 5, 2, 1, 2, 2, 2]
def baseStart_1058 : Nat := 118140960795 + 1058 * 2 ^ 59
def prefixEnd_1058 : Nat := 4983230072969 + 3 ^ 40 * 1058 * 2
def baseEnd_1058 : Nat := 543262532562094270141

theorem tailTrace_1058 : CollatzResearch.WordTrace tailWord_1058 prefixEnd_1058 543262532562094270141 := by
  unfold tailWord_1058
  simp only [CollatzResearch.WordTrace]
  refine ⟨9647107543630384280957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25725620116347691415885 9647107543630384280957)
  ·
    refine ⟨3617665328861394105359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9647107543630384280957 3617665328861394105359)
    ·
      refine ⟨5426497993292091158039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3617665328861394105359 5426497993292091158039)
      ·
        refine ⟨8139746989938136737059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5426497993292091158039 8139746989938136737059)
        ·
          refine ⟨12209620484907205105589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8139746989938136737059 12209620484907205105589)
          ·
            refine ⟨1144651920460050478649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12209620484907205105589 1144651920460050478649)
            ·
              refine ⟨858488940345037858987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1144651920460050478649 858488940345037858987)
              ·
                refine ⟨1287733410517556788481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858488940345037858987 1287733410517556788481)
                ·
                  refine ⟨965800057888167591361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1287733410517556788481 965800057888167591361)
                  ·
                    refine ⟨724350043416125693521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 965800057888167591361 724350043416125693521)
                    ·
                      refine ⟨543262532562094270141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 724350043416125693521 543262532562094270141)
                      ·
                        rfl

theorem cell23_1058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_1058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058 prefixEnd_1058 := by exact prefixLift 1058
  have htrace : WordTrace (prefixWord ++ tailWord_1058) baseStart_1058 baseEnd_1058 := by
    simpa [prefixWord, tailWord_1058, baseEnd_1058] using wordTrace_append hprefix tailTrace_1058
  have hstable : (prefixWord ++ tailWord_1058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058).length < 2 ^ (prefixWord ++ tailWord_1058).sum := by decide
  have hdescent : baseEnd_1058 < baseStart_1058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_1070 : Nat := 118140960795 + 1070 * 2 ^ 59
def prefixEnd_1070 : Nat := 4983230072969 + 3 ^ 40 * 1070 * 2
def baseEnd_1070 : Nat := 549424300416047320085

theorem tailTrace_1070 : CollatzResearch.WordTrace tailWord_1070 prefixEnd_1070 549424300416047320085 := by
  unfold tailWord_1070
  simp only [CollatzResearch.WordTrace]
  refine ⟨4878263266380948320083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26017404087365057707109 4878263266380948320083)
  ·
    refine ⟨7317394899571422480125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4878263266380948320083 7317394899571422480125)
    ·
      refine ⟨2744023087339283430047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7317394899571422480125 2744023087339283430047)
      ·
        refine ⟨4116034631008925145071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2744023087339283430047 4116034631008925145071)
        ·
          refine ⟨6174051946513387717607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4116034631008925145071 6174051946513387717607)
          ·
            refine ⟨9261077919770081576411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6174051946513387717607 9261077919770081576411)
            ·
              refine ⟨13891616879655122364617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9261077919770081576411 13891616879655122364617)
              ·
                refine ⟨10418712659741341773463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13891616879655122364617 10418712659741341773463)
                ·
                  refine ⟨15628068989612012660195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10418712659741341773463 15628068989612012660195)
                  ·
                    refine ⟨23442103484418018990293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15628068989612012660195 23442103484418018990293)
                    ·
                      refine ⟨549424300416047320085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23442103484418018990293 549424300416047320085)
                      ·
                        rfl

theorem cell23_1070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_1070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070 prefixEnd_1070 := by exact prefixLift 1070
  have htrace : WordTrace (prefixWord ++ tailWord_1070) baseStart_1070 baseEnd_1070 := by
    simpa [prefixWord, tailWord_1070, baseEnd_1070] using wordTrace_append hprefix tailTrace_1070
  have hstable : (prefixWord ++ tailWord_1070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070).length < 2 ^ (prefixWord ++ tailWord_1070).sum := by decide
  have hdescent : baseEnd_1070 < baseStart_1070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 5]
def baseStart_1083 : Nat := 118140960795 + 1083 * 2 ^ 59
def prefixEnd_1083 : Nat := 4983230072969 + 3 ^ 40 * 1083 * 2
def baseEnd_1083 : Nat := 556099548924496457525

theorem tailTrace_1083 : CollatzResearch.WordTrace tailWord_1083 prefixEnd_1083 556099548924496457525 := by
  unfold tailWord_1083
  simp only [CollatzResearch.WordTrace]
  refine ⟨39500255083950806783903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26333503389300537855935 39500255083950806783903)
  ·
    refine ⟨59250382625926210175855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39500255083950806783903 59250382625926210175855)
    ·
      refine ⟨88875573938889315263783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59250382625926210175855 88875573938889315263783)
      ·
        refine ⟨133313360908333972895675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88875573938889315263783 133313360908333972895675)
        ·
          refine ⟨199970041362500959343513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133313360908333972895675 199970041362500959343513)
          ·
            refine ⟨149977531021875719507635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199970041362500959343513 149977531021875719507635)
            ·
              refine ⟨224966296532813579261453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149977531021875719507635 224966296532813579261453)
              ·
                refine ⟨84362361199805092223045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 224966296532813579261453 84362361199805092223045)
                ·
                  refine ⟨15817942724963454791821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84362361199805092223045 15817942724963454791821)
                  ·
                    refine ⟨5931728521861295546933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15817942724963454791821 5931728521861295546933)
                    ·
                      refine ⟨556099548924496457525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5931728521861295546933 556099548924496457525)
                      ·
                        rfl

theorem cell23_1083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 5].length) (baseStart_1083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083 prefixEnd_1083 := by exact prefixLift 1083
  have htrace : WordTrace (prefixWord ++ tailWord_1083) baseStart_1083 baseEnd_1083 := by
    simpa [prefixWord, tailWord_1083, baseEnd_1083] using wordTrace_append hprefix tailTrace_1083
  have hstable : (prefixWord ++ tailWord_1083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083).length < 2 ^ (prefixWord ++ tailWord_1083).sum := by decide
  have hdescent : baseEnd_1083 < baseStart_1083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094 : List Nat := [6, 1, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_1094 : Nat := 118140960795 + 1094 * 2 ^ 59
def prefixEnd_1094 : Nat := 4983230072969 + 3 ^ 40 * 1094 * 2
def baseEnd_1094 : Nat := 187249278707984473325

theorem tailTrace_1094 : CollatzResearch.WordTrace tailWord_1094 prefixEnd_1094 187249278707984473325 := by
  unfold tailWord_1094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1246920563878115169823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26600972029399790289557 1246920563878115169823)
  ·
    refine ⟨1870380845817172754735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1246920563878115169823 1870380845817172754735)
    ·
      refine ⟨2805571268725759132103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1870380845817172754735 2805571268725759132103)
      ·
        refine ⟨4208356903088638698155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2805571268725759132103 4208356903088638698155)
        ·
          refine ⟨6312535354632958047233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4208356903088638698155 6312535354632958047233)
          ·
            refine ⟨4734401515974718535425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6312535354632958047233 4734401515974718535425)
            ·
              refine ⟨3550801136981038901569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4734401515974718535425 3550801136981038901569)
              ·
                refine ⟨2663100852735779176177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3550801136981038901569 2663100852735779176177)
                ·
                  refine ⟨1997325639551834382133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2663100852735779176177 1997325639551834382133)
                  ·
                    refine ⟨187249278707984473325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1997325639551834382133 187249278707984473325)
                    ·
                      rfl

theorem cell23_1094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_1094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094 prefixEnd_1094 := by exact prefixLift 1094
  have htrace : WordTrace (prefixWord ++ tailWord_1094) baseStart_1094 baseEnd_1094 := by
    simpa [prefixWord, tailWord_1094, baseEnd_1094] using wordTrace_append hprefix tailTrace_1094
  have hstable : (prefixWord ++ tailWord_1094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094).length < 2 ^ (prefixWord ++ tailWord_1094).sum := by decide
  have hdescent : baseEnd_1094 < baseStart_1094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 3, 4, 3]
def baseStart_1100 : Nat := 118140960795 + 1100 * 2 ^ 59
def prefixEnd_1100 : Nat := 4983230072969 + 3 ^ 40 * 1100 * 2
def baseEnd_1100 : Nat := 564828720050929944947

theorem tailTrace_1100 : CollatzResearch.WordTrace tailWord_1100 prefixEnd_1100 564828720050929944947 := by
  unfold tailWord_1100
  simp only [CollatzResearch.WordTrace]
  refine ⟨20060148011181355076377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26746864014908473435169 20060148011181355076377)
  ·
    refine ⟨15045111008386016307283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20060148011181355076377 15045111008386016307283)
    ·
      refine ⟨22567666512579024460925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15045111008386016307283 22567666512579024460925)
      ·
        refine ⟨8462874942217134172847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22567666512579024460925 8462874942217134172847)
        ·
          refine ⟨12694312413325701259271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8462874942217134172847 12694312413325701259271)
          ·
            refine ⟨19041468619988551888907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12694312413325701259271 19041468619988551888907)
            ·
              refine ⟨28562202929982827833361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19041468619988551888907 28562202929982827833361)
              ·
                refine ⟨21421652197487120875021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28562202929982827833361 21421652197487120875021)
                ·
                  refine ⟨8033119574057670328133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21421652197487120875021 8033119574057670328133)
                  ·
                    refine ⟨1506209920135813186525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8033119574057670328133 1506209920135813186525)
                    ·
                      refine ⟨564828720050929944947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1506209920135813186525 564828720050929944947)
                      ·
                        rfl

theorem cell23_1100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_1100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100 prefixEnd_1100 := by exact prefixLift 1100
  have htrace : WordTrace (prefixWord ++ tailWord_1100) baseStart_1100 baseEnd_1100 := by
    simpa [prefixWord, tailWord_1100, baseEnd_1100] using wordTrace_append hprefix tailTrace_1100
  have hstable : (prefixWord ++ tailWord_1100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100).length < 2 ^ (prefixWord ++ tailWord_1100).sum := by decide
  have hdescent : baseEnd_1100 < baseStart_1100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120 : List Nat := [2, 1, 1, 3, 2, 2, 1, 5, 6]
def baseStart_1120 : Nat := 118140960795 + 1120 * 2 ^ 59
def prefixEnd_1120 : Nat := 4983230072969 + 3 ^ 40 * 1120 * 2
def baseEnd_1120 : Nat := 63899814793427966095

theorem tailTrace_1120 : CollatzResearch.WordTrace tailWord_1120 prefixEnd_1120 63899814793427966095 := by
  unfold tailWord_1120
  simp only [CollatzResearch.WordTrace]
  refine ⟨20424877974953062940407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27233170633270750587209 20424877974953062940407)
  ·
    refine ⟨30637316962429594410611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20424877974953062940407 30637316962429594410611)
    ·
      refine ⟨45955975443644391615917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30637316962429594410611 45955975443644391615917)
      ·
        refine ⟨17233490791366646855969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45955975443644391615917 17233490791366646855969)
        ·
          refine ⟨12925118093524985141977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17233490791366646855969 12925118093524985141977)
          ·
            refine ⟨9693838570143738856483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12925118093524985141977 9693838570143738856483)
            ·
              refine ⟨14540757855215608284725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9693838570143738856483 14540757855215608284725)
              ·
                refine ⟨1363196048926463276693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14540757855215608284725 1363196048926463276693)
                ·
                  refine ⟨63899814793427966095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1363196048926463276693 63899814793427966095)
                  ·
                    rfl

theorem cell23_1120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 6].length) (baseStart_1120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1120 prefixEnd_1120 := by exact prefixLift 1120
  have htrace : WordTrace (prefixWord ++ tailWord_1120) baseStart_1120 baseEnd_1120 := by
    simpa [prefixWord, tailWord_1120, baseEnd_1120] using wordTrace_append hprefix tailTrace_1120
  have hstable : (prefixWord ++ tailWord_1120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120).length < 2 ^ (prefixWord ++ tailWord_1120).sum := by decide
  have hdescent : baseEnd_1120 < baseStart_1120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134 : List Nat := [4, 1, 2, 2, 1, 2, 3, 1, 2, 2, 3]
def baseStart_1134 : Nat := 118140960795 + 1134 * 2 ^ 59
def prefixEnd_1134 : Nat := 4983230072969 + 3 ^ 40 * 1134 * 2
def baseEnd_1134 : Nat := 582287062303796919791

theorem tailTrace_1134 : CollatzResearch.WordTrace tailWord_1134 prefixEnd_1134 582287062303796919791 := by
  unfold tailWord_1134
  simp only [CollatzResearch.WordTrace]
  refine ⟨5170047237398314611307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27573585266124344593637 5170047237398314611307)
  ·
    refine ⟨7755070856097471916961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5170047237398314611307 7755070856097471916961)
    ·
      refine ⟨5816303142073103937721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7755070856097471916961 5816303142073103937721)
      ·
        refine ⟨4362227356554827953291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5816303142073103937721 4362227356554827953291)
        ·
          refine ⟨6543341034832241929937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4362227356554827953291 6543341034832241929937)
          ·
            refine ⟨4907505776124181447453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6543341034832241929937 4907505776124181447453)
            ·
              refine ⟨1840314666046568042795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4907505776124181447453 1840314666046568042795)
              ·
                refine ⟨2760471999069852064193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1840314666046568042795 2760471999069852064193)
                ·
                  refine ⟨2070353999302389048145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2760471999069852064193 2070353999302389048145)
                  ·
                    refine ⟨1552765499476791786109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2070353999302389048145 1552765499476791786109)
                    ·
                      refine ⟨582287062303796919791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1552765499476791786109 582287062303796919791)
                      ·
                        rfl

theorem cell23_1134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_1134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134 prefixEnd_1134 := by exact prefixLift 1134
  have htrace : WordTrace (prefixWord ++ tailWord_1134) baseStart_1134 baseEnd_1134 := by
    simpa [prefixWord, tailWord_1134, baseEnd_1134] using wordTrace_append hprefix tailTrace_1134
  have hstable : (prefixWord ++ tailWord_1134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134).length < 2 ^ (prefixWord ++ tailWord_1134).sum := by decide
  have hdescent : baseEnd_1134 < baseStart_1134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207 : List Nat := [1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 5]
def baseStart_1207 : Nat := 118140960795 + 1207 * 2 ^ 59
def prefixEnd_1207 : Nat := 4983230072969 + 3 ^ 40 * 1207 * 2
def baseEnd_1207 : Nat := 619771150082011306955

theorem tailTrace_1207 : CollatzResearch.WordTrace tailWord_1207 prefixEnd_1207 619771150082011306955 := by
  unfold tailWord_1207
  simp only [CollatzResearch.WordTrace]
  refine ⟨44022906634719984297875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29348604423146656198583 44022906634719984297875)
  ·
    refine ⟨66034359952079976446813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44022906634719984297875 66034359952079976446813)
    ·
      refine ⟨24762884982029991167555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66034359952079976446813 24762884982029991167555)
      ·
        refine ⟨37144327473044986751333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24762884982029991167555 37144327473044986751333)
        ·
          refine ⟨6964561401195935015875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37144327473044986751333 6964561401195935015875)
          ·
            refine ⟨10446842101793902523813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6964561401195935015875 10446842101793902523813)
            ·
              refine ⟨1958782894086356723215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10446842101793902523813 1958782894086356723215)
              ·
                refine ⟨2938174341129535084823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1958782894086356723215 2938174341129535084823)
                ·
                  refine ⟨4407261511694302627235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2938174341129535084823 4407261511694302627235)
                  ·
                    refine ⟨6610892267541453940853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4407261511694302627235 6610892267541453940853)
                    ·
                      refine ⟨619771150082011306955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6610892267541453940853 619771150082011306955)
                      ·
                        rfl

theorem cell23_1207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 5].length) (baseStart_1207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207 prefixEnd_1207 := by exact prefixLift 1207
  have htrace : WordTrace (prefixWord ++ tailWord_1207) baseStart_1207 baseEnd_1207 := by
    simpa [prefixWord, tailWord_1207, baseEnd_1207] using wordTrace_append hprefix tailTrace_1207
  have hstable : (prefixWord ++ tailWord_1207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207).length < 2 ^ (prefixWord ++ tailWord_1207).sum := by decide
  have hdescent : baseEnd_1207 < baseStart_1207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 4, 4]
def baseStart_1214 : Nat := 118140960795 + 1214 * 2 ^ 59
def prefixEnd_1214 : Nat := 4983230072969 + 3 ^ 40 * 1214 * 2
def baseEnd_1214 : Nat := 207788504887827973141

theorem tailTrace_1214 : CollatzResearch.WordTrace tailWord_1214 prefixEnd_1214 207788504887827973141 := by
  unfold tailWord_1214
  simp only [CollatzResearch.WordTrace]
  refine ⟨5534777201170022475337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29518811739573453201797 5534777201170022475337)
  ·
    refine ⟨4151082900877516856503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5534777201170022475337 4151082900877516856503)
    ·
      refine ⟨6226624351316275284755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4151082900877516856503 6226624351316275284755)
      ·
        refine ⟨9339936526974412927133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6226624351316275284755 9339936526974412927133)
        ·
          refine ⟨3502476197615404847675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9339936526974412927133 3502476197615404847675)
          ·
            refine ⟨5253714296423107271513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3502476197615404847675 5253714296423107271513)
            ·
              refine ⟨3940285722317330453635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5253714296423107271513 3940285722317330453635)
              ·
                refine ⟨5910428583475995680453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3940285722317330453635 5910428583475995680453)
                ·
                  refine ⟨1108205359401749190085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5910428583475995680453 1108205359401749190085)
                  ·
                    refine ⟨207788504887827973141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1108205359401749190085 207788504887827973141)
                    ·
                      rfl

theorem cell23_1214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_1214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214 prefixEnd_1214 := by exact prefixLift 1214
  have htrace : WordTrace (prefixWord ++ tailWord_1214) baseStart_1214 baseEnd_1214 := by
    simpa [prefixWord, tailWord_1214, baseEnd_1214] using wordTrace_append hprefix tailTrace_1214
  have hstable : (prefixWord ++ tailWord_1214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214).length < 2 ^ (prefixWord ++ tailWord_1214).sum := by decide
  have hdescent : baseEnd_1214 < baseStart_1214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222 : List Nat := [6, 1, 2, 2, 2, 1, 2, 1, 6]
def baseStart_1222 : Nat := 118140960795 + 1222 * 2 ^ 59
def prefixEnd_1222 : Nat := 4983230072969 + 3 ^ 40 * 1222 * 2
def baseEnd_1222 : Nat := 69719262211050291043

theorem tailTrace_1222 : CollatzResearch.WordTrace tailWord_1222 prefixEnd_1222 69719262211050291043 := by
  unfold tailWord_1222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1392812549386798315435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29713334386918364062613 1392812549386798315435)
  ·
    refine ⟨2089218824080197473153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1392812549386798315435 2089218824080197473153)
    ·
      refine ⟨1566914118060148104865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2089218824080197473153 1566914118060148104865)
      ·
        refine ⟨1175185588545111078649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1566914118060148104865 1175185588545111078649)
        ·
          refine ⟨881389191408833308987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1175185588545111078649 881389191408833308987)
          ·
            refine ⟨1322083787113249963481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 881389191408833308987 1322083787113249963481)
            ·
              refine ⟨991562840334937472611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1322083787113249963481 991562840334937472611)
              ·
                refine ⟨1487344260502406208917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 991562840334937472611 1487344260502406208917)
                ·
                  refine ⟨69719262211050291043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1487344260502406208917 69719262211050291043)
                  ·
                    rfl

theorem cell23_1222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_1222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1222 prefixEnd_1222 := by exact prefixLift 1222
  have htrace : WordTrace (prefixWord ++ tailWord_1222) baseStart_1222 baseEnd_1222 := by
    simpa [prefixWord, tailWord_1222, baseEnd_1222] using wordTrace_append hprefix tailTrace_1222
  have hstable : (prefixWord ++ tailWord_1222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222).length < 2 ^ (prefixWord ++ tailWord_1222).sum := by decide
  have hdescent : baseEnd_1222 < baseStart_1222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 3]
def baseStart_1297 : Nat := 118140960795 + 1297 * 2 ^ 59
def prefixEnd_1297 : Nat := 4983230072969 + 3 ^ 40 * 1297 * 2
def baseEnd_1297 : Nat := 665984408986659181541

theorem tailTrace_1297 : CollatzResearch.WordTrace tailWord_1297 prefixEnd_1297 665984408986659181541 := by
  unfold tailWord_1297
  simp only [CollatzResearch.WordTrace]
  refine ⟨47305476308665355074145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31536984205776903382763 47305476308665355074145)
  ·
    refine ⟨35479107231499016305609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47305476308665355074145 35479107231499016305609)
    ·
      refine ⟨26609330423624262229207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35479107231499016305609 26609330423624262229207)
      ·
        refine ⟨39913995635436393343811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26609330423624262229207 39913995635436393343811)
        ·
          refine ⟨59870993453154590015717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39913995635436393343811 59870993453154590015717)
          ·
            refine ⟨11225811272466485627947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59870993453154590015717 11225811272466485627947)
            ·
              refine ⟨16838716908699728441921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11225811272466485627947 16838716908699728441921)
              ·
                refine ⟨12629037681524796331441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16838716908699728441921 12629037681524796331441)
                ·
                  refine ⟨9471778261143597248581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12629037681524796331441 9471778261143597248581)
                  ·
                    refine ⟨1775958423964424484109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9471778261143597248581 1775958423964424484109)
                    ·
                      refine ⟨665984408986659181541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1775958423964424484109 665984408986659181541)
                      ·
                        rfl

theorem cell23_1297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 3].length) (baseStart_1297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297 prefixEnd_1297 := by exact prefixLift 1297
  have htrace : WordTrace (prefixWord ++ tailWord_1297) baseStart_1297 baseEnd_1297 := by
    simpa [prefixWord, tailWord_1297, baseEnd_1297] using wordTrace_append hprefix tailTrace_1297
  have hstable : (prefixWord ++ tailWord_1297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297).length < 2 ^ (prefixWord ++ tailWord_1297).sum := by decide
  have hdescent : baseEnd_1297 < baseStart_1297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 2, 5, 2]
def baseStart_1354 : Nat := 118140960795 + 1354 * 2 ^ 59
def prefixEnd_1354 : Nat := 4983230072969 + 3 ^ 40 * 1354 * 2
def baseEnd_1354 : Nat := 695252806292936168779

theorem tailTrace_1354 : CollatzResearch.WordTrace tailWord_1354 prefixEnd_1354 695252806292936168779 := by
  unfold tailWord_1354
  simp only [CollatzResearch.WordTrace]
  refine ⟨12346109275541022474779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32922958068109393266077 12346109275541022474779)
  ·
    refine ⟨18519163913311533712169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12346109275541022474779 18519163913311533712169)
    ·
      refine ⟨13889372934983650284127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18519163913311533712169 13889372934983650284127)
      ·
        refine ⟨20834059402475475426191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13889372934983650284127 20834059402475475426191)
        ·
          refine ⟨31251089103713213139287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20834059402475475426191 31251089103713213139287)
          ·
            refine ⟨46876633655569819708931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31251089103713213139287 46876633655569819708931)
            ·
              refine ⟨70314950483354729563397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46876633655569819708931 70314950483354729563397)
              ·
                refine ⟨13184053215629011793137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70314950483354729563397 13184053215629011793137)
                ·
                  refine ⟨9888039911721758844853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13184053215629011793137 9888039911721758844853)
                  ·
                    refine ⟨927003741723914891705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9888039911721758844853 927003741723914891705)
                    ·
                      refine ⟨695252806292936168779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 927003741723914891705 695252806292936168779)
                      ·
                        rfl

theorem cell23_1354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 2, 5, 2].length) (baseStart_1354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354 prefixEnd_1354 := by exact prefixLift 1354
  have htrace : WordTrace (prefixWord ++ tailWord_1354) baseStart_1354 baseEnd_1354 := by
    simpa [prefixWord, tailWord_1354, baseEnd_1354] using wordTrace_append hprefix tailTrace_1354
  have hstable : (prefixWord ++ tailWord_1354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354).length < 2 ^ (prefixWord ++ tailWord_1354).sum := by decide
  have hdescent : baseEnd_1354 < baseStart_1354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364 : List Nat := [2, 4, 1, 1, 2, 1, 2, 3, 2, 5]
def baseStart_1364 : Nat := 118140960795 + 1364 * 2 ^ 59
def prefixEnd_1364 : Nat := 4983230072969 + 3 ^ 40 * 1364 * 2
def baseEnd_1364 : Nat := 233462537612632347911

theorem tailTrace_1364 : CollatzResearch.WordTrace tailWord_1364 prefixEnd_1364 233462537612632347911 := by
  unfold tailWord_1364
  simp only [CollatzResearch.WordTrace]
  refine ⟨24874583532967898881573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33166111377290531842097 24874583532967898881573)
  ·
    refine ⟨4663984412431481040295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24874583532967898881573 4663984412431481040295)
    ·
      refine ⟨6995976618647221560443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4663984412431481040295 6995976618647221560443)
      ·
        refine ⟨10493964927970832340665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6995976618647221560443 10493964927970832340665)
        ·
          refine ⟨7870473695978124255499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10493964927970832340665 7870473695978124255499)
          ·
            refine ⟨11805710543967186383249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7870473695978124255499 11805710543967186383249)
            ·
              refine ⟨8854282907975389787437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11805710543967186383249 8854282907975389787437)
              ·
                refine ⟨3320356090490771170289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8854282907975389787437 3320356090490771170289)
                ·
                  refine ⟨2490267067868078377717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3320356090490771170289 2490267067868078377717)
                  ·
                    refine ⟨233462537612632347911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2490267067868078377717 233462537612632347911)
                    ·
                      rfl

theorem cell23_1364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_1364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364 prefixEnd_1364 := by exact prefixLift 1364
  have htrace : WordTrace (prefixWord ++ tailWord_1364) baseStart_1364 baseEnd_1364 := by
    simpa [prefixWord, tailWord_1364, baseEnd_1364] using wordTrace_append hprefix tailTrace_1364
  have hstable : (prefixWord ++ tailWord_1364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364).length < 2 ^ (prefixWord ++ tailWord_1364).sum := by decide
  have hdescent : baseEnd_1364 < baseStart_1364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 4, 2, 3]
def baseStart_1404 : Nat := 118140960795 + 1404 * 2 ^ 59
def prefixEnd_1404 : Nat := 4983230072969 + 3 ^ 40 * 1404 * 2
def baseEnd_1404 : Nat := 720926839017740543549

theorem tailTrace_1404 : CollatzResearch.WordTrace tailWord_1404 prefixEnd_1404 720926839017740543549 := by
  unfold tailWord_1404
  simp only [CollatzResearch.WordTrace]
  refine ⟨25604043460511314609633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34138724614015086146177 25604043460511314609633)
  ·
    refine ⟨19203032595383485957225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25604043460511314609633 19203032595383485957225)
    ·
      refine ⟨14402274446537614467919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19203032595383485957225 14402274446537614467919)
      ·
        refine ⟨21603411669806421701879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14402274446537614467919 21603411669806421701879)
        ·
          refine ⟨32405117504709632552819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21603411669806421701879 32405117504709632552819)
          ·
            refine ⟨48607676257064448829229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32405117504709632552819 48607676257064448829229)
            ·
              refine ⟨18227878596399168310961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48607676257064448829229 18227878596399168310961)
              ·
                refine ⟨13670908947299376233221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18227878596399168310961 13670908947299376233221)
                ·
                  refine ⟨2563295427618633043729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13670908947299376233221 2563295427618633043729)
                  ·
                    refine ⟨1922471570713974782797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2563295427618633043729 1922471570713974782797)
                    ·
                      refine ⟨720926839017740543549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1922471570713974782797 720926839017740543549)
                      ·
                        rfl

theorem cell23_1404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_1404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404 prefixEnd_1404 := by exact prefixLift 1404
  have htrace : WordTrace (prefixWord ++ tailWord_1404) baseStart_1404 baseEnd_1404 := by
    simpa [prefixWord, tailWord_1404, baseEnd_1404] using wordTrace_append hprefix tailTrace_1404
  have hstable : (prefixWord ++ tailWord_1404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404).length < 2 ^ (prefixWord ++ tailWord_1404).sum := by decide
  have hdescent : baseEnd_1404 < baseStart_1404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511 : List Nat := [1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_1511 : Nat := 118140960795 + 1511 * 2 ^ 59
def prefixEnd_1511 : Nat := 4983230072969 + 3 ^ 40 * 1511 * 2
def baseEnd_1511 : Nat := 775869269048821905557

theorem tailTrace_1511 : CollatzResearch.WordTrace tailWord_1511 prefixEnd_1511 775869269048821905557 := by
  unfold tailWord_1511
  simp only [CollatzResearch.WordTrace]
  refine ⟨55110697533379903364387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36740465022253268909591 55110697533379903364387)
  ·
    refine ⟨82666046300069855046581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55110697533379903364387 82666046300069855046581)
    ·
      refine ⟨7749941840631548910617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82666046300069855046581 7749941840631548910617)
      ·
        refine ⟨5812456380473661682963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7749941840631548910617 5812456380473661682963)
        ·
          refine ⟨8718684570710492524445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5812456380473661682963 8718684570710492524445)
          ·
            refine ⟨3269506714016434696667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8718684570710492524445 3269506714016434696667)
            ·
              refine ⟨4904260071024652045001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3269506714016434696667 4904260071024652045001)
              ·
                refine ⟨3678195053268489033751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4904260071024652045001 3678195053268489033751)
                ·
                  refine ⟨5517292579902733550627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3678195053268489033751 5517292579902733550627)
                  ·
                    refine ⟨8275938869854100325941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5517292579902733550627 8275938869854100325941)
                    ·
                      refine ⟨775869269048821905557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8275938869854100325941 775869269048821905557)
                      ·
                        rfl

theorem cell23_1511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_1511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511 prefixEnd_1511 := by exact prefixLift 1511
  have htrace : WordTrace (prefixWord ++ tailWord_1511) baseStart_1511 baseEnd_1511 := by
    simpa [prefixWord, tailWord_1511, baseEnd_1511] using wordTrace_append hprefix tailTrace_1511
  have hstable : (prefixWord ++ tailWord_1511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511).length < 2 ^ (prefixWord ++ tailWord_1511).sum := by decide
  have hdescent : baseEnd_1511 < baseStart_1511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521 : List Nat := [1, 2, 2, 2, 3, 2, 3, 1, 1, 2, 4]
def baseStart_1521 : Nat := 118140960795 + 1521 * 2 ^ 59
def prefixEnd_1521 : Nat := 4983230072969 + 3 ^ 40 * 1521 * 2
def baseEnd_1521 : Nat := 781004075593782780511

theorem tailTrace_1521 : CollatzResearch.WordTrace tailWord_1521 prefixEnd_1521 781004075593782780511 := by
  unfold tailWord_1521
  simp only [CollatzResearch.WordTrace]
  refine ⟨55475427497151611228417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36983618331434407485611 55475427497151611228417)
  ·
    refine ⟨41606570622863708421313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55475427497151611228417 41606570622863708421313)
    ·
      refine ⟨31204927967147781315985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41606570622863708421313 31204927967147781315985)
      ·
        refine ⟨23403695975360835986989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31204927967147781315985 23403695975360835986989)
        ·
          refine ⟨8776385990760313495121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23403695975360835986989 8776385990760313495121)
          ·
            refine ⟨6582289493070235121341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8776385990760313495121 6582289493070235121341)
            ·
              refine ⟨2468358559901338170503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6582289493070235121341 2468358559901338170503)
              ·
                refine ⟨3702537839852007255755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2468358559901338170503 3702537839852007255755)
                ·
                  refine ⟨5553806759778010883633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3702537839852007255755 5553806759778010883633)
                  ·
                    refine ⟨4165355069833508162725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5553806759778010883633 4165355069833508162725)
                    ·
                      refine ⟨781004075593782780511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4165355069833508162725 781004075593782780511)
                      ·
                        rfl

theorem cell23_1521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_1521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521 prefixEnd_1521 := by exact prefixLift 1521
  have htrace : WordTrace (prefixWord ++ tailWord_1521) baseStart_1521 baseEnd_1521 := by
    simpa [prefixWord, tailWord_1521, baseEnd_1521] using wordTrace_append hprefix tailTrace_1521
  have hstable : (prefixWord ++ tailWord_1521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521).length < 2 ^ (prefixWord ++ tailWord_1521).sum := by decide
  have hdescent : baseEnd_1521 < baseStart_1521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525 : List Nat := [1, 3, 5, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_1525 : Nat := 118140960795 + 1525 * 2 ^ 59
def prefixEnd_1525 : Nat := 4983230072969 + 3 ^ 40 * 1525 * 2
def baseEnd_1525 : Nat := 783057998211767130493

theorem tailTrace_1525 : CollatzResearch.WordTrace tailWord_1525 prefixEnd_1525 783057998211767130493 := by
  unfold tailWord_1525
  simp only [CollatzResearch.WordTrace]
  refine ⟨55621319482660294374029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37080879655106862916019 55621319482660294374029)
  ·
    refine ⟨20857994805997610390261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55621319482660294374029 20857994805997610390261)
    ·
      refine ⟨1955437013062275974087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20857994805997610390261 1955437013062275974087)
      ·
        refine ⟨2933155519593413961131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1955437013062275974087 2933155519593413961131)
        ·
          refine ⟨4399733279390120941697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2933155519593413961131 4399733279390120941697)
          ·
            refine ⟨3299799959542590706273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4399733279390120941697 3299799959542590706273)
            ·
              refine ⟨2474849969656943029705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3299799959542590706273 2474849969656943029705)
              ·
                refine ⟨1856137477242707272279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2474849969656943029705 1856137477242707272279)
                ·
                  refine ⟨2784206215864060908419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1856137477242707272279 2784206215864060908419)
                  ·
                    refine ⟨4176309323796091362629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2784206215864060908419 4176309323796091362629)
                    ·
                      refine ⟨783057998211767130493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4176309323796091362629 783057998211767130493)
                      ·
                        rfl

theorem cell23_1525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_1525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525 prefixEnd_1525 := by exact prefixLift 1525
  have htrace : WordTrace (prefixWord ++ tailWord_1525) baseStart_1525 baseEnd_1525 := by
    simpa [prefixWord, tailWord_1525, baseEnd_1525] using wordTrace_append hprefix tailTrace_1525
  have hstable : (prefixWord ++ tailWord_1525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525).length < 2 ^ (prefixWord ++ tailWord_1525).sum := by decide
  have hdescent : baseEnd_1525 < baseStart_1525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528 : List Nat := [2, 1, 2, 1, 1, 6, 2, 2, 1, 2, 3]
def baseStart_1528 : Nat := 118140960795 + 1528 * 2 ^ 59
def prefixEnd_1528 : Nat := 4983230072969 + 3 ^ 40 * 1528 * 2
def baseEnd_1528 : Nat := 784598440175255392979

theorem tailTrace_1528 : CollatzResearch.WordTrace tailWord_1528 prefixEnd_1528 784598440175255392979 := by
  unfold tailWord_1528
  simp only [CollatzResearch.WordTrace]
  refine ⟨27865369235895903366619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37153825647861204488825 27865369235895903366619)
  ·
    refine ⟨41798053853843855049929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27865369235895903366619 41798053853843855049929)
    ·
      refine ⟨31348540390382891287447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41798053853843855049929 31348540390382891287447)
      ·
        refine ⟨47022810585574336931171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31348540390382891287447 47022810585574336931171)
        ·
          refine ⟨70534215878361505396757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47022810585574336931171 70534215878361505396757)
          ·
            refine ⟨3306291369298195565473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70534215878361505396757 3306291369298195565473)
            ·
              refine ⟨2479718526973646674105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3306291369298195565473 2479718526973646674105)
              ·
                refine ⟨1859788895230235005579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2479718526973646674105 1859788895230235005579)
                ·
                  refine ⟨2789683342845352508369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1859788895230235005579 2789683342845352508369)
                  ·
                    refine ⟨2092262507134014381277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2789683342845352508369 2092262507134014381277)
                    ·
                      refine ⟨784598440175255392979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2092262507134014381277 784598440175255392979)
                      ·
                        rfl

theorem cell23_1528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 1, 2, 3].length) (baseStart_1528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528 prefixEnd_1528 := by exact prefixLift 1528
  have htrace : WordTrace (prefixWord ++ tailWord_1528) baseStart_1528 baseEnd_1528 := by
    simpa [prefixWord, tailWord_1528, baseEnd_1528] using wordTrace_append hprefix tailTrace_1528
  have hstable : (prefixWord ++ tailWord_1528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528).length < 2 ^ (prefixWord ++ tailWord_1528).sum := by decide
  have hdescent : baseEnd_1528 < baseStart_1528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_1601 : Nat := 118140960795 + 1601 * 2 ^ 59
def prefixEnd_1601 : Nat := 4983230072969 + 3 ^ 40 * 1601 * 2
def baseEnd_1601 : Nat := 822082527953469780143

theorem tailTrace_1601 : CollatzResearch.WordTrace tailWord_1601 prefixEnd_1601 822082527953469780143 := by
  unfold tailWord_1601
  simp only [CollatzResearch.WordTrace]
  refine ⟨58393267207325274140657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38928844804883516093771 58393267207325274140657)
  ·
    refine ⟨43794950405493955605493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58393267207325274140657 43794950405493955605493)
    ·
      refine ⟨4105776600515058338015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43794950405493955605493 4105776600515058338015)
      ·
        refine ⟨6158664900772587507023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4105776600515058338015 6158664900772587507023)
        ·
          refine ⟨9237997351158881260535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6158664900772587507023 9237997351158881260535)
          ·
            refine ⟨13856996026738321890803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9237997351158881260535 13856996026738321890803)
            ·
              refine ⟨20785494040107482836205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13856996026738321890803 20785494040107482836205)
              ·
                refine ⟨7794560265040306063577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20785494040107482836205 7794560265040306063577)
                ·
                  refine ⟨5845920198780229547683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7794560265040306063577 5845920198780229547683)
                  ·
                    refine ⟨8768880298170344321525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5845920198780229547683 8768880298170344321525)
                    ·
                      refine ⟨822082527953469780143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8768880298170344321525 822082527953469780143)
                      ·
                        rfl

theorem cell23_1601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_1601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601 prefixEnd_1601 := by exact prefixLift 1601
  have htrace : WordTrace (prefixWord ++ tailWord_1601) baseStart_1601 baseEnd_1601 := by
    simpa [prefixWord, tailWord_1601, baseEnd_1601] using wordTrace_append hprefix tailTrace_1601
  have hstable : (prefixWord ++ tailWord_1601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601).length < 2 ^ (prefixWord ++ tailWord_1601).sum := by decide
  have hdescent : baseEnd_1601 < baseStart_1601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 2, 1, 8]
def baseStart_1624 : Nat := 118140960795 + 1624 * 2 ^ 59
def prefixEnd_1624 : Nat := 4983230072969 + 3 ^ 40 * 1624 * 2
def baseEnd_1624 : Nat := 833892583006879792537

theorem tailTrace_1624 : CollatzResearch.WordTrace tailWord_1624 prefixEnd_1624 833892583006879792537 := by
  unfold tailWord_1624
  simp only [CollatzResearch.WordTrace]
  refine ⟨29616073062000101113963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39488097416000134818617 29616073062000101113963)
  ·
    refine ⟨44424109593000151670945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29616073062000101113963 44424109593000151670945)
    ·
      refine ⟨33318082194750113753209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44424109593000151670945 33318082194750113753209)
      ·
        refine ⟨24988561646062585314907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33318082194750113753209 24988561646062585314907)
        ·
          refine ⟨37482842469093877972361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24988561646062585314907 37482842469093877972361)
          ·
            refine ⟨28112131851820408479271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37482842469093877972361 28112131851820408479271)
            ·
              refine ⟨42168197777730612718907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28112131851820408479271 42168197777730612718907)
              ·
                refine ⟨63252296666595919078361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42168197777730612718907 63252296666595919078361)
                ·
                  refine ⟨47439222499946939308771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63252296666595919078361 47439222499946939308771)
                  ·
                    refine ⟨71158833749920408963157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47439222499946939308771 71158833749920408963157)
                    ·
                      refine ⟨833892583006879792537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 71158833749920408963157 833892583006879792537)
                      ·
                        rfl

theorem cell23_1624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_1624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624 prefixEnd_1624 := by exact prefixLift 1624
  have htrace : WordTrace (prefixWord ++ tailWord_1624) baseStart_1624 baseEnd_1624 := by
    simpa [prefixWord, tailWord_1624, baseEnd_1624] using wordTrace_append hprefix tailTrace_1624
  have hstable : (prefixWord ++ tailWord_1624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624).length < 2 ^ (prefixWord ++ tailWord_1624).sum := by decide
  have hdescent : baseEnd_1624 < baseStart_1624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_1628 : Nat := 118140960795 + 1628 * 2 ^ 59
def prefixEnd_1628 : Nat := 4983230072969 + 3 ^ 40 * 1628 * 2
def baseEnd_1628 : Nat := 835946505624864142519

theorem tailTrace_1628 : CollatzResearch.WordTrace tailWord_1628 prefixEnd_1628 835946505624864142519 := by
  unfold tailWord_1628
  simp only [CollatzResearch.WordTrace]
  refine ⟨29689019054754442686769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39585358739672590249025 29689019054754442686769)
  ·
    refine ⟨22266764291065832015077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29689019054754442686769 22266764291065832015077)
    ·
      refine ⟨4175018304574843502827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22266764291065832015077 4175018304574843502827)
      ·
        refine ⟨6262527456862265254241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4175018304574843502827 6262527456862265254241)
        ·
          refine ⟨4696895592646698940681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6262527456862265254241 4696895592646698940681)
          ·
            refine ⟨3522671694485024205511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4696895592646698940681 3522671694485024205511)
            ·
              refine ⟨5284007541727536308267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3522671694485024205511 5284007541727536308267)
              ·
                refine ⟨7926011312591304462401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5284007541727536308267 7926011312591304462401)
                ·
                  refine ⟨5944508484443478346801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7926011312591304462401 5944508484443478346801)
                  ·
                    refine ⟨4458381363332608760101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5944508484443478346801 4458381363332608760101)
                    ·
                      refine ⟨835946505624864142519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4458381363332608760101 835946505624864142519)
                      ·
                        rfl

theorem cell23_1628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_1628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628 prefixEnd_1628 := by exact prefixLift 1628
  have htrace : WordTrace (prefixWord ++ tailWord_1628) baseStart_1628 baseEnd_1628 := by
    simpa [prefixWord, tailWord_1628, baseEnd_1628] using wordTrace_append hprefix tailTrace_1628
  have hstable : (prefixWord ++ tailWord_1628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628).length < 2 ^ (prefixWord ++ tailWord_1628).sum := by decide
  have hdescent : baseEnd_1628 < baseStart_1628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745 : List Nat := [1, 2, 2, 1, 2, 6, 2, 1, 6]
def baseStart_1745 : Nat := 118140960795 + 1745 * 2 ^ 59
def prefixEnd_1745 : Nat := 4983230072969 + 3 ^ 40 * 1745 * 2
def baseEnd_1745 : Nat := 99558193577878486609

theorem tailTrace_1745 : CollatzResearch.WordTrace tailWord_1745 prefixEnd_1745 99558193577878486609 := by
  unfold tailWord_1745
  simp only [CollatzResearch.WordTrace]
  refine ⟨63645378685637867382689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42430252457091911588459 63645378685637867382689)
  ·
    refine ⟨47734034014228400537017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63645378685637867382689 47734034014228400537017)
    ·
      refine ⟨35800525510671300402763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47734034014228400537017 35800525510671300402763)
      ·
        refine ⟨53700788266006950604145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35800525510671300402763 53700788266006950604145)
        ·
          refine ⟨40275591199505212953109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53700788266006950604145 40275591199505212953109)
          ·
            refine ⟨1887918337476806857177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40275591199505212953109 1887918337476806857177)
            ·
              refine ⟨1415938753107605142883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1887918337476806857177 1415938753107605142883)
              ·
                refine ⟨2123908129661407714325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1415938753107605142883 2123908129661407714325)
                ·
                  refine ⟨99558193577878486609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2123908129661407714325 99558193577878486609)
                  ·
                    rfl

theorem cell23_1745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 6].length) (baseStart_1745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1745 prefixEnd_1745 := by exact prefixLift 1745
  have htrace : WordTrace (prefixWord ++ tailWord_1745) baseStart_1745 baseEnd_1745 := by
    simpa [prefixWord, tailWord_1745, baseEnd_1745] using wordTrace_append hprefix tailTrace_1745
  have hstable : (prefixWord ++ tailWord_1745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745).length < 2 ^ (prefixWord ++ tailWord_1745).sum := by decide
  have hdescent : baseEnd_1745 < baseStart_1745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 3, 6]
def baseStart_1771 : Nat := 118140960795 + 1771 * 2 ^ 59
def prefixEnd_1771 : Nat := 4983230072969 + 3 ^ 40 * 1771 * 2
def baseEnd_1771 : Nat := 303124746405934884787

theorem tailTrace_1771 : CollatzResearch.WordTrace tailWord_1771 prefixEnd_1771 303124746405934884787 := by
  unfold tailWord_1771
  simp only [CollatzResearch.WordTrace]
  refine ⟨64593676591444307829167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43062451060962871886111 64593676591444307829167)
  ·
    refine ⟨96890514887166461743751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64593676591444307829167 96890514887166461743751)
    ·
      refine ⟨145335772330749692615627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96890514887166461743751 145335772330749692615627)
      ·
        refine ⟨218003658496124538923441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145335772330749692615627 218003658496124538923441)
        ·
          refine ⟨163502743872093404192581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218003658496124538923441 163502743872093404192581)
          ·
            refine ⟨30656764476017513286109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163502743872093404192581 30656764476017513286109)
            ·
              refine ⟨11496286678506567482291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30656764476017513286109 11496286678506567482291)
              ·
                refine ⟨17244430017759851223437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11496286678506567482291 17244430017759851223437)
                ·
                  refine ⟨6466661256659944208789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17244430017759851223437 6466661256659944208789)
                  ·
                    refine ⟨303124746405934884787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6466661256659944208789 303124746405934884787)
                    ·
                      rfl

theorem cell23_1771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 6].length) (baseStart_1771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771 prefixEnd_1771 := by exact prefixLift 1771
  have htrace : WordTrace (prefixWord ++ tailWord_1771) baseStart_1771 baseEnd_1771 := by
    simpa [prefixWord, tailWord_1771, baseEnd_1771] using wordTrace_append hprefix tailTrace_1771
  have hstable : (prefixWord ++ tailWord_1771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771).length < 2 ^ (prefixWord ++ tailWord_1771).sum := by decide
  have hdescent : baseEnd_1771 < baseStart_1771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775 : List Nat := [1, 1, 2, 1, 5, 1, 5, 1, 1, 5]
def baseStart_1775 : Nat := 118140960795 + 1775 * 2 ^ 59
def prefixEnd_1775 : Nat := 4983230072969 + 3 ^ 40 * 1775 * 2
def baseEnd_1775 : Nat := 303809387278596334781

theorem tailTrace_1775 : CollatzResearch.WordTrace tailWord_1775 prefixEnd_1775 303809387278596334781 := by
  unfold tailWord_1775
  simp only [CollatzResearch.WordTrace]
  refine ⟨64739568576952990974779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43159712384635327316519 64739568576952990974779)
  ·
    refine ⟨97109352865429486462169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64739568576952990974779 97109352865429486462169)
    ·
      refine ⟨72832014649072114846627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97109352865429486462169 72832014649072114846627)
      ·
        refine ⟨109248021973608172269941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72832014649072114846627 109248021973608172269941)
        ·
          refine ⟨10242002060025766150307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109248021973608172269941 10242002060025766150307)
          ·
            refine ⟨15363003090038649225461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10242002060025766150307 15363003090038649225461)
            ·
              refine ⟨1440281539691123364887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15363003090038649225461 1440281539691123364887)
              ·
                refine ⟨2160422309536685047331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1440281539691123364887 2160422309536685047331)
                ·
                  refine ⟨3240633464305027570997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2160422309536685047331 3240633464305027570997)
                  ·
                    refine ⟨303809387278596334781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3240633464305027570997 303809387278596334781)
                    ·
                      rfl

theorem cell23_1775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 1, 5].length) (baseStart_1775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775 prefixEnd_1775 := by exact prefixLift 1775
  have htrace : WordTrace (prefixWord ++ tailWord_1775) baseStart_1775 baseEnd_1775 := by
    simpa [prefixWord, tailWord_1775, baseEnd_1775] using wordTrace_append hprefix tailTrace_1775
  have hstable : (prefixWord ++ tailWord_1775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775).length < 2 ^ (prefixWord ++ tailWord_1775).sum := by decide
  have hdescent : baseEnd_1775 < baseStart_1775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782 : List Nat := [5, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2]
def baseStart_1782 : Nat := 118140960795 + 1782 * 2 ^ 59
def prefixEnd_1782 : Nat := 4983230072969 + 3 ^ 40 * 1782 * 2
def baseEnd_1782 : Nat := 915022526417261616811

theorem tailTrace_1782 : CollatzResearch.WordTrace tailWord_1782 prefixEnd_1782 915022526417261616811 := by
  unfold tailWord_1782
  simp only [CollatzResearch.WordTrace]
  refine ⟨4062179971974574154975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43329919701062124319733 4062179971974574154975)
  ·
    refine ⟨6093269957961861232463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4062179971974574154975 6093269957961861232463)
    ·
      refine ⟨9139904936942791848695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6093269957961861232463 9139904936942791848695)
      ·
        refine ⟨13709857405414187773043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9139904936942791848695 13709857405414187773043)
        ·
          refine ⟨20564786108121281659565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13709857405414187773043 20564786108121281659565)
          ·
            refine ⟨7711794790545480622337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20564786108121281659565 7711794790545480622337)
            ·
              refine ⟨5783846092909110466753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7711794790545480622337 5783846092909110466753)
              ·
                refine ⟨4337884569681832850065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5783846092909110466753 4337884569681832850065)
                ·
                  refine ⟨3253413427261374637549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4337884569681832850065 3253413427261374637549)
                  ·
                    refine ⟨1220030035223015489081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3253413427261374637549 1220030035223015489081)
                    ·
                      refine ⟨915022526417261616811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1220030035223015489081 915022526417261616811)
                      ·
                        rfl

theorem cell23_1782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_1782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782 prefixEnd_1782 := by exact prefixLift 1782
  have htrace : WordTrace (prefixWord ++ tailWord_1782) baseStart_1782 baseEnd_1782 := by
    simpa [prefixWord, tailWord_1782, baseEnd_1782] using wordTrace_append hprefix tailTrace_1782
  have hstable : (prefixWord ++ tailWord_1782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782).length < 2 ^ (prefixWord ++ tailWord_1782).sum := by decide
  have hdescent : baseEnd_1782 < baseStart_1782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1791 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 6]
def baseStart_1791 : Nat := 118140960795 + 1791 * 2 ^ 59
def prefixEnd_1791 : Nat := 4983230072969 + 3 ^ 40 * 1791 * 2
def baseEnd_1791 : Nat := 919643852307726404269

theorem tailTrace_1791 : CollatzResearch.WordTrace tailWord_1791 prefixEnd_1791 919643852307726404269 := by
  unfold tailWord_1791
  simp only [CollatzResearch.WordTrace]
  refine ⟨65323136518987723557227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43548757679325149038151 65323136518987723557227)
  ·
    refine ⟨97984704778481585335841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65323136518987723557227 97984704778481585335841)
    ·
      refine ⟨73488528583861189001881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97984704778481585335841 73488528583861189001881)
      ·
        refine ⟨55116396437895891751411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73488528583861189001881 55116396437895891751411)
        ·
          refine ⟨82674594656843837627117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55116396437895891751411 82674594656843837627117)
          ·
            refine ⟨31002972996316439110169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82674594656843837627117 31002972996316439110169)
            ·
              refine ⟨23252229747237329332627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31002972996316439110169 23252229747237329332627)
              ·
                refine ⟨34878344620855993998941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23252229747237329332627 34878344620855993998941)
                ·
                  refine ⟨13079379232820997749603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34878344620855993998941 13079379232820997749603)
                  ·
                    refine ⟨19619068849231496624405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13079379232820997749603 19619068849231496624405)
                    ·
                      refine ⟨919643852307726404269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19619068849231496624405 919643852307726404269)
                      ·
                        rfl

theorem cell23_1791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_1791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1791 prefixEnd_1791 := by exact prefixLift 1791
  have htrace : WordTrace (prefixWord ++ tailWord_1791) baseStart_1791 baseEnd_1791 := by
    simpa [prefixWord, tailWord_1791, baseEnd_1791] using wordTrace_append hprefix tailTrace_1791
  have hstable : (prefixWord ++ tailWord_1791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1791).length < 2 ^ (prefixWord ++ tailWord_1791).sum := by decide
  have hdescent : baseEnd_1791 < baseStart_1791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 3]
def baseStart_1815 : Nat := 118140960795 + 1815 * 2 ^ 59
def prefixEnd_1815 : Nat := 4983230072969 + 3 ^ 40 * 1815 * 2
def baseEnd_1815 : Nat := 931967388015632504159

theorem tailTrace_1815 : CollatzResearch.WordTrace tailWord_1815 prefixEnd_1815 931967388015632504159 := by
  unfold tailWord_1815
  simp only [CollatzResearch.WordTrace]
  refine ⟨66198488432039822430899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44132325621359881620599 66198488432039822430899)
  ·
    refine ⟨99297732648059733646349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66198488432039822430899 99297732648059733646349)
    ·
      refine ⟨37236649743022400117381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99297732648059733646349 37236649743022400117381)
      ·
        refine ⟨6981871826816700022009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37236649743022400117381 6981871826816700022009)
        ·
          refine ⟨5236403870112525016507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6981871826816700022009 5236403870112525016507)
          ·
            refine ⟨7854605805168787524761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5236403870112525016507 7854605805168787524761)
            ·
              refine ⟨5890954353876590643571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7854605805168787524761 5890954353876590643571)
              ·
                refine ⟨8836431530814885965357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5890954353876590643571 8836431530814885965357)
                ·
                  refine ⟨3313661824055582237009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8836431530814885965357 3313661824055582237009)
                  ·
                    refine ⟨2485246368041686677757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3313661824055582237009 2485246368041686677757)
                    ·
                      refine ⟨931967388015632504159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2485246368041686677757 931967388015632504159)
                      ·
                        rfl

theorem cell23_1815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_1815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815 prefixEnd_1815 := by exact prefixLift 1815
  have htrace : WordTrace (prefixWord ++ tailWord_1815) baseStart_1815 baseEnd_1815 := by
    simpa [prefixWord, tailWord_1815, baseEnd_1815] using wordTrace_append hprefix tailTrace_1815
  have hstable : (prefixWord ++ tailWord_1815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815).length < 2 ^ (prefixWord ++ tailWord_1815).sum := by decide
  have hdescent : baseEnd_1815 < baseStart_1815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829 : List Nat := [1, 3, 1, 2, 3, 2, 1, 5, 1, 2, 2]
def baseStart_1829 : Nat := 118140960795 + 1829 * 2 ^ 59
def prefixEnd_1829 : Nat := 4983230072969 + 3 ^ 40 * 1829 * 2
def baseEnd_1829 : Nat := 939156117178577729095

theorem tailTrace_1829 : CollatzResearch.WordTrace tailWord_1829 prefixEnd_1829 939156117178577729095 := by
  unfold tailWord_1829
  simp only [CollatzResearch.WordTrace]
  refine ⟨66709110381320213440541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44472740254213475627027 66709110381320213440541)
  ·
    refine ⟨25015916392995080040203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66709110381320213440541 25015916392995080040203)
    ·
      refine ⟨37523874589492620060305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25015916392995080040203 37523874589492620060305)
      ·
        refine ⟨28142905942119465045229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37523874589492620060305 28142905942119465045229)
        ·
          refine ⟨10553589728294799391961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28142905942119465045229 10553589728294799391961)
          ·
            refine ⟨7915192296221099543971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10553589728294799391961 7915192296221099543971)
            ·
              refine ⟨11872788444331649315957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7915192296221099543971 11872788444331649315957)
              ·
                refine ⟨1113073916656092123371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11872788444331649315957 1113073916656092123371)
                ·
                  refine ⟨1669610874984138185057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1113073916656092123371 1669610874984138185057)
                  ·
                    refine ⟨1252208156238103638793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1669610874984138185057 1252208156238103638793)
                    ·
                      refine ⟨939156117178577729095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1252208156238103638793 939156117178577729095)
                      ·
                        rfl

theorem cell23_1829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 1, 2, 2].length) (baseStart_1829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829 prefixEnd_1829 := by exact prefixLift 1829
  have htrace : WordTrace (prefixWord ++ tailWord_1829) baseStart_1829 baseEnd_1829 := by
    simpa [prefixWord, tailWord_1829, baseEnd_1829] using wordTrace_append hprefix tailTrace_1829
  have hstable : (prefixWord ++ tailWord_1829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829).length < 2 ^ (prefixWord ++ tailWord_1829).sum := by decide
  have hdescent : baseEnd_1829 < baseStart_1829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832 : List Nat := [2, 1, 5, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_1832 : Nat := 118140960795 + 1832 * 2 ^ 59
def prefixEnd_1832 : Nat := 4983230072969 + 3 ^ 40 * 1832 * 2
def baseEnd_1832 : Nat := 940696559142065991581

theorem tailTrace_1832 : CollatzResearch.WordTrace tailWord_1832 prefixEnd_1832 940696559142065991581 := by
  unfold tailWord_1832
  simp only [CollatzResearch.WordTrace]
  refine ⟨33409264685225862899875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44545686246967817199833 33409264685225862899875)
  ·
    refine ⟨50113897027838794349813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33409264685225862899875 50113897027838794349813)
    ·
      refine ⟨4698177846359886970295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50113897027838794349813 4698177846359886970295)
      ·
        refine ⟨7047266769539830455443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4698177846359886970295 7047266769539830455443)
        ·
          refine ⟨10570900154309745683165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7047266769539830455443 10570900154309745683165)
          ·
            refine ⟨3964087557866154631187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10570900154309745683165 3964087557866154631187)
            ·
              refine ⟨5946131336799231946781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3964087557866154631187 5946131336799231946781)
              ·
                refine ⟨2229799251299711980043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5946131336799231946781 2229799251299711980043)
                ·
                  refine ⟨3344698876949567970065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2229799251299711980043 3344698876949567970065)
                  ·
                    refine ⟨2508524157712175977549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3344698876949567970065 2508524157712175977549)
                    ·
                      refine ⟨940696559142065991581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2508524157712175977549 940696559142065991581)
                      ·
                        rfl

theorem cell23_1832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_1832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832 prefixEnd_1832 := by exact prefixLift 1832
  have htrace : WordTrace (prefixWord ++ tailWord_1832) baseStart_1832 baseEnd_1832 := by
    simpa [prefixWord, tailWord_1832, baseEnd_1832] using wordTrace_append hprefix tailTrace_1832
  have hstable : (prefixWord ++ tailWord_1832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832).length < 2 ^ (prefixWord ++ tailWord_1832).sum := by decide
  have hdescent : baseEnd_1832 < baseStart_1832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846 : List Nat := [5, 1, 2, 2, 1, 2, 2, 1, 3, 2, 2]
def baseStart_1846 : Nat := 118140960795 + 1846 * 2 ^ 59
def prefixEnd_1846 : Nat := 4983230072969 + 3 ^ 40 * 1846 * 2
def baseEnd_1846 : Nat := 947885288305011216517

theorem tailTrace_1846 : CollatzResearch.WordTrace tailWord_1846 prefixEnd_1846 947885288305011216517 := by
  unfold tailWord_1846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4208071957483257300587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44886100879821411206261 4208071957483257300587)
  ·
    refine ⟨6312107936224885950881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4208071957483257300587 6312107936224885950881)
    ·
      refine ⟨4734080952168664463161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6312107936224885950881 4734080952168664463161)
      ·
        refine ⟨3550560714126498347371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4734080952168664463161 3550560714126498347371)
        ·
          refine ⟨5325841071189747521057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3550560714126498347371 5325841071189747521057)
          ·
            refine ⟨3994380803392310640793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5325841071189747521057 3994380803392310640793)
            ·
              refine ⟨2995785602544232980595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3994380803392310640793 2995785602544232980595)
              ·
                refine ⟨4493678403816349470893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2995785602544232980595 4493678403816349470893)
                ·
                  refine ⟨1685129401431131051585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4493678403816349470893 1685129401431131051585)
                  ·
                    refine ⟨1263847051073348288689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1685129401431131051585 1263847051073348288689)
                    ·
                      refine ⟨947885288305011216517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1263847051073348288689 947885288305011216517)
                      ·
                        rfl

theorem cell23_1846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_1846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846 prefixEnd_1846 := by exact prefixLift 1846
  have htrace : WordTrace (prefixWord ++ tailWord_1846) baseStart_1846 baseEnd_1846 := by
    simpa [prefixWord, tailWord_1846, baseEnd_1846] using wordTrace_append hprefix tailTrace_1846
  have hstable : (prefixWord ++ tailWord_1846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846).length < 2 ^ (prefixWord ++ tailWord_1846).sum := by decide
  have hdescent : baseEnd_1846 < baseStart_1846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 5]
def baseStart_1888 : Nat := 118140960795 + 1888 * 2 ^ 59
def prefixEnd_1888 : Nat := 4983230072969 + 3 ^ 40 * 1888 * 2
def baseEnd_1888 : Nat := 969451475793846891323

theorem tailTrace_1888 : CollatzResearch.WordTrace tailWord_1888 prefixEnd_1888 969451475793846891323 := by
  unfold tailWord_1888
  simp only [CollatzResearch.WordTrace]
  refine ⟨34430508583786644919159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45907344778382193225545 34430508583786644919159)
  ·
    refine ⟨51645762875679967378739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34430508583786644919159 51645762875679967378739)
    ·
      refine ⟨77468644313519951068109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51645762875679967378739 77468644313519951068109)
      ·
        refine ⟨29050741617569981650541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77468644313519951068109 29050741617569981650541)
        ·
          refine ⟨10894028106588743118953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29050741617569981650541 10894028106588743118953)
          ·
            refine ⟨8170521079941557339215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10894028106588743118953 8170521079941557339215)
            ·
              refine ⟨12255781619912336008823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8170521079941557339215 12255781619912336008823)
              ·
                refine ⟨18383672429868504013235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12255781619912336008823 18383672429868504013235)
                ·
                  refine ⟨27575508644802756019853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18383672429868504013235 27575508644802756019853)
                  ·
                    refine ⟨10340815741801033507445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27575508644802756019853 10340815741801033507445)
                    ·
                      refine ⟨969451475793846891323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10340815741801033507445 969451475793846891323)
                      ·
                        rfl

theorem cell23_1888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_1888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888 prefixEnd_1888 := by exact prefixLift 1888
  have htrace : WordTrace (prefixWord ++ tailWord_1888) baseStart_1888 baseEnd_1888 := by
    simpa [prefixWord, tailWord_1888, baseEnd_1888] using wordTrace_append hprefix tailTrace_1888
  have hstable : (prefixWord ++ tailWord_1888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888).length < 2 ^ (prefixWord ++ tailWord_1888).sum := by decide
  have hdescent : baseEnd_1888 < baseStart_1888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959 : List Nat := [1, 1, 6, 1, 2, 1, 4, 2, 5]
def baseStart_1959 : Nat := 118140960795 + 1959 * 2 ^ 59
def prefixEnd_1959 : Nat := 4983230072969 + 3 ^ 40 * 1959 * 2
def baseEnd_1959 : Nat := 111767622473674344833

theorem tailTrace_1959 : CollatzResearch.WordTrace tailWord_1959 prefixEnd_1959 111767622473674344833 := by
  unfold tailWord_1959
  simp only [CollatzResearch.WordTrace]
  refine ⟨71450599910352415672931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47633733273568277115287 71450599910352415672931)
  ·
    refine ⟨107175899865528623509397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71450599910352415672931 107175899865528623509397)
    ·
      refine ⟨5023870306196654227003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107175899865528623509397 5023870306196654227003)
      ·
        refine ⟨7535805459294981340505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5023870306196654227003 7535805459294981340505)
        ·
          refine ⟨5651854094471236005379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7535805459294981340505 5651854094471236005379)
          ·
            refine ⟨8477781141706854008069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5651854094471236005379 8477781141706854008069)
            ·
              refine ⟨1589583964070035126513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8477781141706854008069 1589583964070035126513)
              ·
                refine ⟨1192187973052526344885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1589583964070035126513 1192187973052526344885)
                ·
                  refine ⟨111767622473674344833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1192187973052526344885 111767622473674344833)
                  ·
                    rfl

theorem cell23_1959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 5].length) (baseStart_1959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1959 prefixEnd_1959 := by exact prefixLift 1959
  have htrace : WordTrace (prefixWord ++ tailWord_1959) baseStart_1959 baseEnd_1959 := by
    simpa [prefixWord, tailWord_1959, baseEnd_1959] using wordTrace_append hprefix tailTrace_1959
  have hstable : (prefixWord ++ tailWord_1959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959).length < 2 ^ (prefixWord ++ tailWord_1959).sum := by decide
  have hdescent : baseEnd_1959 < baseStart_1959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_1966 : Nat := 118140960795 + 1966 * 2 ^ 59
def prefixEnd_1966 : Nat := 4983230072969 + 3 ^ 40 * 1966 * 2
def baseEnd_1966 : Nat := 1009502966844541715965

theorem tailTrace_1966 : CollatzResearch.WordTrace tailWord_1966 prefixEnd_1966 1009502966844541715965 := by
  unfold tailWord_1966
  simp only [CollatzResearch.WordTrace]
  refine ⟨8963238860624076397219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47803940589995074118501 8963238860624076397219)
  ·
    refine ⟨13444858290936114595829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8963238860624076397219 13444858290936114595829)
    ·
      refine ⟨1260455464775260743359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13444858290936114595829 1260455464775260743359)
      ·
        refine ⟨1890683197162891115039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1260455464775260743359 1890683197162891115039)
        ·
          refine ⟨2836024795744336672559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1890683197162891115039 2836024795744336672559)
          ·
            refine ⟨4254037193616505008839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2836024795744336672559 4254037193616505008839)
            ·
              refine ⟨6381055790424757513259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4254037193616505008839 6381055790424757513259)
              ·
                refine ⟨9571583685637136269889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6381055790424757513259 9571583685637136269889)
                ·
                  refine ⟨7178687764227852202417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9571583685637136269889 7178687764227852202417)
                  ·
                    refine ⟨5384015823170889151813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7178687764227852202417 5384015823170889151813)
                    ·
                      refine ⟨1009502966844541715965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5384015823170889151813 1009502966844541715965)
                      ·
                        rfl

theorem cell23_1966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_1966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966 prefixEnd_1966 := by exact prefixLift 1966
  have htrace : WordTrace (prefixWord ++ tailWord_1966) baseStart_1966 baseEnd_1966 := by
    simpa [prefixWord, tailWord_1966, baseEnd_1966] using wordTrace_append hprefix tailTrace_1966
  have hstable : (prefixWord ++ tailWord_1966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966).length < 2 ^ (prefixWord ++ tailWord_1966).sum := by decide
  have hdescent : baseEnd_1966 < baseStart_1966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992 : List Nat := [2, 1, 3, 1, 4, 1, 3, 1, 2, 1, 4]
def baseStart_1992 : Nat := 118140960795 + 1992 * 2 ^ 59
def prefixEnd_1992 : Nat := 4983230072969 + 3 ^ 40 * 1992 * 2
def baseEnd_1992 : Nat := 1022853463861439990845

theorem tailTrace_1992 : CollatzResearch.WordTrace tailWord_1992 prefixEnd_1992 1022853463861439990845 := by
  unfold tailWord_1992
  simp only [CollatzResearch.WordTrace]
  refine ⟨36327104395399525812115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48436139193866034416153 36327104395399525812115)
  ·
    refine ⟨54490656593099288718173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36327104395399525812115 54490656593099288718173)
    ·
      refine ⟨20433996222412233269315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54490656593099288718173 20433996222412233269315)
      ·
        refine ⟨30650994333618349903973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20433996222412233269315 30650994333618349903973)
        ·
          refine ⟨5747061437553440606995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30650994333618349903973 5747061437553440606995)
          ·
            refine ⟨8620592156330160910493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5747061437553440606995 8620592156330160910493)
            ·
              refine ⟨3232722058623810341435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8620592156330160910493 3232722058623810341435)
              ·
                refine ⟨4849083087935715512153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3232722058623810341435 4849083087935715512153)
                ·
                  refine ⟨3636812315951786634115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4849083087935715512153 3636812315951786634115)
                  ·
                    refine ⟨5455218473927679951173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3636812315951786634115 5455218473927679951173)
                    ·
                      refine ⟨1022853463861439990845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5455218473927679951173 1022853463861439990845)
                      ·
                        rfl

theorem cell23_1992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_1992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992 prefixEnd_1992 := by exact prefixLift 1992
  have htrace : WordTrace (prefixWord ++ tailWord_1992) baseStart_1992 baseEnd_1992 := by
    simpa [prefixWord, tailWord_1992, baseEnd_1992] using wordTrace_append hprefix tailTrace_1992
  have hstable : (prefixWord ++ tailWord_1992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992).length < 2 ^ (prefixWord ++ tailWord_1992).sum := by decide
  have hdescent : baseEnd_1992 < baseStart_1992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 3]
def baseStart_1995 : Nat := 118140960795 + 1995 * 2 ^ 59
def prefixEnd_1995 : Nat := 4983230072969 + 3 ^ 40 * 1995 * 2
def baseEnd_1995 : Nat := 1024393905824928253331

theorem tailTrace_1995 : CollatzResearch.WordTrace tailWord_1995 prefixEnd_1995 1024393905824928253331 := by
  unfold tailWord_1995
  simp only [CollatzResearch.WordTrace]
  refine ⟨72763627779930563983439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48509085186620375988959 72763627779930563983439)
  ·
    refine ⟨109145441669895845975159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72763627779930563983439 109145441669895845975159)
    ·
      refine ⟨163718162504843768962739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109145441669895845975159 163718162504843768962739)
      ·
        refine ⟨245577243757265653444109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163718162504843768962739 245577243757265653444109)
        ·
          refine ⟨92091466408974620041541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245577243757265653444109 92091466408974620041541)
          ·
            refine ⟨17267149951682741257789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92091466408974620041541 17267149951682741257789)
            ·
              refine ⟨6475181231881027971671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17267149951682741257789 6475181231881027971671)
              ·
                refine ⟨9712771847821541957507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6475181231881027971671 9712771847821541957507)
                ·
                  refine ⟨14569157771732312936261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9712771847821541957507 14569157771732312936261)
                  ·
                    refine ⟨2731717082199808675549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14569157771732312936261 2731717082199808675549)
                    ·
                      refine ⟨1024393905824928253331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2731717082199808675549 1024393905824928253331)
                      ·
                        rfl

theorem cell23_1995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 3].length) (baseStart_1995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995 prefixEnd_1995 := by exact prefixLift 1995
  have htrace : WordTrace (prefixWord ++ tailWord_1995) baseStart_1995 baseEnd_1995 := by
    simpa [prefixWord, tailWord_1995, baseEnd_1995] using wordTrace_append hprefix tailTrace_1995
  have hstable : (prefixWord ++ tailWord_1995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995).length < 2 ^ (prefixWord ++ tailWord_1995).sum := by decide
  have hdescent : baseEnd_1995 < baseStart_1995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 2, 1, 6]
def baseStart_2005 : Nat := 118140960795 + 2005 * 2 ^ 59
def prefixEnd_2005 : Nat := 4983230072969 + 3 ^ 40 * 2005 * 2
def baseEnd_2005 : Nat := 1029528712369889128285

theorem tailTrace_2005 : CollatzResearch.WordTrace tailWord_2005 prefixEnd_2005 1029528712369889128285 := by
  unfold tailWord_2005
  simp only [CollatzResearch.WordTrace]
  refine ⟨73128357743702271847469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48752238495801514564979 73128357743702271847469)
  ·
    refine ⟨27423134153888351942801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73128357743702271847469 27423134153888351942801)
    ·
      refine ⟨20567350615416263957101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27423134153888351942801 20567350615416263957101)
      ·
        refine ⟨7712756480781098983913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20567350615416263957101 7712756480781098983913)
        ·
          refine ⟨5784567360585824237935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7712756480781098983913 5784567360585824237935)
          ·
            refine ⟨8676851040878736356903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5784567360585824237935 8676851040878736356903)
            ·
              refine ⟨13015276561318104535355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8676851040878736356903 13015276561318104535355)
              ·
                refine ⟨19522914841977156803033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13015276561318104535355 19522914841977156803033)
                ·
                  refine ⟨14642186131482867602275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19522914841977156803033 14642186131482867602275)
                  ·
                    refine ⟨21963279197224301403413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14642186131482867602275 21963279197224301403413)
                    ·
                      refine ⟨1029528712369889128285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21963279197224301403413 1029528712369889128285)
                      ·
                        rfl

theorem cell23_2005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_2005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005 prefixEnd_2005 := by exact prefixLift 2005
  have htrace : WordTrace (prefixWord ++ tailWord_2005) baseStart_2005 baseEnd_2005 := by
    simpa [prefixWord, tailWord_2005, baseEnd_2005] using wordTrace_append hprefix tailTrace_2005
  have hstable : (prefixWord ++ tailWord_2005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005).length < 2 ^ (prefixWord ++ tailWord_2005).sum := by decide
  have hdescent : baseEnd_2005 < baseStart_2005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 8]
def baseStart_2015 : Nat := 118140960795 + 2015 * 2 ^ 59
def prefixEnd_2015 : Nat := 4983230072969 + 3 ^ 40 * 2015 * 2
def baseEnd_2015 : Nat := 114962613212761111471

theorem tailTrace_2015 : CollatzResearch.WordTrace tailWord_2015 prefixEnd_2015 114962613212761111471 := by
  unfold tailWord_2015
  simp only [CollatzResearch.WordTrace]
  refine ⟨73493087707473979711499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48995391804982653140999 73493087707473979711499)
  ·
    refine ⟨110239631561210969567249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73493087707473979711499 110239631561210969567249)
    ·
      refine ⟨82679723670908227175437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110239631561210969567249 82679723670908227175437)
      ·
        refine ⟨31004896376590585190789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82679723670908227175437 31004896376590585190789)
        ·
          refine ⟨5813418070610734723273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31004896376590585190789 5813418070610734723273)
          ·
            refine ⟨4360063552958051042455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5813418070610734723273 4360063552958051042455)
            ·
              refine ⟨6540095329437076563683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4360063552958051042455 6540095329437076563683)
              ·
                refine ⟨9810142994155614845525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6540095329437076563683 9810142994155614845525)
                ·
                  refine ⟨114962613212761111471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9810142994155614845525 114962613212761111471)
                  ·
                    rfl

theorem cell23_2015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 8].length) (baseStart_2015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015 prefixEnd_2015 := by exact prefixLift 2015
  have htrace : WordTrace (prefixWord ++ tailWord_2015) baseStart_2015 baseEnd_2015 := by
    simpa [prefixWord, tailWord_2015, baseEnd_2015] using wordTrace_append hprefix tailTrace_2015
  have hstable : (prefixWord ++ tailWord_2015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015).length < 2 ^ (prefixWord ++ tailWord_2015).sum := by decide
  have hdescent : baseEnd_2015 < baseStart_2015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019 : List Nat := [1, 1, 1, 6, 1, 2, 2, 4, 1, 4]
def baseStart_2019 : Nat := 118140960795 + 2019 * 2 ^ 59
def prefixEnd_2019 : Nat := 4983230072969 + 3 ^ 40 * 2019 * 2
def baseEnd_2019 : Nat := 345572480510944784407

theorem tailTrace_2019 : CollatzResearch.WordTrace tailWord_2019 prefixEnd_2019 345572480510944784407 := by
  unfold tailWord_2019
  simp only [CollatzResearch.WordTrace]
  refine ⟨73638979692982662857111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49092653128655108571407 73638979692982662857111)
  ·
    refine ⟨110458469539473994285667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73638979692982662857111 110458469539473994285667)
    ·
      refine ⟨165687704309210991428501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110458469539473994285667 165687704309210991428501)
      ·
        refine ⟨7766611139494265223211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 165687704309210991428501 7766611139494265223211)
        ·
          refine ⟨11649916709241397834817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7766611139494265223211 11649916709241397834817)
          ·
            refine ⟨8737437531931048376113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11649916709241397834817 8737437531931048376113)
            ·
              refine ⟨6553078148948286282085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8737437531931048376113 6553078148948286282085)
              ·
                refine ⟨1228702152927803677891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6553078148948286282085 1228702152927803677891)
                ·
                  refine ⟨1843053229391705516837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1228702152927803677891 1843053229391705516837)
                  ·
                    refine ⟨345572480510944784407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1843053229391705516837 345572480510944784407)
                    ·
                      rfl

theorem cell23_2019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 1, 4].length) (baseStart_2019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019 prefixEnd_2019 := by exact prefixLift 2019
  have htrace : WordTrace (prefixWord ++ tailWord_2019) baseStart_2019 baseEnd_2019 := by
    simpa [prefixWord, tailWord_2019, baseEnd_2019] using wordTrace_append hprefix tailTrace_2019
  have hstable : (prefixWord ++ tailWord_2019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019).length < 2 ^ (prefixWord ++ tailWord_2019).sum := by decide
  have hdescent : baseEnd_2019 < baseStart_2019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 3, 5]
def baseStart_2045 : Nat := 118140960795 + 2045 * 2 ^ 59
def prefixEnd_2045 : Nat := 4983230072969 + 3 ^ 40 * 2045 * 2
def baseEnd_2045 : Nat := 350022646183244209367

theorem tailTrace_2045 : CollatzResearch.WordTrace tailWord_2045 prefixEnd_2045 350022646183244209367 := by
  unfold tailWord_2045
  simp only [CollatzResearch.WordTrace]
  refine ⟨74587277598789103303589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49724851732526068869059 74587277598789103303589)
  ·
    refine ⟨13985114549772956869423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74587277598789103303589 13985114549772956869423)
    ·
      refine ⟨20977671824659435304135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13985114549772956869423 20977671824659435304135)
      ·
        refine ⟨31466507736989152956203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20977671824659435304135 31466507736989152956203)
        ·
          refine ⟨47199761605483729434305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31466507736989152956203 47199761605483729434305)
          ·
            refine ⟨35399821204112797075729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47199761605483729434305 35399821204112797075729)
            ·
              refine ⟨26549865903084597806797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35399821204112797075729 26549865903084597806797)
              ·
                refine ⟨9956199713656724177549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26549865903084597806797 9956199713656724177549)
                ·
                  refine ⟨3733574892621271566581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9956199713656724177549 3733574892621271566581)
                  ·
                    refine ⟨350022646183244209367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3733574892621271566581 350022646183244209367)
                    ·
                      rfl

theorem cell23_2045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_2045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045 prefixEnd_2045 := by exact prefixLift 2045
  have htrace : WordTrace (prefixWord ++ tailWord_2045) baseStart_2045 baseEnd_2045 := by
    simpa [prefixWord, tailWord_2045, baseEnd_2045] using wordTrace_append hprefix tailTrace_2045
  have hstable : (prefixWord ++ tailWord_2045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045).length < 2 ^ (prefixWord ++ tailWord_2045).sum := by decide
  have hdescent : baseEnd_2045 < baseStart_2045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062 : List Nat := [4, 1, 1, 2, 2, 1, 1, 5, 1, 5]
def baseStart_2062 : Nat := 118140960795 + 2062 * 2 ^ 59
def prefixEnd_2062 : Nat := 4983230072969 + 3 ^ 40 * 2062 * 2
def baseEnd_2062 : Nat := 352932369892055371841

theorem tailTrace_2062 : CollatzResearch.WordTrace tailWord_2062 prefixEnd_2062 352932369892055371841 := by
  unfold tailWord_2062
  simp only [CollatzResearch.WordTrace]
  refine ⟨9400914817150125834055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50138212358134004448293 9400914817150125834055)
  ·
    refine ⟨14101372225725188751083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9400914817150125834055 14101372225725188751083)
    ·
      refine ⟨21152058338587783126625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14101372225725188751083 21152058338587783126625)
      ·
        refine ⟨15864043753940837344969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21152058338587783126625 15864043753940837344969)
        ·
          refine ⟨11898032815455628008727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15864043753940837344969 11898032815455628008727)
          ·
            refine ⟨17847049223183442013091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11898032815455628008727 17847049223183442013091)
            ·
              refine ⟨26770573834775163019637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17847049223183442013091 26770573834775163019637)
              ·
                refine ⟨2509741297010171533091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26770573834775163019637 2509741297010171533091)
                ·
                  refine ⟨3764611945515257299637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2509741297010171533091 3764611945515257299637)
                  ·
                    refine ⟨352932369892055371841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3764611945515257299637 352932369892055371841)
                    ·
                      rfl

theorem cell23_2062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_2062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062 prefixEnd_2062 := by exact prefixLift 2062
  have htrace : WordTrace (prefixWord ++ tailWord_2062) baseStart_2062 baseEnd_2062 := by
    simpa [prefixWord, tailWord_2062, baseEnd_2062] using wordTrace_append hprefix tailTrace_2062
  have hstable : (prefixWord ++ tailWord_2062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062).length < 2 ^ (prefixWord ++ tailWord_2062).sum := by decide
  have hdescent : baseEnd_2062 < baseStart_2062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 4]
def baseStart_2065 : Nat := 118140960795 + 2065 * 2 ^ 59
def prefixEnd_2065 : Nat := 4983230072969 + 3 ^ 40 * 2065 * 2
def baseEnd_2065 : Nat := 1060337551639654378009

theorem tailTrace_2065 : CollatzResearch.WordTrace tailWord_2065 prefixEnd_2065 1060337551639654378009 := by
  unfold tailWord_2065
  simp only [CollatzResearch.WordTrace]
  refine ⟨75316737526332519031649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50211158350888346021099 75316737526332519031649)
  ·
    refine ⟨56487553144749389273737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75316737526332519031649 56487553144749389273737)
    ·
      refine ⟨42365664858562041955303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56487553144749389273737 42365664858562041955303)
      ·
        refine ⟨63548497287843062932955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42365664858562041955303 63548497287843062932955)
        ·
          refine ⟨95322745931764594399433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63548497287843062932955 95322745931764594399433)
          ·
            refine ⟨71492059448823445799575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95322745931764594399433 71492059448823445799575)
            ·
              refine ⟨107238089173235168699363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71492059448823445799575 107238089173235168699363)
              ·
                refine ⟨160857133759852753049045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107238089173235168699363 160857133759852753049045)
                ·
                  refine ⟨3770089072496548899587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 160857133759852753049045 3770089072496548899587)
                  ·
                    refine ⟨5655133608744823349381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3770089072496548899587 5655133608744823349381)
                    ·
                      refine ⟨1060337551639654378009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5655133608744823349381 1060337551639654378009)
                      ·
                        rfl

theorem cell23_2065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_2065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065 prefixEnd_2065 := by exact prefixLift 2065
  have htrace : WordTrace (prefixWord ++ tailWord_2065) baseStart_2065 baseEnd_2065 := by
    simpa [prefixWord, tailWord_2065, baseEnd_2065] using wordTrace_append hprefix tailTrace_2065
  have hstable : (prefixWord ++ tailWord_2065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065).length < 2 ^ (prefixWord ++ tailWord_2065).sum := by decide
  have hdescent : baseEnd_2065 < baseStart_2065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076 : List Nat := [2, 2, 3, 1, 3, 3, 1, 1, 3, 1, 3]
def baseStart_2076 : Nat := 118140960795 + 2076 * 2 ^ 59
def prefixEnd_2076 : Nat := 4983230072969 + 3 ^ 40 * 2076 * 2
def baseEnd_2076 : Nat := 1065985838839111340459

theorem tailTrace_2076 : CollatzResearch.WordTrace tailWord_2076 prefixEnd_2076 1065985838839111340459 := by
  unfold tailWord_2076
  simp only [CollatzResearch.WordTrace]
  refine ⟨37858970243240698841041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50478626990987598454721 37858970243240698841041)
  ·
    refine ⟨28394227682430524130781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37858970243240698841041 28394227682430524130781)
    ·
      refine ⟨10647835380911446549043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28394227682430524130781 10647835380911446549043)
      ·
        refine ⟨15971753071367169823565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10647835380911446549043 15971753071367169823565)
        ·
          refine ⟨5989407401762688683837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15971753071367169823565 5989407401762688683837)
          ·
            refine ⟨2246027775661008256439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5989407401762688683837 2246027775661008256439)
            ·
              refine ⟨3369041663491512384659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2246027775661008256439 3369041663491512384659)
              ·
                refine ⟨5053562495237268576989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3369041663491512384659 5053562495237268576989)
                ·
                  refine ⟨1895085935713975716371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5053562495237268576989 1895085935713975716371)
                  ·
                    refine ⟨2842628903570963574557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1895085935713975716371 2842628903570963574557)
                    ·
                      refine ⟨1065985838839111340459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2842628903570963574557 1065985838839111340459)
                      ·
                        rfl

theorem cell23_2076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_2076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076 prefixEnd_2076 := by exact prefixLift 2076
  have htrace : WordTrace (prefixWord ++ tailWord_2076) baseStart_2076 baseEnd_2076 := by
    simpa [prefixWord, tailWord_2076, baseEnd_2076] using wordTrace_append hprefix tailTrace_2076
  have hstable : (prefixWord ++ tailWord_2076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076).length < 2 ^ (prefixWord ++ tailWord_2076).sum := by decide
  have hdescent : baseEnd_2076 < baseStart_2076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_2082 : Nat := 118140960795 + 2082 * 2 ^ 59
def prefixEnd_2082 : Nat := 4983230072969 + 3 ^ 40 * 2082 * 2
def baseEnd_2082 : Nat := 1069066722766087865431

theorem tailTrace_2082 : CollatzResearch.WordTrace tailWord_2082 prefixEnd_2082 1069066722766087865431 := by
  unfold tailWord_2082
  simp only [CollatzResearch.WordTrace]
  refine ⟨18984194616186105600125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50624518976496281600333 18984194616186105600125)
  ·
    refine ⟨7119072981069789600047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18984194616186105600125 7119072981069789600047)
    ·
      refine ⟨10678609471604684400071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7119072981069789600047 10678609471604684400071)
      ·
        refine ⟨16017914207407026600107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10678609471604684400071 16017914207407026600107)
        ·
          refine ⟨24026871311110539900161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16017914207407026600107 24026871311110539900161)
          ·
            refine ⟨18020153483332904925121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24026871311110539900161 18020153483332904925121)
            ·
              refine ⟨13515115112499678693841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18020153483332904925121 13515115112499678693841)
              ·
                refine ⟨10136336334374759020381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13515115112499678693841 10136336334374759020381)
                ·
                  refine ⟨3801126125390534632643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10136336334374759020381 3801126125390534632643)
                  ·
                    refine ⟨5701689188085801948965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3801126125390534632643 5701689188085801948965)
                    ·
                      refine ⟨1069066722766087865431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5701689188085801948965 1069066722766087865431)
                      ·
                        rfl

theorem cell23_2082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_2082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082 prefixEnd_2082 := by exact prefixLift 2082
  have htrace : WordTrace (prefixWord ++ tailWord_2082) baseStart_2082 baseEnd_2082 := by
    simpa [prefixWord, tailWord_2082, baseEnd_2082] using wordTrace_append hprefix tailTrace_2082
  have hstable : (prefixWord ++ tailWord_2082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082).length < 2 ^ (prefixWord ++ tailWord_2082).sum := by decide
  have hdescent : baseEnd_2082 < baseStart_2082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2099 : List Nat := [1, 1, 1, 2, 4, 1, 2, 4, 3, 2, 2]
def baseStart_2099 : Nat := 118140960795 + 2099 * 2 ^ 59
def prefixEnd_2099 : Nat := 4983230072969 + 3 ^ 40 * 2099 * 2
def baseEnd_2099 : Nat := 1077795893892521352853

theorem tailTrace_2099 : CollatzResearch.WordTrace tailWord_2099 prefixEnd_2099 1077795893892521352853 := by
  unfold tailWord_2099
  simp only [CollatzResearch.WordTrace]
  refine ⟨76556819403156325769351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51037879602104217179567 76556819403156325769351)
  ·
    refine ⟨114835229104734488654027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76556819403156325769351 114835229104734488654027)
    ·
      refine ⟨172252843657101732981041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114835229104734488654027 172252843657101732981041)
      ·
        refine ⟨129189632742826299735781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172252843657101732981041 129189632742826299735781)
        ·
          refine ⟨24223056139279931200459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129189632742826299735781 24223056139279931200459)
          ·
            refine ⟨36334584208919896800689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24223056139279931200459 36334584208919896800689)
            ·
              refine ⟨27250938156689922600517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36334584208919896800689 27250938156689922600517)
              ·
                refine ⟨5109550904379360487597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27250938156689922600517 5109550904379360487597)
                ·
                  refine ⟨1916081589142260182849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5109550904379360487597 1916081589142260182849)
                  ·
                    refine ⟨1437061191856695137137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1916081589142260182849 1437061191856695137137)
                    ·
                      refine ⟨1077795893892521352853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1437061191856695137137 1077795893892521352853)
                      ·
                        rfl

theorem cell23_2099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 2, 2].length) (baseStart_2099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2099 prefixEnd_2099 := by exact prefixLift 2099
  have htrace : WordTrace (prefixWord ++ tailWord_2099) baseStart_2099 baseEnd_2099 := by
    simpa [prefixWord, tailWord_2099, baseEnd_2099] using wordTrace_append hprefix tailTrace_2099
  have hstable : (prefixWord ++ tailWord_2099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2099).length < 2 ^ (prefixWord ++ tailWord_2099).sum := by decide
  have hdescent : baseEnd_2099 < baseStart_2099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112 : List Nat := [2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 4]
def baseStart_2112 : Nat := 118140960795 + 2112 * 2 ^ 59
def prefixEnd_2112 : Nat := 4983230072969 + 3 ^ 40 * 2112 * 2
def baseEnd_2112 : Nat := 1084471142400970490293

theorem tailTrace_2112 : CollatzResearch.WordTrace tailWord_2112 prefixEnd_2112 1084471142400970490293 := by
  unfold tailWord_2112
  simp only [CollatzResearch.WordTrace]
  refine ⟨38515484178029772996295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51353978904039697328393 38515484178029772996295)
  ·
    refine ⟨57773226267044659494443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38515484178029772996295 57773226267044659494443)
    ·
      refine ⟨86659839400566989241665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57773226267044659494443 86659839400566989241665)
      ·
        refine ⟨64994879550425241931249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86659839400566989241665 64994879550425241931249)
        ·
          refine ⟨48746159662818931448437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64994879550425241931249 48746159662818931448437)
          ·
            refine ⟨4569952468389274823291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48746159662818931448437 4569952468389274823291)
            ·
              refine ⟨6854928702583912234937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4569952468389274823291 6854928702583912234937)
              ·
                refine ⟨5141196526937934176203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6854928702583912234937 5141196526937934176203)
                ·
                  refine ⟨7711794790406901264305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5141196526937934176203 7711794790406901264305)
                  ·
                    refine ⟨5783846092805175948229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7711794790406901264305 5783846092805175948229)
                    ·
                      refine ⟨1084471142400970490293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5783846092805175948229 1084471142400970490293)
                      ·
                        rfl

theorem cell23_2112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_2112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2112 prefixEnd_2112 := by exact prefixLift 2112
  have htrace : WordTrace (prefixWord ++ tailWord_2112) baseStart_2112 baseEnd_2112 := by
    simpa [prefixWord, tailWord_2112, baseEnd_2112] using wordTrace_append hprefix tailTrace_2112
  have hstable : (prefixWord ++ tailWord_2112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112).length < 2 ^ (prefixWord ++ tailWord_2112).sum := by decide
  have hdescent : baseEnd_2112 < baseStart_2112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 5, 3, 3]
def baseStart_2132 : Nat := 118140960795 + 2132 * 2 ^ 59
def prefixEnd_2132 : Nat := 4983230072969 + 3 ^ 40 * 2132 * 2
def baseEnd_2132 : Nat := 1094740755490892240201

theorem tailTrace_2132 : CollatzResearch.WordTrace tailWord_2132 prefixEnd_2132 1094740755490892240201 := by
  unfold tailWord_2132
  simp only [CollatzResearch.WordTrace]
  refine ⟨38880214141801480860325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51840285522401974480433 38880214141801480860325)
  ·
    refine ⟨7290040151587777661311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38880214141801480860325 7290040151587777661311)
    ·
      refine ⟨10935060227381666491967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7290040151587777661311 10935060227381666491967)
      ·
        refine ⟨16402590341072499737951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10935060227381666491967 16402590341072499737951)
        ·
          refine ⟨24603885511608749606927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16402590341072499737951 24603885511608749606927)
          ·
            refine ⟨36905828267413124410391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24603885511608749606927 36905828267413124410391)
            ·
              refine ⟨55358742401119686615587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36905828267413124410391 55358742401119686615587)
              ·
                refine ⟨83038113601679529923381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55358742401119686615587 83038113601679529923381)
                ·
                  refine ⟨7784823150157455930317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83038113601679529923381 7784823150157455930317)
                  ·
                    refine ⟨2919308681309045973869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7784823150157455930317 2919308681309045973869)
                    ·
                      refine ⟨1094740755490892240201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2919308681309045973869 1094740755490892240201)
                      ·
                        rfl

theorem cell23_2132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_2132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2132 prefixEnd_2132 := by exact prefixLift 2132
  have htrace : WordTrace (prefixWord ++ tailWord_2132) baseStart_2132 baseEnd_2132 := by
    simpa [prefixWord, tailWord_2132, baseEnd_2132] using wordTrace_append hprefix tailTrace_2132
  have hstable : (prefixWord ++ tailWord_2132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132).length < 2 ^ (prefixWord ++ tailWord_2132).sum := by decide
  have hdescent : baseEnd_2132 < baseStart_2132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133 : List Nat := [1, 3, 2, 2, 1, 4, 1, 4, 1, 2, 2]
def baseStart_2133 : Nat := 118140960795 + 2133 * 2 ^ 59
def prefixEnd_2133 : Nat := 4983230072969 + 3 ^ 40 * 2133 * 2
def baseEnd_2133 : Nat := 1095254236145388327697

theorem tailTrace_2133 : CollatzResearch.WordTrace tailWord_2133 prefixEnd_2133 1095254236145388327697 := by
  unfold tailWord_2133
  simp only [CollatzResearch.WordTrace]
  refine ⟨77796901279980132507053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51864600853320088338035 77796901279980132507053)
  ·
    refine ⟨29173837979992549690145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77796901279980132507053 29173837979992549690145)
    ·
      refine ⟨21880378484994412267609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29173837979992549690145 21880378484994412267609)
      ·
        refine ⟨16410283863745809200707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21880378484994412267609 16410283863745809200707)
        ·
          refine ⟨24615425795618713801061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16410283863745809200707 24615425795618713801061)
          ·
            refine ⟨4615392336678508837699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24615425795618713801061 4615392336678508837699)
            ·
              refine ⟨6923088505017763256549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4615392336678508837699 6923088505017763256549)
              ·
                refine ⟨1298079094690830610603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6923088505017763256549 1298079094690830610603)
                ·
                  refine ⟨1947118642036245915905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298079094690830610603 1947118642036245915905)
                  ·
                    refine ⟨1460338981527184436929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1947118642036245915905 1460338981527184436929)
                    ·
                      refine ⟨1095254236145388327697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1460338981527184436929 1095254236145388327697)
                      ·
                        rfl

theorem cell23_2133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_2133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2133 prefixEnd_2133 := by exact prefixLift 2133
  have htrace : WordTrace (prefixWord ++ tailWord_2133) baseStart_2133 baseEnd_2133 := by
    simpa [prefixWord, tailWord_2133, baseEnd_2133] using wordTrace_append hprefix tailTrace_2133
  have hstable : (prefixWord ++ tailWord_2133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133).length < 2 ^ (prefixWord ++ tailWord_2133).sum := by decide
  have hdescent : baseEnd_2133 < baseStart_2133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 2, 7]
def baseStart_2135 : Nat := 118140960795 + 2135 * 2 ^ 59
def prefixEnd_2135 : Nat := 4983230072969 + 3 ^ 40 * 2135 * 2
def baseEnd_2135 : Nat := 365427065818126834229

theorem tailTrace_2135 : CollatzResearch.WordTrace tailWord_2135 prefixEnd_2135 365427065818126834229 := by
  unfold tailWord_2135
  simp only [CollatzResearch.WordTrace]
  refine ⟨77869847272734474079859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51913231515156316053239 77869847272734474079859)
  ·
    refine ⟨116804770909101711119789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77869847272734474079859 116804770909101711119789)
    ·
      refine ⟨43801789090913141669921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116804770909101711119789 43801789090913141669921)
      ·
        refine ⟨32851341818184856252441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43801789090913141669921 32851341818184856252441)
        ·
          refine ⟨24638506363638642189331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32851341818184856252441 24638506363638642189331)
          ·
            refine ⟨36957759545457963283997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24638506363638642189331 36957759545457963283997)
            ·
              refine ⟨13859159829546736231499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36957759545457963283997 13859159829546736231499)
              ·
                refine ⟨20788739744320104347249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13859159829546736231499 20788739744320104347249)
                ·
                  refine ⟨15591554808240078260437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20788739744320104347249 15591554808240078260437)
                  ·
                    refine ⟨365427065818126834229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15591554808240078260437 365427065818126834229)
                    ·
                      rfl

theorem cell23_2135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_2135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135 prefixEnd_2135 := by exact prefixLift 2135
  have htrace : WordTrace (prefixWord ++ tailWord_2135) baseStart_2135 baseEnd_2135 := by
    simpa [prefixWord, tailWord_2135, baseEnd_2135] using wordTrace_append hprefix tailTrace_2135
  have hstable : (prefixWord ++ tailWord_2135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135).length < 2 ^ (prefixWord ++ tailWord_2135).sum := by decide
  have hdescent : baseEnd_2135 < baseStart_2135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 1, 4, 5]
def baseStart_2145 : Nat := 118140960795 + 2145 * 2 ^ 59
def prefixEnd_2145 : Nat := 4983230072969 + 3 ^ 40 * 2145 * 2
def baseEnd_2145 : Nat := 1101416003999341377641

theorem tailTrace_2145 : CollatzResearch.WordTrace tailWord_2145 prefixEnd_2145 1101416003999341377641 := by
  unfold tailWord_2145
  simp only [CollatzResearch.WordTrace]
  refine ⟨78234577236506181943889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52156384824337454629259 78234577236506181943889)
  ·
    refine ⟨58675932927379636457917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78234577236506181943889 58675932927379636457917)
    ·
      refine ⟨22003474847767363671719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58675932927379636457917 22003474847767363671719)
      ·
        refine ⟨33005212271651045507579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22003474847767363671719 33005212271651045507579)
        ·
          refine ⟨49507818407476568261369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33005212271651045507579 49507818407476568261369)
          ·
            refine ⟨37130863805607426196027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49507818407476568261369 37130863805607426196027)
            ·
              refine ⟨55696295708411139294041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37130863805607426196027 55696295708411139294041)
              ·
                refine ⟨41772221781308354470531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55696295708411139294041 41772221781308354470531)
                ·
                  refine ⟨62658332671962531705797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41772221781308354470531 62658332671962531705797)
                  ·
                    refine ⟨11748437375992974694837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62658332671962531705797 11748437375992974694837)
                    ·
                      refine ⟨1101416003999341377641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11748437375992974694837 1101416003999341377641)
                      ·
                        rfl

theorem cell23_2145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_2145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145 prefixEnd_2145 := by exact prefixLift 2145
  have htrace : WordTrace (prefixWord ++ tailWord_2145) baseStart_2145 baseEnd_2145 := by
    simpa [prefixWord, tailWord_2145, baseEnd_2145] using wordTrace_append hprefix tailTrace_2145
  have hstable : (prefixWord ++ tailWord_2145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145).length < 2 ^ (prefixWord ++ tailWord_2145).sum := by decide
  have hdescent : baseEnd_2145 < baseStart_2145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146 : List Nat := [3, 3, 2, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_2146 : Nat := 118140960795 + 2146 * 2 ^ 59
def prefixEnd_2146 : Nat := 4983230072969 + 3 ^ 40 * 2146 * 2
def baseEnd_2146 : Nat := 1101929484653837465137

theorem tailTrace_2146 : CollatzResearch.WordTrace tailWord_2146 prefixEnd_2146 1101929484653837465137 := by
  unfold tailWord_2146
  simp only [CollatzResearch.WordTrace]
  refine ⟨19567762558220838182573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52180700155255568486861 19567762558220838182573)
  ·
    refine ⟨7337910959332814318465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19567762558220838182573 7337910959332814318465)
    ·
      refine ⟨5503433219499610738849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7337910959332814318465 5503433219499610738849)
      ·
        refine ⟨4127574914624708054137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5503433219499610738849 4127574914624708054137)
        ·
          refine ⟨3095681185968531040603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4127574914624708054137 3095681185968531040603)
          ·
            refine ⟨4643521778952796560905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3095681185968531040603 4643521778952796560905)
            ·
              refine ⟨3482641334214597420679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4643521778952796560905 3482641334214597420679)
              ·
                refine ⟨5223962001321896131019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3482641334214597420679 5223962001321896131019)
                ·
                  refine ⟨7835943001982844196529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5223962001321896131019 7835943001982844196529)
                  ·
                    refine ⟨5876957251487133147397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7835943001982844196529 5876957251487133147397)
                    ·
                      refine ⟨1101929484653837465137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5876957251487133147397 1101929484653837465137)
                      ·
                        rfl

theorem cell23_2146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_2146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146 prefixEnd_2146 := by exact prefixLift 2146
  have htrace : WordTrace (prefixWord ++ tailWord_2146) baseStart_2146 baseEnd_2146 := by
    simpa [prefixWord, tailWord_2146, baseEnd_2146] using wordTrace_append hprefix tailTrace_2146
  have hstable : (prefixWord ++ tailWord_2146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146).length < 2 ^ (prefixWord ++ tailWord_2146).sum := by decide
  have hdescent : baseEnd_2146 < baseStart_2146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149 : List Nat := [1, 3, 1, 3, 2, 3, 2, 1, 1, 3, 3]
def baseStart_2149 : Nat := 118140960795 + 2149 * 2 ^ 59
def prefixEnd_2149 : Nat := 4983230072969 + 3 ^ 40 * 2149 * 2
def baseEnd_2149 : Nat := 1103469926617325727623

theorem tailTrace_2149 : CollatzResearch.WordTrace tailWord_2149 prefixEnd_2149 1103469926617325727623 := by
  unfold tailWord_2149
  simp only [CollatzResearch.WordTrace]
  refine ⟨78380469222014865089501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52253646148009910059667 78380469222014865089501)
  ·
    refine ⟨29392675958255574408563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78380469222014865089501 29392675958255574408563)
    ·
      refine ⟨44089013937383361612845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29392675958255574408563 44089013937383361612845)
      ·
        refine ⟨16533380226518760604817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44089013937383361612845 16533380226518760604817)
        ·
          refine ⟨12400035169889070453613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16533380226518760604817 12400035169889070453613)
          ·
            refine ⟨4650013188708401420105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12400035169889070453613 4650013188708401420105)
            ·
              refine ⟨3487509891531301065079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4650013188708401420105 3487509891531301065079)
              ·
                refine ⟨5231264837296951597619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3487509891531301065079 5231264837296951597619)
                ·
                  refine ⟨7846897255945427396429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5231264837296951597619 7846897255945427396429)
                  ·
                    refine ⟨2942586470979535273661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7846897255945427396429 2942586470979535273661)
                    ·
                      refine ⟨1103469926617325727623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2942586470979535273661 1103469926617325727623)
                      ·
                        rfl

theorem cell23_2149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_2149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149 prefixEnd_2149 := by exact prefixLift 2149
  have htrace : WordTrace (prefixWord ++ tailWord_2149) baseStart_2149 baseEnd_2149 := by
    simpa [prefixWord, tailWord_2149, baseEnd_2149] using wordTrace_append hprefix tailTrace_2149
  have hstable : (prefixWord ++ tailWord_2149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149).length < 2 ^ (prefixWord ++ tailWord_2149).sum := by decide
  have hdescent : baseEnd_2149 < baseStart_2149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 3, 3, 2]
def baseStart_2159 : Nat := 118140960795 + 2159 * 2 ^ 59
def prefixEnd_2159 : Nat := 4983230072969 + 3 ^ 40 * 2159 * 2
def baseEnd_2159 : Nat := 1108604733162286602577

theorem tailTrace_2159 : CollatzResearch.WordTrace tailWord_2159 prefixEnd_2159 1108604733162286602577 := by
  unfold tailWord_2159
  simp only [CollatzResearch.WordTrace]
  refine ⟨78745199185786572953531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52496799457191048635687 78745199185786572953531)
  ·
    refine ⟨118117798778679859430297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78745199185786572953531 118117798778679859430297)
    ·
      refine ⟨88588349084009894572723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118117798778679859430297 88588349084009894572723)
      ·
        refine ⟨132882523626014841859085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88588349084009894572723 132882523626014841859085)
        ·
          refine ⟨49830946359755565697157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132882523626014841859085 49830946359755565697157)
          ·
            refine ⟨9343302442454168568217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49830946359755565697157 9343302442454168568217)
            ·
              refine ⟨7007476831840626426163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9343302442454168568217 7007476831840626426163)
              ·
                refine ⟨10511215247760939639245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7007476831840626426163 10511215247760939639245)
                ·
                  refine ⟨3941705717910352364717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10511215247760939639245 3941705717910352364717)
                  ·
                    refine ⟨1478139644216382136769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3941705717910352364717 1478139644216382136769)
                    ·
                      refine ⟨1108604733162286602577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1478139644216382136769 1108604733162286602577)
                      ·
                        rfl

theorem cell23_2159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 3, 2].length) (baseStart_2159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159 prefixEnd_2159 := by exact prefixLift 2159
  have htrace : WordTrace (prefixWord ++ tailWord_2159) baseStart_2159 baseEnd_2159 := by
    simpa [prefixWord, tailWord_2159, baseEnd_2159] using wordTrace_append hprefix tailTrace_2159
  have hstable : (prefixWord ++ tailWord_2159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159).length < 2 ^ (prefixWord ++ tailWord_2159).sum := by decide
  have hdescent : baseEnd_2159 < baseStart_2159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353 : List Nat := [1, 2, 2, 3, 5, 1, 1, 2, 6]
def baseStart_2353 : Nat := 118140960795 + 2353 * 2 ^ 59
def prefixEnd_2353 : Nat := 4983230072969 + 3 ^ 40 * 2353 * 2
def baseEnd_2353 : Nat := 134246664459391952965

theorem tailTrace_2353 : CollatzResearch.WordTrace tailWord_2353 prefixEnd_2353 134246664459391952965 := by
  unfold tailWord_2353
  simp only [CollatzResearch.WordTrace]
  refine ⟨85820960482957705515713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57213973655305137010475 85820960482957705515713)
  ·
    refine ⟨64365720362218279136785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85820960482957705515713 64365720362218279136785)
    ·
      refine ⟨48274290271663709352589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64365720362218279136785 48274290271663709352589)
      ·
        refine ⟨18102858851873891007221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48274290271663709352589 18102858851873891007221)
        ·
          refine ⟨1697143017363177281927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18102858851873891007221 1697143017363177281927)
          ·
            refine ⟨2545714526044765922891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1697143017363177281927 2545714526044765922891)
            ·
              refine ⟨3818571789067148884337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2545714526044765922891 3818571789067148884337)
              ·
                refine ⟨2863928841800361663253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3818571789067148884337 2863928841800361663253)
                ·
                  refine ⟨134246664459391952965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2863928841800361663253 134246664459391952965)
                  ·
                    rfl

theorem cell23_2353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 6].length) (baseStart_2353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2353 prefixEnd_2353 := by exact prefixLift 2353
  have htrace : WordTrace (prefixWord ++ tailWord_2353) baseStart_2353 baseEnd_2353 := by
    simpa [prefixWord, tailWord_2353, baseEnd_2353] using wordTrace_append hprefix tailTrace_2353
  have hstable : (prefixWord ++ tailWord_2353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353).length < 2 ^ (prefixWord ++ tailWord_2353).sum := by decide
  have hdescent : baseEnd_2353 < baseStart_2353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386 : List Nat := [3, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4]
def baseStart_2386 : Nat := 118140960795 + 2386 * 2 ^ 59
def prefixEnd_2386 : Nat := 4983230072969 + 3 ^ 40 * 2386 * 2
def baseEnd_2386 : Nat := 1225164841732898464033

theorem tailTrace_2386 : CollatzResearch.WordTrace tailWord_2386 prefixEnd_2386 1225164841732898464033 := by
  unfold tailWord_2386
  simp only [CollatzResearch.WordTrace]
  refine ⟨21756142340851085366753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58016379575602894311341 21756142340851085366753)
  ·
    refine ⟨16317106755638314025065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21756142340851085366753 16317106755638314025065)
    ·
      refine ⟨12237830066728735518799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16317106755638314025065 12237830066728735518799)
      ·
        refine ⟨18356745100093103278199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12237830066728735518799 18356745100093103278199)
        ·
          refine ⟨27535117650139654917299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18356745100093103278199 27535117650139654917299)
          ·
            refine ⟨41302676475209482375949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27535117650139654917299 41302676475209482375949)
            ·
              refine ⟨15488503678203555890981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41302676475209482375949 15488503678203555890981)
              ·
                refine ⟨2904094439663166729559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15488503678203555890981 2904094439663166729559)
                ·
                  refine ⟨4356141659494750094339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2904094439663166729559 4356141659494750094339)
                  ·
                    refine ⟨6534212489242125141509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4356141659494750094339 6534212489242125141509)
                    ·
                      refine ⟨1225164841732898464033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6534212489242125141509 1225164841732898464033)
                      ·
                        rfl

theorem cell23_2386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_2386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386 prefixEnd_2386 := by exact prefixLift 2386
  have htrace : WordTrace (prefixWord ++ tailWord_2386) baseStart_2386 baseEnd_2386 := by
    simpa [prefixWord, tailWord_2386, baseEnd_2386] using wordTrace_append hprefix tailTrace_2386
  have hstable : (prefixWord ++ tailWord_2386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386).length < 2 ^ (prefixWord ++ tailWord_2386).sum := by decide
  have hdescent : baseEnd_2386 < baseStart_2386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2399 : List Nat := [1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 4]
def baseStart_2399 : Nat := 118140960795 + 2399 * 2 ^ 59
def prefixEnd_2399 : Nat := 4983230072969 + 3 ^ 40 * 2399 * 2
def baseEnd_2399 : Nat := 1231840090241347601473

theorem tailTrace_2399 : CollatzResearch.WordTrace tailWord_2399 prefixEnd_2399 1231840090241347601473 := by
  unfold tailWord_2399
  simp only [CollatzResearch.WordTrace]
  refine ⟨87498718316307561690251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58332478877538374460167 87498718316307561690251)
  ·
    refine ⟨131248077474461342535377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87498718316307561690251 131248077474461342535377)
    ·
      refine ⟨98436058105846006901533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131248077474461342535377 98436058105846006901533)
      ·
        refine ⟨36913521789692252588075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98436058105846006901533 36913521789692252588075)
        ·
          refine ⟨55370282684538378882113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36913521789692252588075 55370282684538378882113)
          ·
            refine ⟨41527712013403784161585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55370282684538378882113 41527712013403784161585)
            ·
              refine ⟨31145784010052838121189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41527712013403784161585 31145784010052838121189)
              ·
                refine ⟨5839834501884907147723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31145784010052838121189 5839834501884907147723)
                ·
                  refine ⟨8759751752827360721585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5839834501884907147723 8759751752827360721585)
                  ·
                    refine ⟨6569813814620520541189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8759751752827360721585 6569813814620520541189)
                    ·
                      refine ⟨1231840090241347601473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6569813814620520541189 1231840090241347601473)
                      ·
                        rfl

theorem cell23_2399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_2399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2399 prefixEnd_2399 := by exact prefixLift 2399
  have htrace : WordTrace (prefixWord ++ tailWord_2399) baseStart_2399 baseEnd_2399 := by
    simpa [prefixWord, tailWord_2399, baseEnd_2399] using wordTrace_append hprefix tailTrace_2399
  have hstable : (prefixWord ++ tailWord_2399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2399).length < 2 ^ (prefixWord ++ tailWord_2399).sum := by decide
  have hdescent : baseEnd_2399 < baseStart_2399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 3]
def baseStart_2419 : Nat := 118140960795 + 2419 * 2 ^ 59
def prefixEnd_2419 : Nat := 4983230072969 + 3 ^ 40 * 2419 * 2
def baseEnd_2419 : Nat := 1242109703331269351381

theorem tailTrace_2419 : CollatzResearch.WordTrace tailWord_2419 prefixEnd_2419 1242109703331269351381 := by
  unfold tailWord_2419
  simp only [CollatzResearch.WordTrace]
  refine ⟨88228178243850977418311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58818785495900651612207 88228178243850977418311)
  ·
    refine ⟨132342267365776466127467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88228178243850977418311 132342267365776466127467)
    ·
      refine ⟨198513401048664699191201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132342267365776466127467 198513401048664699191201)
      ·
        refine ⟨148885050786498524393401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198513401048664699191201 148885050786498524393401)
        ·
          refine ⟨111663788089873893295051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148885050786498524393401 111663788089873893295051)
          ·
            refine ⟨167495682134810839942577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111663788089873893295051 167495682134810839942577)
            ·
              refine ⟨125621761601108129956933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167495682134810839942577 125621761601108129956933)
              ·
                refine ⟨23554080300207774366925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125621761601108129956933 23554080300207774366925)
                ·
                  refine ⟨8832780112577915387597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23554080300207774366925 8832780112577915387597)
                  ·
                    refine ⟨3312292542216718270349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8832780112577915387597 3312292542216718270349)
                    ·
                      refine ⟨1242109703331269351381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3312292542216718270349 1242109703331269351381)
                      ·
                        rfl

theorem cell23_2419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 3].length) (baseStart_2419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419 prefixEnd_2419 := by exact prefixLift 2419
  have htrace : WordTrace (prefixWord ++ tailWord_2419) baseStart_2419 baseEnd_2419 := by
    simpa [prefixWord, tailWord_2419, baseEnd_2419] using wordTrace_append hprefix tailTrace_2419
  have hstable : (prefixWord ++ tailWord_2419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419).length < 2 ^ (prefixWord ++ tailWord_2419).sum := by decide
  have hdescent : baseEnd_2419 < baseStart_2419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436 : List Nat := [2, 3, 2, 1, 1, 2, 2, 3, 1, 3, 3]
def baseStart_2436 : Nat := 118140960795 + 2436 * 2 ^ 59
def prefixEnd_2436 : Nat := 4983230072969 + 3 ^ 40 * 2436 * 2
def baseEnd_2436 : Nat := 1250838874457702838803

theorem tailTrace_2436 : CollatzResearch.WordTrace tailWord_2436 prefixEnd_2436 1250838874457702838803 := by
  unfold tailWord_2436
  simp only [CollatzResearch.WordTrace]
  refine ⟨44424109591131440393581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59232146121508587191441 44424109591131440393581)
  ·
    refine ⟨16659041096674290147593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44424109591131440393581 16659041096674290147593)
    ·
      refine ⟨12494280822505717610695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16659041096674290147593 12494280822505717610695)
      ·
        refine ⟨18741421233758576416043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12494280822505717610695 18741421233758576416043)
        ·
          refine ⟨28112131850637864624065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18741421233758576416043 28112131850637864624065)
          ·
            refine ⟨21084098887978398468049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28112131850637864624065 21084098887978398468049)
            ·
              refine ⟨15813074165983798851037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21084098887978398468049 15813074165983798851037)
              ·
                refine ⟨5929902812243924569139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15813074165983798851037 5929902812243924569139)
                ·
                  refine ⟨8894854218365886853709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5929902812243924569139 8894854218365886853709)
                  ·
                    refine ⟨3335570331887207570141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8894854218365886853709 3335570331887207570141)
                    ·
                      refine ⟨1250838874457702838803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3335570331887207570141 1250838874457702838803)
                      ·
                        rfl

theorem cell23_2436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_2436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436 prefixEnd_2436 := by exact prefixLift 2436
  have htrace : WordTrace (prefixWord ++ tailWord_2436) baseStart_2436 baseEnd_2436 := by
    simpa [prefixWord, tailWord_2436, baseEnd_2436] using wordTrace_append hprefix tailTrace_2436
  have hstable : (prefixWord ++ tailWord_2436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436).length < 2 ^ (prefixWord ++ tailWord_2436).sum := by decide
  have hdescent : baseEnd_2436 < baseStart_2436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 2, 6]
def baseStart_2469 : Nat := 118140960795 + 2469 * 2 ^ 59
def prefixEnd_2469 : Nat := 4983230072969 + 3 ^ 40 * 2469 * 2
def baseEnd_2469 : Nat := 422594578685357908717

theorem tailTrace_2469 : CollatzResearch.WordTrace tailWord_2469 prefixEnd_2469 422594578685357908717 := by
  unfold tailWord_2469
  simp only [CollatzResearch.WordTrace]
  refine ⟨90051828062709516738461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60034552041806344492307 90051828062709516738461)
  ·
    refine ⟨33769435523516068776923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90051828062709516738461 33769435523516068776923)
    ·
      refine ⟨50654153285274103165385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33769435523516068776923 50654153285274103165385)
      ·
        refine ⟨37990614963955577374039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50654153285274103165385 37990614963955577374039)
        ·
          refine ⟨56985922445933366061059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37990614963955577374039 56985922445933366061059)
          ·
            refine ⟨85478883668900049091589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56985922445933366061059 85478883668900049091589)
            ·
              refine ⟨16027290687918759204673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85478883668900049091589 16027290687918759204673)
              ·
                refine ⟨12020468015939069403505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16027290687918759204673 12020468015939069403505)
                ·
                  refine ⟨9015351011954302052629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12020468015939069403505 9015351011954302052629)
                  ·
                    refine ⟨422594578685357908717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9015351011954302052629 422594578685357908717)
                    ·
                      rfl

theorem cell23_2469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_2469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2469 prefixEnd_2469 := by exact prefixLift 2469
  have htrace : WordTrace (prefixWord ++ tailWord_2469) baseStart_2469 baseEnd_2469 := by
    simpa [prefixWord, tailWord_2469, baseEnd_2469] using wordTrace_append hprefix tailTrace_2469
  have hstable : (prefixWord ++ tailWord_2469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469).length < 2 ^ (prefixWord ++ tailWord_2469).sum := by decide
  have hdescent : baseEnd_2469 < baseStart_2469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 5, 4, 2]
def baseStart_2476 : Nat := 118140960795 + 2476 * 2 ^ 59
def prefixEnd_2476 : Nat := 4983230072969 + 3 ^ 40 * 2476 * 2
def baseEnd_2476 : Nat := 1271378100637546338619

theorem tailTrace_2476 : CollatzResearch.WordTrace tailWord_2476 prefixEnd_2476 1271378100637546338619 := by
  unfold tailWord_2476
  simp only [CollatzResearch.WordTrace]
  refine ⟨45153569518674856121641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60204759358233141495521 45153569518674856121641)
  ·
    refine ⟨33865177139006142091231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45153569518674856121641 33865177139006142091231)
    ·
      refine ⟨50797765708509213136847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33865177139006142091231 50797765708509213136847)
      ·
        refine ⟨76196648562763819705271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50797765708509213136847 76196648562763819705271)
        ·
          refine ⟨114294972844145729557907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76196648562763819705271 114294972844145729557907)
          ·
            refine ⟨171442459266218594336861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114294972844145729557907 171442459266218594336861)
            ·
              refine ⟨64290922224831972876323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171442459266218594336861 64290922224831972876323)
              ·
                refine ⟨96436383337247959314485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64290922224831972876323 96436383337247959314485)
                ·
                  refine ⟨9040910937866996185733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 96436383337247959314485 9040910937866996185733)
                  ·
                    refine ⟨1695170800850061784825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9040910937866996185733 1695170800850061784825)
                    ·
                      refine ⟨1271378100637546338619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1695170800850061784825 1271378100637546338619)
                      ·
                        rfl

theorem cell23_2476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 4, 2].length) (baseStart_2476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2476 prefixEnd_2476 := by exact prefixLift 2476
  have htrace : WordTrace (prefixWord ++ tailWord_2476) baseStart_2476 baseEnd_2476 := by
    simpa [prefixWord, tailWord_2476, baseEnd_2476] using wordTrace_append hprefix tailTrace_2476
  have hstable : (prefixWord ++ tailWord_2476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476).length < 2 ^ (prefixWord ++ tailWord_2476).sum := by decide
  have hdescent : baseEnd_2476 < baseStart_2476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493 : List Nat := [1, 4, 1, 2, 2, 2, 1, 3, 1, 4, 2]
def baseStart_2493 : Nat := 118140960795 + 2493 * 2 ^ 59
def prefixEnd_2493 : Nat := 4983230072969 + 3 ^ 40 * 2493 * 2
def baseEnd_2493 : Nat := 1280107271763979826041

theorem tailTrace_2493 : CollatzResearch.WordTrace tailWord_2493 prefixEnd_2493 1280107271763979826041 := by
  unfold tailWord_2493
  simp only [CollatzResearch.WordTrace]
  refine ⟨90927179975761615612133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60618119983841077074755 90927179975761615612133)
  ·
    refine ⟨17048846245455302927275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90927179975761615612133 17048846245455302927275)
    ·
      refine ⟨25573269368182954390913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17048846245455302927275 25573269368182954390913)
      ·
        refine ⟨19179952026137215793185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25573269368182954390913 19179952026137215793185)
        ·
          refine ⟨14384964019602911844889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19179952026137215793185 14384964019602911844889)
          ·
            refine ⟨10788723014702183883667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14384964019602911844889 10788723014702183883667)
            ·
              refine ⟨16183084522053275825501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10788723014702183883667 16183084522053275825501)
              ·
                refine ⟨6068656695769978434563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16183084522053275825501 6068656695769978434563)
                ·
                  refine ⟨9102985043654967651845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6068656695769978434563 9102985043654967651845)
                  ·
                    refine ⟨1706809695685306434721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9102985043654967651845 1706809695685306434721)
                    ·
                      refine ⟨1280107271763979826041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1706809695685306434721 1280107271763979826041)
                      ·
                        rfl

theorem cell23_2493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_2493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493 prefixEnd_2493 := by exact prefixLift 2493
  have htrace : WordTrace (prefixWord ++ tailWord_2493) baseStart_2493 baseEnd_2493 := by
    simpa [prefixWord, tailWord_2493, baseEnd_2493] using wordTrace_append hprefix tailTrace_2493
  have hstable : (prefixWord ++ tailWord_2493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493).length < 2 ^ (prefixWord ++ tailWord_2493).sum := by decide
  have hdescent : baseEnd_2493 < baseStart_2493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527 : List Nat := [1, 1, 2, 3, 3, 4, 1, 2, 2, 2, 2]
def baseStart_2527 : Nat := 118140960795 + 2527 * 2 ^ 59
def prefixEnd_2527 : Nat := 4983230072969 + 3 ^ 40 * 2527 * 2
def baseEnd_2527 : Nat := 1297565614016846800885

theorem tailTrace_2527 : CollatzResearch.WordTrace tailWord_2527 prefixEnd_2527 1297565614016846800885 := by
  unfold tailWord_2527
  simp only [CollatzResearch.WordTrace]
  refine ⟨92167261852585422349835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61444841235056948233223 92167261852585422349835)
  ·
    refine ⟨138250892778878133524753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92167261852585422349835 138250892778878133524753)
    ·
      refine ⟨103688169584158600143565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138250892778878133524753 103688169584158600143565)
      ·
        refine ⟨38883063594059475053837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103688169584158600143565 38883063594059475053837)
        ·
          refine ⟨14581148847772303145189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38883063594059475053837 14581148847772303145189)
          ·
            refine ⟨2733965408957306839723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14581148847772303145189 2733965408957306839723)
            ·
              refine ⟨4100948113435960259585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2733965408957306839723 4100948113435960259585)
              ·
                refine ⟨3075711085076970194689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4100948113435960259585 3075711085076970194689)
                ·
                  refine ⟨2306783313807727646017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3075711085076970194689 2306783313807727646017)
                  ·
                    refine ⟨1730087485355795734513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2306783313807727646017 1730087485355795734513)
                    ·
                      refine ⟨1297565614016846800885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1730087485355795734513 1297565614016846800885)
                      ·
                        rfl

theorem cell23_2527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 2, 2].length) (baseStart_2527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527 prefixEnd_2527 := by exact prefixLift 2527
  have htrace : WordTrace (prefixWord ++ tailWord_2527) baseStart_2527 baseEnd_2527 := by
    simpa [prefixWord, tailWord_2527, baseEnd_2527] using wordTrace_append hprefix tailTrace_2527
  have hstable : (prefixWord ++ tailWord_2527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527).length < 2 ^ (prefixWord ++ tailWord_2527).sum := by decide
  have hdescent : baseEnd_2527 < baseStart_2527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533 : List Nat := [1, 3, 1, 5, 2, 1, 2, 1, 7]
def baseStart_2533 : Nat := 118140960795 + 2533 * 2 ^ 59
def prefixEnd_2533 : Nat := 4983230072969 + 3 ^ 40 * 2533 * 2
def baseEnd_2533 : Nat := 144516277549313702873

theorem tailTrace_2533 : CollatzResearch.WordTrace tailWord_2533 prefixEnd_2533 144516277549313702873 := by
  unfold tailWord_2533
  simp only [CollatzResearch.WordTrace]
  refine ⟨92386099830848447068253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61590733220565631378835 92386099830848447068253)
  ·
    refine ⟨34644787436568167650595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92386099830848447068253 34644787436568167650595)
    ·
      refine ⟨51967181154852251475893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34644787436568167650595 51967181154852251475893)
      ·
        refine ⟨4871923233267398575865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51967181154852251475893 4871923233267398575865)
        ·
          refine ⟨3653942424950548931899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4871923233267398575865 3653942424950548931899)
          ·
            refine ⟨5480913637425823397849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3653942424950548931899 5480913637425823397849)
            ·
              refine ⟨4110685228069367548387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5480913637425823397849 4110685228069367548387)
              ·
                refine ⟨6166027842104051322581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4110685228069367548387 6166027842104051322581)
                ·
                  refine ⟨144516277549313702873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6166027842104051322581 144516277549313702873)
                  ·
                    rfl

theorem cell23_2533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 7].length) (baseStart_2533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533 prefixEnd_2533 := by exact prefixLift 2533
  have htrace : WordTrace (prefixWord ++ tailWord_2533) baseStart_2533 baseEnd_2533 := by
    simpa [prefixWord, tailWord_2533, baseEnd_2533] using wordTrace_append hprefix tailTrace_2533
  have hstable : (prefixWord ++ tailWord_2533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533).length < 2 ^ (prefixWord ++ tailWord_2533).sum := by decide
  have hdescent : baseEnd_2533 < baseStart_2533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 7]
def baseStart_2539 : Nat := 118140960795 + 2539 * 2 ^ 59
def prefixEnd_2539 : Nat := 4983230072969 + 3 ^ 40 * 2539 * 2
def baseEnd_2539 : Nat := 1303727381870799850829

theorem tailTrace_2539 : CollatzResearch.WordTrace tailWord_2539 prefixEnd_2539 1303727381870799850829 := by
  unfold tailWord_2539
  simp only [CollatzResearch.WordTrace]
  refine ⟨92604937809111471786671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61736625206074314524447 92604937809111471786671)
  ·
    refine ⟨138907406713667207680007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92604937809111471786671 138907406713667207680007)
    ·
      refine ⟨208361110070500811520011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138907406713667207680007 208361110070500811520011)
      ·
        refine ⟨312541665105751217280017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208361110070500811520011 312541665105751217280017)
        ·
          refine ⟨234406248829313412960013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312541665105751217280017 234406248829313412960013)
          ·
            refine ⟨87902343310992529860005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234406248829313412960013 87902343310992529860005)
            ·
              refine ⟨16481689370811099348751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87902343310992529860005 16481689370811099348751)
              ·
                refine ⟨24722534056216649023127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16481689370811099348751 24722534056216649023127)
                ·
                  refine ⟨37083801084324973534691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24722534056216649023127 37083801084324973534691)
                  ·
                    refine ⟨55625701626487460302037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37083801084324973534691 55625701626487460302037)
                    ·
                      refine ⟨1303727381870799850829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55625701626487460302037 1303727381870799850829)
                      ·
                        rfl

theorem cell23_2539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 7].length) (baseStart_2539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539 prefixEnd_2539 := by exact prefixLift 2539
  have htrace : WordTrace (prefixWord ++ tailWord_2539) baseStart_2539 baseEnd_2539 := by
    simpa [prefixWord, tailWord_2539, baseEnd_2539] using wordTrace_append hprefix tailTrace_2539
  have hstable : (prefixWord ++ tailWord_2539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539).length < 2 ^ (prefixWord ++ tailWord_2539).sum := by decide
  have hdescent : baseEnd_2539 < baseStart_2539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 2, 8]
def baseStart_2559 : Nat := 118140960795 + 2559 * 2 ^ 59
def prefixEnd_2559 : Nat := 4983230072969 + 3 ^ 40 * 2559 * 2
def baseEnd_2559 : Nat := 437998998320240533579

theorem tailTrace_2559 : CollatzResearch.WordTrace tailWord_2559 prefixEnd_2559 437998998320240533579 := by
  unfold tailWord_2559
  simp only [CollatzResearch.WordTrace]
  refine ⟨93334397736654887514731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62222931824436591676487 93334397736654887514731)
  ·
    refine ⟨140001596604982331272097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93334397736654887514731 140001596604982331272097)
    ·
      refine ⟨105001197453736748454073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140001596604982331272097 105001197453736748454073)
      ·
        refine ⟨78750898090302561340555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105001197453736748454073 78750898090302561340555)
        ·
          refine ⟨118126347135453842010833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78750898090302561340555 118126347135453842010833)
          ·
            refine ⟨88594760351590381508125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118126347135453842010833 88594760351590381508125)
            ·
              refine ⟨33223035131846393065547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88594760351590381508125 33223035131846393065547)
              ·
                refine ⟨49834552697769589598321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33223035131846393065547 49834552697769589598321)
                ·
                  refine ⟨37375914523327192198741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49834552697769589598321 37375914523327192198741)
                  ·
                    refine ⟨437998998320240533579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37375914523327192198741 437998998320240533579)
                    ·
                      rfl

theorem cell23_2559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 8].length) (baseStart_2559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559 prefixEnd_2559 := by exact prefixLift 2559
  have htrace : WordTrace (prefixWord ++ tailWord_2559) baseStart_2559 baseEnd_2559 := by
    simpa [prefixWord, tailWord_2559, baseEnd_2559] using wordTrace_append hprefix tailTrace_2559
  have hstable : (prefixWord ++ tailWord_2559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559).length < 2 ^ (prefixWord ++ tailWord_2559).sum := by decide
  have hdescent : baseEnd_2559 < baseStart_2559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567 : List Nat := [1, 1, 4, 3, 4, 1, 1, 3, 5]
def baseStart_2567 : Nat := 118140960795 + 2567 * 2 ^ 59
def prefixEnd_2567 : Nat := 4983230072969 + 3 ^ 40 * 2567 * 2
def baseEnd_2567 : Nat := 146456093355187811189

theorem tailTrace_2567 : CollatzResearch.WordTrace tailWord_2567 prefixEnd_2567 146456093355187811189 := by
  unfold tailWord_2567
  simp only [CollatzResearch.WordTrace]
  refine ⟨93626181707672253805955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62417454471781502537303 93626181707672253805955)
  ·
    refine ⟨140439272561508380708933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93626181707672253805955 140439272561508380708933)
    ·
      refine ⟨26332363605282821382925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140439272561508380708933 26332363605282821382925)
      ·
        refine ⟨9874636351981058018597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26332363605282821382925 9874636351981058018597)
        ·
          refine ⟨1851494315996448378487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9874636351981058018597 1851494315996448378487)
          ·
            refine ⟨2777241473994672567731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1851494315996448378487 2777241473994672567731)
            ·
              refine ⟨4165862210992008851597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2777241473994672567731 4165862210992008851597)
              ·
                refine ⟨1562198329122003319349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4165862210992008851597 1562198329122003319349)
                ·
                  refine ⟨146456093355187811189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1562198329122003319349 146456093355187811189)
                  ·
                    rfl

theorem cell23_2567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 5].length) (baseStart_2567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567 prefixEnd_2567 := by exact prefixLift 2567
  have htrace : WordTrace (prefixWord ++ tailWord_2567) baseStart_2567 baseEnd_2567 := by
    simpa [prefixWord, tailWord_2567, baseEnd_2567] using wordTrace_append hprefix tailTrace_2567
  have hstable : (prefixWord ++ tailWord_2567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567).length < 2 ^ (prefixWord ++ tailWord_2567).sum := by decide
  have hdescent : baseEnd_2567 < baseStart_2567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2580 : List Nat := [2, 4, 3, 1, 1, 2, 1, 2, 2, 5]
def baseStart_2580 : Nat := 118140960795 + 2580 * 2 ^ 59
def prefixEnd_2580 : Nat := 4983230072969 + 3 ^ 40 * 2580 * 2
def baseEnd_2580 : Nat := 441593362901713146047

theorem tailTrace_2580 : CollatzResearch.WordTrace tailWord_2580 prefixEnd_2580 441593362901713146047 := by
  unfold tailWord_2580
  simp only [CollatzResearch.WordTrace]
  refine ⟨47050165330287737014597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62733553773716982686129 47050165330287737014597)
  ·
    refine ⟨8821905999428950690237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47050165330287737014597 8821905999428950690237)
    ·
      refine ⟨3308214749785856508839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8821905999428950690237 3308214749785856508839)
      ·
        refine ⟨4962322124678784763259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3308214749785856508839 4962322124678784763259)
        ·
          refine ⟨7443483187018177144889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4962322124678784763259 7443483187018177144889)
          ·
            refine ⟨5582612390263632858667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7443483187018177144889 5582612390263632858667)
            ·
              refine ⟨8373918585395449288001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5582612390263632858667 8373918585395449288001)
              ·
                refine ⟨6280438939046586966001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8373918585395449288001 6280438939046586966001)
                ·
                  refine ⟨4710329204284940224501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6280438939046586966001 4710329204284940224501)
                  ·
                    refine ⟨441593362901713146047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4710329204284940224501 441593362901713146047)
                    ·
                      rfl

theorem cell23_2580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_2580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2580 prefixEnd_2580 := by exact prefixLift 2580
  have htrace : WordTrace (prefixWord ++ tailWord_2580) baseStart_2580 baseEnd_2580 := by
    simpa [prefixWord, tailWord_2580, baseEnd_2580] using wordTrace_append hprefix tailTrace_2580
  have hstable : (prefixWord ++ tailWord_2580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2580).length < 2 ^ (prefixWord ++ tailWord_2580).sum := by decide
  have hdescent : baseEnd_2580 < baseStart_2580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620 : List Nat := [2, 2, 2, 2, 3, 2, 2, 1, 2, 2, 3]
def baseStart_2620 : Nat := 118140960795 + 2620 * 2 ^ 59
def prefixEnd_2620 : Nat := 4983230072969 + 3 ^ 40 * 2620 * 2
def baseEnd_2620 : Nat := 1345319314884982937957

theorem tailTrace_2620 : CollatzResearch.WordTrace tailWord_2620 prefixEnd_2620 1345319314884982937957 := by
  unfold tailWord_2620
  simp only [CollatzResearch.WordTrace]
  refine ⟨47779625257831152742657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63706167010441536990209 47779625257831152742657)
  ·
    refine ⟨35834718943373364556993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47779625257831152742657 35834718943373364556993)
    ·
      refine ⟨26876039207530023417745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35834718943373364556993 26876039207530023417745)
      ·
        refine ⟨20157029405647517563309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26876039207530023417745 20157029405647517563309)
        ·
          refine ⟨7558886027117819086241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20157029405647517563309 7558886027117819086241)
          ·
            refine ⟨5669164520338364314681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7558886027117819086241 5669164520338364314681)
            ·
              refine ⟨4251873390253773236011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5669164520338364314681 4251873390253773236011)
              ·
                refine ⟨6377810085380659854017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4251873390253773236011 6377810085380659854017)
                ·
                  refine ⟨4783357564035494890513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6377810085380659854017 4783357564035494890513)
                  ·
                    refine ⟨3587518173026621167885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4783357564035494890513 3587518173026621167885)
                    ·
                      refine ⟨1345319314884982937957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3587518173026621167885 1345319314884982937957)
                      ·
                        rfl

theorem cell23_2620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_2620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620 prefixEnd_2620 := by exact prefixLift 2620
  have htrace : WordTrace (prefixWord ++ tailWord_2620) baseStart_2620 baseEnd_2620 := by
    simpa [prefixWord, tailWord_2620, baseEnd_2620] using wordTrace_append hprefix tailTrace_2620
  have hstable : (prefixWord ++ tailWord_2620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620).length < 2 ^ (prefixWord ++ tailWord_2620).sum := by decide
  have hdescent : baseEnd_2620 < baseStart_2620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644 : List Nat := [2, 4, 1, 1, 1, 5, 2, 2, 1, 4]
def baseStart_2644 : Nat := 118140960795 + 2644 * 2 ^ 59
def prefixEnd_2644 : Nat := 4983230072969 + 3 ^ 40 * 2644 * 2
def baseEnd_2644 : Nat := 452547616864296345949

theorem tailTrace_2644 : CollatzResearch.WordTrace tailWord_2644 prefixEnd_2644 452547616864296345949 := by
  unfold tailWord_2644
  simp only [CollatzResearch.WordTrace]
  refine ⟨48217301214357202179493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64289734952476269572657 48217301214357202179493)
  ·
    refine ⟨9040743977691975408655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48217301214357202179493 9040743977691975408655)
    ·
      refine ⟨13561115966537963112983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9040743977691975408655 13561115966537963112983)
      ·
        refine ⟨20341673949806944669475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13561115966537963112983 20341673949806944669475)
        ·
          refine ⟨30512510924710417004213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20341673949806944669475 30512510924710417004213)
          ·
            refine ⟨2860547899191601594145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30512510924710417004213 2860547899191601594145)
            ·
              refine ⟨2145410924393701195609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2860547899191601594145 2145410924393701195609)
              ·
                refine ⟨1609058193295275896707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2145410924393701195609 1609058193295275896707)
                ·
                  refine ⟨2413587289942913845061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1609058193295275896707 2413587289942913845061)
                  ·
                    refine ⟨452547616864296345949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2413587289942913845061 452547616864296345949)
                    ·
                      rfl

theorem cell23_2644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_2644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644 prefixEnd_2644 := by exact prefixLift 2644
  have htrace : WordTrace (prefixWord ++ tailWord_2644) baseStart_2644 baseEnd_2644 := by
    simpa [prefixWord, tailWord_2644, baseEnd_2644] using wordTrace_append hprefix tailTrace_2644
  have hstable : (prefixWord ++ tailWord_2644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644).length < 2 ^ (prefixWord ++ tailWord_2644).sum := by decide
  have hdescent : baseEnd_2644 < baseStart_2644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 1, 5, 2]
def baseStart_2677 : Nat := 118140960795 + 2677 * 2 ^ 59
def prefixEnd_2677 : Nat := 4983230072969 + 3 ^ 40 * 2677 * 2
def baseEnd_2677 : Nat := 1374587712191259925195

theorem tailTrace_2677 : CollatzResearch.WordTrace tailWord_2677 prefixEnd_2677 1374587712191259925195 := by
  unfold tailWord_2677
  simp only [CollatzResearch.WordTrace]
  refine ⟨97638211309161040310285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65092140872774026873523 97638211309161040310285)
  ·
    refine ⟨36614329240935390116357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97638211309161040310285 36614329240935390116357)
    ·
      refine ⟨6865186732675385646817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36614329240935390116357 6865186732675385646817)
      ·
        refine ⟨5148890049506539235113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6865186732675385646817 5148890049506539235113)
        ·
          refine ⟨3861667537129904426335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5148890049506539235113 3861667537129904426335)
          ·
            refine ⟨5792501305694856639503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3861667537129904426335 5792501305694856639503)
            ·
              refine ⟨8688751958542284959255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5792501305694856639503 8688751958542284959255)
              ·
                refine ⟨13033127937813427438883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8688751958542284959255 13033127937813427438883)
                ·
                  refine ⟨19549691906720141158325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13033127937813427438883 19549691906720141158325)
                  ·
                    refine ⟨1832783616255013233593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19549691906720141158325 1832783616255013233593)
                    ·
                      refine ⟨1374587712191259925195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1832783616255013233593 1374587712191259925195)
                      ·
                        rfl

theorem cell23_2677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_2677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2677 prefixEnd_2677 := by exact prefixLift 2677
  have htrace : WordTrace (prefixWord ++ tailWord_2677) baseStart_2677 baseEnd_2677 := by
    simpa [prefixWord, tailWord_2677, baseEnd_2677] using wordTrace_append hprefix tailTrace_2677
  have hstable : (prefixWord ++ tailWord_2677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677).length < 2 ^ (prefixWord ++ tailWord_2677).sum := by decide
  have hdescent : baseEnd_2677 < baseStart_2677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723 : List Nat := [1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 3]
def baseStart_2723 : Nat := 118140960795 + 2723 * 2 ^ 59
def prefixEnd_2723 : Nat := 4983230072969 + 3 ^ 40 * 2723 * 2
def baseEnd_2723 : Nat := 1398207822298079949983

theorem tailTrace_2723 : CollatzResearch.WordTrace tailWord_2723 prefixEnd_2723 1398207822298079949983 := by
  unfold tailWord_2723
  simp only [CollatzResearch.WordTrace]
  refine ⟨99315969142510896484823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66210646095007264323215 99315969142510896484823)
  ·
    refine ⟨148973953713766344727235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99315969142510896484823 148973953713766344727235)
    ·
      refine ⟨223460930570649517090853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148973953713766344727235 223460930570649517090853)
      ·
        refine ⟨41898924481996784454535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 223460930570649517090853 41898924481996784454535)
        ·
          refine ⟨62848386722995176681803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41898924481996784454535 62848386722995176681803)
          ·
            refine ⟨94272580084492765022705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62848386722995176681803 94272580084492765022705)
            ·
              refine ⟨70704435063369573767029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94272580084492765022705 70704435063369573767029)
              ·
                refine ⟨6628540787190897540659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70704435063369573767029 6628540787190897540659)
                ·
                  refine ⟨9942811180786346310989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6628540787190897540659 9942811180786346310989)
                  ·
                    refine ⟨3728554192794879866621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9942811180786346310989 3728554192794879866621)
                    ·
                      refine ⟨1398207822298079949983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3728554192794879866621 1398207822298079949983)
                      ·
                        rfl

theorem cell23_2723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_2723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723 prefixEnd_2723 := by exact prefixLift 2723
  have htrace : WordTrace (prefixWord ++ tailWord_2723) baseStart_2723 baseEnd_2723 := by
    simpa [prefixWord, tailWord_2723, baseEnd_2723] using wordTrace_append hprefix tailTrace_2723
  have hstable : (prefixWord ++ tailWord_2723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723).length < 2 ^ (prefixWord ++ tailWord_2723).sum := by decide
  have hdescent : baseEnd_2723 < baseStart_2723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741 : List Nat := [1, 3, 3, 3, 1, 1, 3, 3, 1, 2, 2]
def baseStart_2741 : Nat := 118140960795 + 2741 * 2 ^ 59
def prefixEnd_2741 : Nat := 4983230072969 + 3 ^ 40 * 2741 * 2
def baseEnd_2741 : Nat := 1407450474079009524901

theorem tailTrace_2741 : CollatzResearch.WordTrace tailWord_2741 prefixEnd_2741 1407450474079009524901 := by
  unfold tailWord_2741
  simp only [CollatzResearch.WordTrace]
  refine ⟨99972483077299970640077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66648322051533313760051 99972483077299970640077)
  ·
    refine ⟨37489681153987488990029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99972483077299970640077 37489681153987488990029)
    ·
      refine ⟨14058630432745308371261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37489681153987488990029 14058630432745308371261)
      ·
        refine ⟨5271986412279490639223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14058630432745308371261 5271986412279490639223)
        ·
          refine ⟨7907979618419235958835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5271986412279490639223 7907979618419235958835)
          ·
            refine ⟨11861969427628853938253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7907979618419235958835 11861969427628853938253)
            ·
              refine ⟨4448238535360820226845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11861969427628853938253 4448238535360820226845)
              ·
                refine ⟨1668089450760307585067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4448238535360820226845 1668089450760307585067)
                ·
                  refine ⟨2502134176140461377601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1668089450760307585067 2502134176140461377601)
                  ·
                    refine ⟨1876600632105346033201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2502134176140461377601 1876600632105346033201)
                    ·
                      refine ⟨1407450474079009524901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1876600632105346033201 1407450474079009524901)
                      ·
                        rfl

theorem cell23_2741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_2741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2741 prefixEnd_2741 := by exact prefixLift 2741
  have htrace : WordTrace (prefixWord ++ tailWord_2741) baseStart_2741 baseEnd_2741 := by
    simpa [prefixWord, tailWord_2741, baseEnd_2741] using wordTrace_append hprefix tailTrace_2741
  have hstable : (prefixWord ++ tailWord_2741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741).length < 2 ^ (prefixWord ++ tailWord_2741).sum := by decide
  have hdescent : baseEnd_2741 < baseStart_2741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 5]
def baseStart_2783 : Nat := 118140960795 + 2783 * 2 ^ 59
def prefixEnd_2783 : Nat := 4983230072969 + 3 ^ 40 * 2783 * 2
def baseEnd_2783 : Nat := 1429016661567845199707

theorem tailTrace_2783 : CollatzResearch.WordTrace tailWord_2783 prefixEnd_2783 1429016661567845199707 := by
  unfold tailWord_2783
  simp only [CollatzResearch.WordTrace]
  refine ⟨101504348925141143669003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67669565950094095779335 101504348925141143669003)
  ·
    refine ⟨152256523387711715503505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101504348925141143669003 152256523387711715503505)
    ·
      refine ⟨114192392540783786627629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152256523387711715503505 114192392540783786627629)
      ·
        refine ⟨42822147202793919985361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114192392540783786627629 42822147202793919985361)
        ·
          refine ⟨32116610402095439989021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42822147202793919985361 32116610402095439989021)
          ·
            refine ⟨12043728900785789995883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32116610402095439989021 12043728900785789995883)
            ·
              refine ⟨18065593351178684993825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12043728900785789995883 18065593351178684993825)
              ·
                refine ⟨13549195013384013745369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18065593351178684993825 13549195013384013745369)
                ·
                  refine ⟨10161896260038010309027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13549195013384013745369 10161896260038010309027)
                  ·
                    refine ⟨15242844390057015463541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10161896260038010309027 15242844390057015463541)
                    ·
                      refine ⟨1429016661567845199707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15242844390057015463541 1429016661567845199707)
                      ·
                        rfl

theorem cell23_2783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_2783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783 prefixEnd_2783 := by exact prefixLift 2783
  have htrace : WordTrace (prefixWord ++ tailWord_2783) baseStart_2783 baseEnd_2783 := by
    simpa [prefixWord, tailWord_2783, baseEnd_2783] using wordTrace_append hprefix tailTrace_2783
  have hstable : (prefixWord ++ tailWord_2783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783).length < 2 ^ (prefixWord ++ tailWord_2783).sum := by decide
  have hdescent : baseEnd_2783 < baseStart_2783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797 : List Nat := [1, 5, 1, 2, 1, 1, 3, 2, 1, 4, 2]
def baseStart_2797 : Nat := 118140960795 + 2797 * 2 ^ 59
def prefixEnd_2797 : Nat := 4983230072969 + 3 ^ 40 * 2797 * 2
def baseEnd_2797 : Nat := 1436205390730790424643

theorem tailTrace_2797 : CollatzResearch.WordTrace tailWord_2797 prefixEnd_2797 1436205390730790424643 := by
  unfold tailWord_2797
  simp only [CollatzResearch.WordTrace]
  refine ⟨102014970874421534678645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68009980582947689785763 102014970874421534678645)
  ·
    refine ⟨9563903519477018876123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102014970874421534678645 9563903519477018876123)
    ·
      refine ⟨14345855279215528314185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9563903519477018876123 14345855279215528314185)
      ·
        refine ⟨10759391459411646235639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14345855279215528314185 10759391459411646235639)
        ·
          refine ⟨16139087189117469353459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10759391459411646235639 16139087189117469353459)
          ·
            refine ⟨24208630783676204030189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16139087189117469353459 24208630783676204030189)
            ·
              refine ⟨9078236543878576511321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24208630783676204030189 9078236543878576511321)
              ·
                refine ⟨6808677407908932383491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9078236543878576511321 6808677407908932383491)
                ·
                  refine ⟨10213016111863398575237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6808677407908932383491 10213016111863398575237)
                  ·
                    refine ⟨1914940520974387232857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10213016111863398575237 1914940520974387232857)
                    ·
                      refine ⟨1436205390730790424643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1914940520974387232857 1436205390730790424643)
                      ·
                        rfl

theorem cell23_2797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_2797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797 prefixEnd_2797 := by exact prefixLift 2797
  have htrace : WordTrace (prefixWord ++ tailWord_2797) baseStart_2797 baseEnd_2797 := by
    simpa [prefixWord, tailWord_2797, baseEnd_2797] using wordTrace_append hprefix tailTrace_2797
  have hstable : (prefixWord ++ tailWord_2797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797).length < 2 ^ (prefixWord ++ tailWord_2797).sum := by decide
  have hdescent : baseEnd_2797 < baseStart_2797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 4, 5]
def baseStart_2833 : Nat := 118140960795 + 2833 * 2 ^ 59
def prefixEnd_2833 : Nat := 4983230072969 + 3 ^ 40 * 2833 * 2
def baseEnd_2833 : Nat := 484896898097549858159

theorem tailTrace_2833 : CollatzResearch.WordTrace tailWord_2833 prefixEnd_2833 484896898097549858159 := by
  unfold tailWord_2833
  simp only [CollatzResearch.WordTrace]
  refine ⟨103327998743999682989153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68885332495999788659435 103327998743999682989153)
  ·
    refine ⟨77495999057999762241865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103327998743999682989153 77495999057999762241865)
    ·
      refine ⟨58121999293499821681399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77495999057999762241865 58121999293499821681399)
      ·
        refine ⟨87182998940249732522099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58121999293499821681399 87182998940249732522099)
        ·
          refine ⟨130774498410374598783149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87182998940249732522099 130774498410374598783149)
          ·
            refine ⟨49040436903890474543681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130774498410374598783149 49040436903890474543681)
            ·
              refine ⟨36780327677917855907761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49040436903890474543681 36780327677917855907761)
              ·
                refine ⟨27585245758438391930821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36780327677917855907761 27585245758438391930821)
                ·
                  refine ⟨5172233579707198487029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27585245758438391930821 5172233579707198487029)
                  ·
                    refine ⟨484896898097549858159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5172233579707198487029 484896898097549858159)
                    ·
                      rfl

theorem cell23_2833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_2833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2833 prefixEnd_2833 := by exact prefixLift 2833
  have htrace : WordTrace (prefixWord ++ tailWord_2833) baseStart_2833 baseEnd_2833 := by
    simpa [prefixWord, tailWord_2833, baseEnd_2833] using wordTrace_append hprefix tailTrace_2833
  have hstable : (prefixWord ++ tailWord_2833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833).length < 2 ^ (prefixWord ++ tailWord_2833).sum := by decide
  have hdescent : baseEnd_2833 < baseStart_2833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 4, 5, 2]
def baseStart_2840 : Nat := 118140960795 + 2840 * 2 ^ 59
def prefixEnd_2840 : Nat := 4983230072969 + 3 ^ 40 * 2840 * 2
def baseEnd_2840 : Nat := 1458285058874122186945

theorem tailTrace_2840 : CollatzResearch.WordTrace tailWord_2840 prefixEnd_2840 1458285058874122186945 := by
  unfold tailWord_2840
  simp only [CollatzResearch.WordTrace]
  refine ⟨51791654859319939246987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69055539812426585662649 51791654859319939246987)
  ·
    refine ⟨77687482288979908870481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51791654859319939246987 77687482288979908870481)
    ·
      refine ⟨58265611716734931652861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77687482288979908870481 58265611716734931652861)
      ·
        refine ⟨21849604393775599369823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58265611716734931652861 21849604393775599369823)
        ·
          refine ⟨32774406590663399054735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21849604393775599369823 32774406590663399054735)
          ·
            refine ⟨49161609885995098582103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32774406590663399054735 49161609885995098582103)
            ·
              refine ⟨73742414828992647873155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49161609885995098582103 73742414828992647873155)
              ·
                refine ⟨110613622243488971809733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73742414828992647873155 110613622243488971809733)
                ·
                  refine ⟨20740054170654182214325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110613622243488971809733 20740054170654182214325)
                  ·
                    refine ⟨1944380078498829582593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20740054170654182214325 1944380078498829582593)
                    ·
                      refine ⟨1458285058874122186945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1944380078498829582593 1458285058874122186945)
                      ·
                        rfl

theorem cell23_2840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_2840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840 prefixEnd_2840 := by exact prefixLift 2840
  have htrace : WordTrace (prefixWord ++ tailWord_2840) baseStart_2840 baseEnd_2840 := by
    simpa [prefixWord, tailWord_2840, baseEnd_2840] using wordTrace_append hprefix tailTrace_2840
  have hstable : (prefixWord ++ tailWord_2840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840).length < 2 ^ (prefixWord ++ tailWord_2840).sum := by decide
  have hdescent : baseEnd_2840 < baseStart_2840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 1, 7]
def baseStart_2850 : Nat := 118140960795 + 2850 * 2 ^ 59
def prefixEnd_2850 : Nat := 4983230072969 + 3 ^ 40 * 2850 * 2
def baseEnd_2850 : Nat := 487806621806361020633

theorem tailTrace_2850 : CollatzResearch.WordTrace tailWord_2850 prefixEnd_2850 487806621806361020633 := by
  unfold tailWord_2850
  simp only [CollatzResearch.WordTrace]
  refine ⟨25987009920602896589501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69298693121607724238669 25987009920602896589501)
  ·
    refine ⟨9745128720226086221063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25987009920602896589501 9745128720226086221063)
    ·
      refine ⟨14617693080339129331595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9745128720226086221063 14617693080339129331595)
      ·
        refine ⟨21926539620508693997393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14617693080339129331595 21926539620508693997393)
        ·
          refine ⟨16444904715381520498045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21926539620508693997393 16444904715381520498045)
          ·
            refine ⟨6166839268268070186767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16444904715381520498045 6166839268268070186767)
            ·
              refine ⟨9250258902402105280151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6166839268268070186767 9250258902402105280151)
              ·
                refine ⟨13875388353603157920227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9250258902402105280151 13875388353603157920227)
                ·
                  refine ⟨20813082530404736880341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13875388353603157920227 20813082530404736880341)
                  ·
                    refine ⟨487806621806361020633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20813082530404736880341 487806621806361020633)
                    ·
                      rfl

theorem cell23_2850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_2850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850 prefixEnd_2850 := by exact prefixLift 2850
  have htrace : WordTrace (prefixWord ++ tailWord_2850) baseStart_2850 baseEnd_2850 := by
    simpa [prefixWord, tailWord_2850, baseEnd_2850] using wordTrace_append hprefix tailTrace_2850
  have hstable : (prefixWord ++ tailWord_2850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850).length < 2 ^ (prefixWord ++ tailWord_2850).sum := by decide
  have hdescent : baseEnd_2850 < baseStart_2850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 6]
def baseStart_2883 : Nat := 118140960795 + 2883 * 2 ^ 59
def prefixEnd_2883 : Nat := 4983230072969 + 3 ^ 40 * 2883 * 2
def baseEnd_2883 : Nat := 1480364727017453949247

theorem tailTrace_2883 : CollatzResearch.WordTrace tailWord_2883 prefixEnd_2883 1480364727017453949247 := by
  unfold tailWord_2883
  simp only [CollatzResearch.WordTrace]
  refine ⟨105151648562858222309303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70101099041905481539535 105151648562858222309303)
  ·
    refine ⟨157727472844287333463955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105151648562858222309303 157727472844287333463955)
    ·
      refine ⟨236591209266431000195933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157727472844287333463955 236591209266431000195933)
      ·
        refine ⟨88721703474911625073475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236591209266431000195933 88721703474911625073475)
        ·
          refine ⟨133082555212367437610213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88721703474911625073475 133082555212367437610213)
          ·
            refine ⟨24952979102318894551915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133082555212367437610213 24952979102318894551915)
            ·
              refine ⟨37429468653478341827873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24952979102318894551915 37429468653478341827873)
              ·
                refine ⟨28072101490108756370905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37429468653478341827873 28072101490108756370905)
                ·
                  refine ⟨21054076117581567278179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28072101490108756370905 21054076117581567278179)
                  ·
                    refine ⟨31581114176372350917269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21054076117581567278179 31581114176372350917269)
                    ·
                      refine ⟨1480364727017453949247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31581114176372350917269 1480364727017453949247)
                      ·
                        rfl

theorem cell23_2883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_2883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883 prefixEnd_2883 := by exact prefixLift 2883
  have htrace : WordTrace (prefixWord ++ tailWord_2883) baseStart_2883 baseEnd_2883 := by
    simpa [prefixWord, tailWord_2883, baseEnd_2883] using wordTrace_append hprefix tailTrace_2883
  have hstable : (prefixWord ++ tailWord_2883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883).length < 2 ^ (prefixWord ++ tailWord_2883).sum := by decide
  have hdescent : baseEnd_2883 < baseStart_2883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 6, 2, 3]
def baseStart_2890 : Nat := 118140960795 + 2890 * 2 ^ 59
def prefixEnd_2890 : Nat := 4983230072969 + 3 ^ 40 * 2890 * 2
def baseEnd_2890 : Nat := 1483959091598926561715

theorem tailTrace_2890 : CollatzResearch.WordTrace tailWord_2890 prefixEnd_2890 1483959091598926561715 := by
  unfold tailWord_2890
  simp only [CollatzResearch.WordTrace]
  refine ⟨26351739884374604453531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70271306358332278542749 26351739884374604453531)
  ·
    refine ⟨39527609826561906680297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26351739884374604453531 39527609826561906680297)
    ·
      refine ⟨29645707369921430010223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39527609826561906680297 29645707369921430010223)
      ·
        refine ⟨44468561054882145015335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29645707369921430010223 44468561054882145015335)
        ·
          refine ⟨66702841582323217523003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44468561054882145015335 66702841582323217523003)
          ·
            refine ⟨100054262373484826284505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66702841582323217523003 100054262373484826284505)
            ·
              refine ⟨75040696780113619713379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100054262373484826284505 75040696780113619713379)
              ·
                refine ⟨112561045170170429570069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75040696780113619713379 112561045170170429570069)
                ·
                  refine ⟨5276298992351738886097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 112561045170170429570069 5276298992351738886097)
                  ·
                    refine ⟨3957224244263804164573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5276298992351738886097 3957224244263804164573)
                    ·
                      refine ⟨1483959091598926561715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3957224244263804164573 1483959091598926561715)
                      ·
                        rfl

theorem cell23_2890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_2890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890 prefixEnd_2890 := by exact prefixLift 2890
  have htrace : WordTrace (prefixWord ++ tailWord_2890) baseStart_2890 baseEnd_2890 := by
    simpa [prefixWord, tailWord_2890, baseEnd_2890] using wordTrace_append hprefix tailTrace_2890
  have hstable : (prefixWord ++ tailWord_2890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890).length < 2 ^ (prefixWord ++ tailWord_2890).sum := by decide
  have hdescent : baseEnd_2890 < baseStart_2890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 1, 1, 8]
def baseStart_2913 : Nat := 118140960795 + 2913 * 2 ^ 59
def prefixEnd_2913 : Nat := 4983230072969 + 3 ^ 40 * 2913 * 2
def baseEnd_2913 : Nat := 1495769146652336574109

theorem tailTrace_2913 : CollatzResearch.WordTrace tailWord_2913 prefixEnd_2913 1495769146652336574109 := by
  unfold tailWord_2913
  simp only [CollatzResearch.WordTrace]
  refine ⟨106245838454173345901393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70830558969448897267595 106245838454173345901393)
  ·
    refine ⟨79684378840630009426045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106245838454173345901393 79684378840630009426045)
    ·
      refine ⟨29881642065236253534767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79684378840630009426045 29881642065236253534767)
      ·
        refine ⟨44822463097854380302151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29881642065236253534767 44822463097854380302151)
        ·
          refine ⟨67233694646781570453227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44822463097854380302151 67233694646781570453227)
          ·
            refine ⟨100850541970172355679841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67233694646781570453227 100850541970172355679841)
            ·
              refine ⟨75637906477629266759881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100850541970172355679841 75637906477629266759881)
              ·
                refine ⟨56728429858221950069911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75637906477629266759881 56728429858221950069911)
                ·
                  refine ⟨85092644787332925104867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56728429858221950069911 85092644787332925104867)
                  ·
                    refine ⟨127638967180999387657301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85092644787332925104867 127638967180999387657301)
                    ·
                      refine ⟨1495769146652336574109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 127638967180999387657301 1495769146652336574109)
                      ·
                        rfl

theorem cell23_2913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_2913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2913 prefixEnd_2913 := by exact prefixLift 2913
  have htrace : WordTrace (prefixWord ++ tailWord_2913) baseStart_2913 baseEnd_2913 := by
    simpa [prefixWord, tailWord_2913, baseEnd_2913] using wordTrace_append hprefix tailTrace_2913
  have hstable : (prefixWord ++ tailWord_2913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913).length < 2 ^ (prefixWord ++ tailWord_2913).sum := by decide
  have hdescent : baseEnd_2913 < baseStart_2913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 4, 3, 2]
def baseStart_2947 : Nat := 118140960795 + 2947 * 2 ^ 59
def prefixEnd_2947 : Nat := 4983230072969 + 3 ^ 40 * 2947 * 2
def baseEnd_2947 : Nat := 1513227488905203548953

theorem tailTrace_2947 : CollatzResearch.WordTrace tailWord_2947 prefixEnd_2947 1513227488905203548953 := by
  unfold tailWord_2947
  simp only [CollatzResearch.WordTrace]
  refine ⟨107485920330997152639095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71657280220664768426063 107485920330997152639095)
  ·
    refine ⟨161228880496495728958643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107485920330997152639095 161228880496495728958643)
    ·
      refine ⟨241843320744743593437965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161228880496495728958643 241843320744743593437965)
      ·
        refine ⟨90691245279278847539237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241843320744743593437965 90691245279278847539237)
        ·
          refine ⟨17004608489864783913607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90691245279278847539237 17004608489864783913607)
          ·
            refine ⟨25506912734797175870411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17004608489864783913607 25506912734797175870411)
            ·
              refine ⟨38260369102195763805617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25506912734797175870411 38260369102195763805617)
              ·
                refine ⟨28695276826646822854213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38260369102195763805617 28695276826646822854213)
                ·
                  refine ⟨5380364404996279285165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28695276826646822854213 5380364404996279285165)
                  ·
                    refine ⟨2017636651873604731937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5380364404996279285165 2017636651873604731937)
                    ·
                      refine ⟨1513227488905203548953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2017636651873604731937 1513227488905203548953)
                      ·
                        rfl

theorem cell23_2947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 3, 2].length) (baseStart_2947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947 prefixEnd_2947 := by exact prefixLift 2947
  have htrace : WordTrace (prefixWord ++ tailWord_2947) baseStart_2947 baseEnd_2947 := by
    simpa [prefixWord, tailWord_2947, baseEnd_2947] using wordTrace_append hprefix tailTrace_2947
  have hstable : (prefixWord ++ tailWord_2947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947).length < 2 ^ (prefixWord ++ tailWord_2947).sum := by decide
  have hdescent : baseEnd_2947 < baseStart_2947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 5, 2, 3]
def baseStart_2997 : Nat := 118140960795 + 2997 * 2 ^ 59
def prefixEnd_2997 : Nat := 4983230072969 + 3 ^ 40 * 2997 * 2
def baseEnd_2997 : Nat := 1538901521630007923723

theorem tailTrace_2997 : CollatzResearch.WordTrace tailWord_2997 prefixEnd_2997 1538901521630007923723 := by
  unfold tailWord_2997
  simp only [CollatzResearch.WordTrace]
  refine ⟨109309570149855691959245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72873046766570461306163 109309570149855691959245)
  ·
    refine ⟨40991088806195884484717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109309570149855691959245 40991088806195884484717)
    ·
      refine ⟨15371658302323456681769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40991088806195884484717 15371658302323456681769)
      ·
        refine ⟨11528743726742592511327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15371658302323456681769 11528743726742592511327)
        ·
          refine ⟨17293115590113888766991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11528743726742592511327 17293115590113888766991)
          ·
            refine ⟨25939673385170833150487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17293115590113888766991 25939673385170833150487)
            ·
              refine ⟨38909510077756249725731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25939673385170833150487 38909510077756249725731)
              ·
                refine ⟨58364265116634374588597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38909510077756249725731 58364265116634374588597)
                ·
                  refine ⟨5471649854684472617681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58364265116634374588597 5471649854684472617681)
                  ·
                    refine ⟨4103737391013354463261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5471649854684472617681 4103737391013354463261)
                    ·
                      refine ⟨1538901521630007923723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4103737391013354463261 1538901521630007923723)
                      ·
                        rfl

theorem cell23_2997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_2997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997 prefixEnd_2997 := by exact prefixLift 2997
  have htrace : WordTrace (prefixWord ++ tailWord_2997) baseStart_2997 baseEnd_2997 := by
    simpa [prefixWord, tailWord_2997, baseEnd_2997] using wordTrace_append hprefix tailTrace_2997
  have hstable : (prefixWord ++ tailWord_2997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997).length < 2 ^ (prefixWord ++ tailWord_2997).sum := by decide
  have hdescent : baseEnd_2997 < baseStart_2997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000 : List Nat := [2, 1, 2, 1, 2, 4, 3, 8]
def baseStart_3000 : Nat := 118140960795 + 3000 * 2 ^ 59
def prefixEnd_3000 : Nat := 4983230072969 + 3 ^ 40 * 3000 * 2
def baseEnd_3000 : Nat := 57053406059018377267

theorem tailTrace_3000 : CollatzResearch.WordTrace tailWord_3000 prefixEnd_3000 57053406059018377267 := by
  unfold tailWord_3000
  simp only [CollatzResearch.WordTrace]
  refine ⟨54709494569493602159227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72945992759324802878969 54709494569493602159227)
  ·
    refine ⟨82064241854240403238841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54709494569493602159227 82064241854240403238841)
    ·
      refine ⟨61548181390680302429131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82064241854240403238841 61548181390680302429131)
      ·
        refine ⟨92322272086020453643697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61548181390680302429131 92322272086020453643697)
        ·
          refine ⟨69241704064515340232773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92322272086020453643697 69241704064515340232773)
          ·
            refine ⟨12982819512096626293645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69241704064515340232773 12982819512096626293645)
            ·
              refine ⟨4868557317036234860117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12982819512096626293645 4868557317036234860117)
              ·
                refine ⟨57053406059018377267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4868557317036234860117 57053406059018377267)
                ·
                  rfl

theorem cell23_3000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 8].length) (baseStart_3000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000 prefixEnd_3000 := by exact prefixLift 3000
  have htrace : WordTrace (prefixWord ++ tailWord_3000) baseStart_3000 baseEnd_3000 := by
    simpa [prefixWord, tailWord_3000, baseEnd_3000] using wordTrace_append hprefix tailTrace_3000
  have hstable : (prefixWord ++ tailWord_3000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000).length < 2 ^ (prefixWord ++ tailWord_3000).sum := by decide
  have hdescent : baseEnd_3000 < baseStart_3000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028 : List Nat := [2, 4, 1, 2, 1, 2, 1, 5, 1, 2, 2]
def baseStart_3028 : Nat := 118140960795 + 3028 * 2 ^ 59
def prefixEnd_3028 : Nat := 4983230072969 + 3 ^ 40 * 3028 * 2
def baseEnd_3028 : Nat := 1554819421919386636081

theorem tailTrace_3028 : CollatzResearch.WordTrace tailWord_3028 prefixEnd_3028 1554819421919386636081 := by
  unfold tailWord_3028
  simp only [CollatzResearch.WordTrace]
  refine ⟨55220116518773993168869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73626822025031990891825 55220116518773993168869)
  ·
    refine ⟨10353771847270123719163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55220116518773993168869 10353771847270123719163)
    ·
      refine ⟨15530657770905185578745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10353771847270123719163 15530657770905185578745)
      ·
        refine ⟨11647993328178889184059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15530657770905185578745 11647993328178889184059)
        ·
          refine ⟨17471989992268333776089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11647993328178889184059 17471989992268333776089)
          ·
            refine ⟨13103992494201250332067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17471989992268333776089 13103992494201250332067)
            ·
              refine ⟨19655988741301875498101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13103992494201250332067 19655988741301875498101)
              ·
                refine ⟨1842748944497050827947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19655988741301875498101 1842748944497050827947)
                ·
                  refine ⟨2764123416745576241921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1842748944497050827947 2764123416745576241921)
                  ·
                    refine ⟨2073092562559182181441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2764123416745576241921 2073092562559182181441)
                    ·
                      refine ⟨1554819421919386636081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2073092562559182181441 1554819421919386636081)
                      ·
                        rfl

theorem cell23_3028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_3028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028 prefixEnd_3028 := by exact prefixLift 3028
  have htrace : WordTrace (prefixWord ++ tailWord_3028) baseStart_3028 baseEnd_3028 := by
    simpa [prefixWord, tailWord_3028, baseEnd_3028] using wordTrace_append hprefix tailTrace_3028
  have hstable : (prefixWord ++ tailWord_3028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028).length < 2 ^ (prefixWord ++ tailWord_3028).sum := by decide
  have hdescent : baseEnd_3028 < baseStart_3028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044 : List Nat := [2, 3, 1, 1, 1, 1, 2, 6, 2, 1, 3]
def baseStart_3044 : Nat := 118140960795 + 3044 * 2 ^ 59
def prefixEnd_3044 : Nat := 4983230072969 + 3 ^ 40 * 3044 * 2
def baseEnd_3044 : Nat := 1563035112391324036007

theorem tailTrace_3044 : CollatzResearch.WordTrace tailWord_3044 prefixEnd_3044 1563035112391324036007 := by
  unfold tailWord_3044
  simp only [CollatzResearch.WordTrace]
  refine ⟨55511900489791359460093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74015867319721812613457 55511900489791359460093)
  ·
    refine ⟨20816962683671759797535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55511900489791359460093 20816962683671759797535)
    ·
      refine ⟨31225444025507639696303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20816962683671759797535 31225444025507639696303)
      ·
        refine ⟨46838166038261459544455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31225444025507639696303 46838166038261459544455)
        ·
          refine ⟨70257249057392189316683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46838166038261459544455 70257249057392189316683)
          ·
            refine ⟨105385873586088283975025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70257249057392189316683 105385873586088283975025)
            ·
              refine ⟨79039405189566212981269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105385873586088283975025 79039405189566212981269)
              ·
                refine ⟨3704972118260916233497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79039405189566212981269 3704972118260916233497)
                ·
                  refine ⟨2778729088695687175123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3704972118260916233497 2778729088695687175123)
                  ·
                    refine ⟨4168093633043530762685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2778729088695687175123 4168093633043530762685)
                    ·
                      refine ⟨1563035112391324036007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4168093633043530762685 1563035112391324036007)
                      ·
                        rfl

theorem cell23_3044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_3044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3044 prefixEnd_3044 := by exact prefixLift 3044
  have htrace : WordTrace (prefixWord ++ tailWord_3044) baseStart_3044 baseEnd_3044 := by
    simpa [prefixWord, tailWord_3044, baseEnd_3044] using wordTrace_append hprefix tailTrace_3044
  have hstable : (prefixWord ++ tailWord_3044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044).length < 2 ^ (prefixWord ++ tailWord_3044).sum := by decide
  have hdescent : baseEnd_3044 < baseStart_3044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058 : List Nat := [3, 2, 1, 5, 2, 1, 1, 1, 1, 2, 4]
def baseStart_3058 : Nat := 118140960795 + 3058 * 2 ^ 59
def prefixEnd_3058 : Nat := 4983230072969 + 3 ^ 40 * 3058 * 2
def baseEnd_3058 : Nat := 1570223841554269260943

theorem tailTrace_3058 : CollatzResearch.WordTrace tailWord_3058 prefixEnd_3058 1570223841554269260943 := by
  unfold tailWord_3058
  simp only [CollatzResearch.WordTrace]
  refine ⟨27883605732215777482457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74356281952575406619885 27883605732215777482457)
  ·
    refine ⟨20912704299161833111843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27883605732215777482457 20912704299161833111843)
    ·
      refine ⟨31369056448742749667765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20912704299161833111843 31369056448742749667765)
      ·
        refine ⟨2940849042069632781353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31369056448742749667765 2940849042069632781353)
        ·
          refine ⟨2205636781552224586015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2940849042069632781353 2205636781552224586015)
          ·
            refine ⟨3308455172328336879023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2205636781552224586015 3308455172328336879023)
            ·
              refine ⟨4962682758492505318535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3308455172328336879023 4962682758492505318535)
              ·
                refine ⟨7444024137738757977803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4962682758492505318535 7444024137738757977803)
                ·
                  refine ⟨11166036206608136966705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7444024137738757977803 11166036206608136966705)
                  ·
                    refine ⟨8374527154956102725029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11166036206608136966705 8374527154956102725029)
                    ·
                      refine ⟨1570223841554269260943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8374527154956102725029 1570223841554269260943)
                      ·
                        rfl

theorem cell23_3058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_3058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058 prefixEnd_3058 := by exact prefixLift 3058
  have htrace : WordTrace (prefixWord ++ tailWord_3058) baseStart_3058 baseEnd_3058 := by
    simpa [prefixWord, tailWord_3058, baseEnd_3058] using wordTrace_append hprefix tailTrace_3058
  have hstable : (prefixWord ++ tailWord_3058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058).length < 2 ^ (prefixWord ++ tailWord_3058).sum := by decide
  have hdescent : baseEnd_3058 < baseStart_3058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107 : List Nat := [1, 1, 1, 4, 3, 2, 3, 1, 7]
def baseStart_3107 : Nat := 118140960795 + 3107 * 2 ^ 59
def prefixEnd_3107 : Nat := 4983230072969 + 3 ^ 40 * 3107 * 2
def baseEnd_3107 : Nat := 177264932624953060913

theorem tailTrace_3107 : CollatzResearch.WordTrace tailWord_3107 prefixEnd_3107 177264932624953060913 := by
  unfold tailWord_3107
  simp only [CollatzResearch.WordTrace]
  refine ⟨113321599751344478463575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75547733167562985642383 113321599751344478463575)
  ·
    refine ⟨169982399627016717695363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113321599751344478463575 169982399627016717695363)
    ·
      refine ⟨254973599440525076543045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169982399627016717695363 254973599440525076543045)
      ·
        refine ⟨47807549895098451851821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254973599440525076543045 47807549895098451851821)
        ·
          refine ⟨17927831210661919444433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47807549895098451851821 17927831210661919444433)
          ·
            refine ⟨13445873407996439583325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17927831210661919444433 13445873407996439583325)
            ·
              refine ⟨5042202527998664843747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13445873407996439583325 5042202527998664843747)
              ·
                refine ⟨7563303791997997265621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5042202527998664843747 7563303791997997265621)
                ·
                  refine ⟨177264932624953060913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7563303791997997265621 177264932624953060913)
                  ·
                    rfl

theorem cell23_3107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 7].length) (baseStart_3107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107 prefixEnd_3107 := by exact prefixLift 3107
  have htrace : WordTrace (prefixWord ++ tailWord_3107) baseStart_3107 baseEnd_3107 := by
    simpa [prefixWord, tailWord_3107, baseEnd_3107] using wordTrace_append hprefix tailTrace_3107
  have hstable : (prefixWord ++ tailWord_3107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107).length < 2 ^ (prefixWord ++ tailWord_3107).sum := by decide
  have hdescent : baseEnd_3107 < baseStart_3107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118 : List Nat := [4, 1, 3, 1, 1, 1, 3, 3, 2, 2, 2]
def baseStart_3118 : Nat := 118140960795 + 3118 * 2 ^ 59
def prefixEnd_3118 : Nat := 4983230072969 + 3 ^ 40 * 3118 * 2
def baseEnd_3118 : Nat := 1601032680824034510667

theorem tailTrace_3118 : CollatzResearch.WordTrace tailWord_3118 prefixEnd_3118 1601032680824034510667 := by
  unfold tailWord_3118
  simp only [CollatzResearch.WordTrace]
  refine ⟨14215350338936669639251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75815201807662238076005 14215350338936669639251)
  ·
    refine ⟨21323025508405004458877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14215350338936669639251 21323025508405004458877)
    ·
      refine ⟨7996134565651876672079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21323025508405004458877 7996134565651876672079)
      ·
        refine ⟨11994201848477815008119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7996134565651876672079 11994201848477815008119)
        ·
          refine ⟨17991302772716722512179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11994201848477815008119 17991302772716722512179)
          ·
            refine ⟨26986954159075083768269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17991302772716722512179 26986954159075083768269)
            ·
              refine ⟨10120107809653156413101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26986954159075083768269 10120107809653156413101)
              ·
                refine ⟨3795040428619933654913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10120107809653156413101 3795040428619933654913)
                ·
                  refine ⟨2846280321464950241185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3795040428619933654913 2846280321464950241185)
                  ·
                    refine ⟨2134710241098712680889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2846280321464950241185 2134710241098712680889)
                    ·
                      refine ⟨1601032680824034510667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2134710241098712680889 1601032680824034510667)
                      ·
                        rfl

theorem cell23_3118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_3118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118 prefixEnd_3118 := by exact prefixLift 3118
  have htrace : WordTrace (prefixWord ++ tailWord_3118) baseStart_3118 baseEnd_3118 := by
    simpa [prefixWord, tailWord_3118, baseEnd_3118] using wordTrace_append hprefix tailTrace_3118
  have hstable : (prefixWord ++ tailWord_3118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118).length < 2 ^ (prefixWord ++ tailWord_3118).sum := by decide
  have hdescent : baseEnd_3118 < baseStart_3118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154 : List Nat := [3, 2, 2, 1, 3, 1, 2, 2, 2, 5]
def baseStart_3154 : Nat := 118140960795 + 3154 * 2 ^ 59
def prefixEnd_3154 : Nat := 4983230072969 + 3 ^ 40 * 3154 * 2
def baseEnd_3154 : Nat := 539839328128631220167

theorem tailTrace_3154 : CollatzResearch.WordTrace tailWord_3154 prefixEnd_3154 539839328128631220167 := by
  unfold tailWord_3154
  simp only [CollatzResearch.WordTrace]
  refine ⟨28758957645267876356129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76690553720714336949677 28758957645267876356129)
  ·
    refine ⟨21569218233950907267097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28758957645267876356129 21569218233950907267097)
    ·
      refine ⟨16176913675463180450323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21569218233950907267097 16176913675463180450323)
      ·
        refine ⟨24265370513194770675485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16176913675463180450323 24265370513194770675485)
        ·
          refine ⟨9099513942448039003307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24265370513194770675485 9099513942448039003307)
          ·
            refine ⟨13649270913672058504961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9099513942448039003307 13649270913672058504961)
            ·
              refine ⟨10236953185254043878721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13649270913672058504961 10236953185254043878721)
              ·
                refine ⟨7677714888940532909041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10236953185254043878721 7677714888940532909041)
                ·
                  refine ⟨5758286166705399681781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7677714888940532909041 5758286166705399681781)
                  ·
                    refine ⟨539839328128631220167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5758286166705399681781 539839328128631220167)
                    ·
                      rfl

theorem cell23_3154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_3154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154 prefixEnd_3154 := by exact prefixLift 3154
  have htrace : WordTrace (prefixWord ++ tailWord_3154) baseStart_3154 baseEnd_3154 := by
    simpa [prefixWord, tailWord_3154, baseEnd_3154] using wordTrace_append hprefix tailTrace_3154
  have hstable : (prefixWord ++ tailWord_3154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154).length < 2 ^ (prefixWord ++ tailWord_3154).sum := by decide
  have hdescent : baseEnd_3154 < baseStart_3154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184 : List Nat := [2, 1, 1, 1, 5, 1, 3, 2, 3, 4]
def baseStart_3184 : Nat := 118140960795 + 3184 * 2 ^ 59
def prefixEnd_3184 : Nat := 4983230072969 + 3 ^ 40 * 3184 * 2
def baseEnd_3184 : Nat := 544974134673592095121

theorem tailTrace_3184 : CollatzResearch.WordTrace tailWord_3184 prefixEnd_3184 544974134673592095121 := by
  unfold tailWord_3184
  simp only [CollatzResearch.WordTrace]
  refine ⟨58065010236193314508303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77420013648257752677737 58065010236193314508303)
  ·
    refine ⟨87097515354289971762455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58065010236193314508303 87097515354289971762455)
    ·
      refine ⟨130646273031434957643683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87097515354289971762455 130646273031434957643683)
      ·
        refine ⟨195969409547152436465525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130646273031434957643683 195969409547152436465525)
        ·
          refine ⟨18372132145045540918643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 195969409547152436465525 18372132145045540918643)
          ·
            refine ⟨27558198217568311377965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18372132145045540918643 27558198217568311377965)
            ·
              refine ⟨10334324331588116766737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27558198217568311377965 10334324331588116766737)
              ·
                refine ⟨7750743248691087575053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10334324331588116766737 7750743248691087575053)
                ·
                  refine ⟨2906528718259157840645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7750743248691087575053 2906528718259157840645)
                  ·
                    refine ⟨544974134673592095121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2906528718259157840645 544974134673592095121)
                    ·
                      rfl

theorem cell23_3184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 3, 4].length) (baseStart_3184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184 prefixEnd_3184 := by exact prefixLift 3184
  have htrace : WordTrace (prefixWord ++ tailWord_3184) baseStart_3184 baseEnd_3184 := by
    simpa [prefixWord, tailWord_3184, baseEnd_3184] using wordTrace_append hprefix tailTrace_3184
  have hstable : (prefixWord ++ tailWord_3184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184).length < 2 ^ (prefixWord ++ tailWord_3184).sum := by decide
  have hdescent : baseEnd_3184 < baseStart_3184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 8]
def baseStart_3197 : Nat := 118140960795 + 3197 * 2 ^ 59
def prefixEnd_3197 : Nat := 4983230072969 + 3 ^ 40 * 3197 * 2
def baseEnd_3197 : Nat := 182399739169913935867

theorem tailTrace_3197 : CollatzResearch.WordTrace tailWord_3197 prefixEnd_3197 182399739169913935867 := by
  unfold tailWord_3197
  simp only [CollatzResearch.WordTrace]
  refine ⟨116604169425289849239845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77736112950193232826563 116604169425289849239845)
  ·
    refine ⟨21863281767241846732471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116604169425289849239845 21863281767241846732471)
    ·
      refine ⟨32794922650862770098707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21863281767241846732471 32794922650862770098707)
      ·
        refine ⟨49192383976294155148061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32794922650862770098707 49192383976294155148061)
        ·
          refine ⟨18447143991110308180523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49192383976294155148061 18447143991110308180523)
          ·
            refine ⟨27670715986665462270785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18447143991110308180523 27670715986665462270785)
            ·
              refine ⟨20753036989999096703089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27670715986665462270785 20753036989999096703089)
              ·
                refine ⟨15564777742499322527317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20753036989999096703089 15564777742499322527317)
                ·
                  refine ⟨182399739169913935867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15564777742499322527317 182399739169913935867)
                  ·
                    rfl

theorem cell23_3197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_3197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3197 prefixEnd_3197 := by exact prefixLift 3197
  have htrace : WordTrace (prefixWord ++ tailWord_3197) baseStart_3197 baseEnd_3197 := by
    simpa [prefixWord, tailWord_3197, baseEnd_3197] using wordTrace_append hprefix tailTrace_3197
  have hstable : (prefixWord ++ tailWord_3197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197).length < 2 ^ (prefixWord ++ tailWord_3197).sum := by decide
  have hdescent : baseEnd_3197 < baseStart_3197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 8]
def baseStart_3214 : Nat := 118140960795 + 3214 * 2 ^ 59
def prefixEnd_3214 : Nat := 4983230072969 + 3 ^ 40 * 3214 * 2
def baseEnd_3214 : Nat := 183369647072850990025

theorem tailTrace_3214 : CollatzResearch.WordTrace tailWord_3214 prefixEnd_3214 183369647072850990025 := by
  unfold tailWord_3214
  simp only [CollatzResearch.WordTrace]
  refine ⟨14653026295462719076087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78149473575801168405797 14653026295462719076087)
  ·
    refine ⟨21979539443194078614131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14653026295462719076087 21979539443194078614131)
    ·
      refine ⟨32969309164791117921197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21979539443194078614131 32969309164791117921197)
      ·
        refine ⟨12363490936796669220449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32969309164791117921197 12363490936796669220449)
        ·
          refine ⟨9272618202597501915337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12363490936796669220449 9272618202597501915337)
          ·
            refine ⟨6954463651948126436503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9272618202597501915337 6954463651948126436503)
            ·
              refine ⟨10431695477922189654755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6954463651948126436503 10431695477922189654755)
              ·
                refine ⟨15647543216883284482133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10431695477922189654755 15647543216883284482133)
                ·
                  refine ⟨183369647072850990025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15647543216883284482133 183369647072850990025)
                  ·
                    rfl

theorem cell23_3214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_3214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3214 prefixEnd_3214 := by exact prefixLift 3214
  have htrace : WordTrace (prefixWord ++ tailWord_3214) baseStart_3214 baseEnd_3214 := by
    simpa [prefixWord, tailWord_3214, baseEnd_3214] using wordTrace_append hprefix tailTrace_3214
  have hstable : (prefixWord ++ tailWord_3214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214).length < 2 ^ (prefixWord ++ tailWord_3214).sum := by decide
  have hdescent : baseEnd_3214 < baseStart_3214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218 : List Nat := [3, 2, 3, 1, 1, 2, 2, 4, 1, 4]
def baseStart_3218 : Nat := 118140960795 + 3218 * 2 ^ 59
def prefixEnd_3218 : Nat := 4983230072969 + 3 ^ 40 * 3218 * 2
def baseEnd_3218 : Nat := 550793582091214420069

theorem tailTrace_3218 : CollatzResearch.WordTrace tailWord_3218 prefixEnd_3218 550793582091214420069 := by
  unfold tailWord_3218
  simp only [CollatzResearch.WordTrace]
  refine ⟨29342525587302608938577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78246734899473623836205 29342525587302608938577)
  ·
    refine ⟨22006894190476956703933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29342525587302608938577 22006894190476956703933)
    ·
      refine ⟨8252585321428858763975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22006894190476956703933 8252585321428858763975)
      ·
        refine ⟨12378877982143288145963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8252585321428858763975 12378877982143288145963)
        ·
          refine ⟨18568316973214932218945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12378877982143288145963 18568316973214932218945)
          ·
            refine ⟨13926237729911199164209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18568316973214932218945 13926237729911199164209)
            ·
              refine ⟨10444678297433399373157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13926237729911199164209 10444678297433399373157)
              ·
                refine ⟨1958377180768762382467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10444678297433399373157 1958377180768762382467)
                ·
                  refine ⟨2937565771153143573701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1958377180768762382467 2937565771153143573701)
                  ·
                    refine ⟨550793582091214420069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2937565771153143573701 550793582091214420069)
                    ·
                      rfl

theorem cell23_3218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_3218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3218 prefixEnd_3218 := by exact prefixLift 3218
  have htrace : WordTrace (prefixWord ++ tailWord_3218) baseStart_3218 baseEnd_3218 := by
    simpa [prefixWord, tailWord_3218, baseEnd_3218] using wordTrace_append hprefix tailTrace_3218
  have hstable : (prefixWord ++ tailWord_3218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218).length < 2 ^ (prefixWord ++ tailWord_3218).sum := by decide
  have hdescent : baseEnd_3218 < baseStart_3218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287 : List Nat := [1, 1, 3, 2, 1, 2, 3, 10]
def baseStart_3287 : Nat := 118140960795 + 3287 * 2 ^ 59
def prefixEnd_3287 : Nat := 4983230072969 + 3 ^ 40 * 3287 * 2
def baseEnd_3287 : Nat := 62511515238291603607

theorem tailTrace_3287 : CollatzResearch.WordTrace tailWord_3287 prefixEnd_3287 62511515238291603607 := by
  unfold tailWord_3287
  simp only [CollatzResearch.WordTrace]
  refine ⟨119886739099235220016115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79924492732823480010743 119886739099235220016115)
  ·
    refine ⟨179830108648852830024173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119886739099235220016115 179830108648852830024173)
    ·
      refine ⟨67436290743319811259065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179830108648852830024173 67436290743319811259065)
      ·
        refine ⟨50577218057489858444299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67436290743319811259065 50577218057489858444299)
        ·
          refine ⟨75865827086234787666449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50577218057489858444299 75865827086234787666449)
          ·
            refine ⟨56899370314676090749837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75865827086234787666449 56899370314676090749837)
            ·
              refine ⟨21337263868003534031189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56899370314676090749837 21337263868003534031189)
              ·
                refine ⟨62511515238291603607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21337263868003534031189 62511515238291603607)
                ·
                  rfl

theorem cell23_3287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 10].length) (baseStart_3287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3287 prefixEnd_3287 := by exact prefixLift 3287
  have htrace : WordTrace (prefixWord ++ tailWord_3287) baseStart_3287 baseEnd_3287 := by
    simpa [prefixWord, tailWord_3287, baseEnd_3287] using wordTrace_append hprefix tailTrace_3287
  have hstable : (prefixWord ++ tailWord_3287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287).length < 2 ^ (prefixWord ++ tailWord_3287).sum := by decide
  have hdescent : baseEnd_3287 < baseStart_3287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311 : List Nat := [1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 4]
def baseStart_3311 : Nat := 118140960795 + 3311 * 2 ^ 59
def prefixEnd_3311 : Nat := 4983230072969 + 3 ^ 40 * 3311 * 2
def baseEnd_3311 : Nat := 1700134447141779397279

theorem tailTrace_3311 : CollatzResearch.WordTrace tailWord_3311 prefixEnd_3311 1700134447141779397279 := by
  unfold tailWord_3311
  simp only [CollatzResearch.WordTrace]
  refine ⟨120762091012287318889787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80508060674858212593191 120762091012287318889787)
  ·
    refine ⟨181143136518430978334681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120762091012287318889787 181143136518430978334681)
    ·
      refine ⟨135857352388823233751011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181143136518430978334681 135857352388823233751011)
      ·
        refine ⟨203786028583234850626517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135857352388823233751011 203786028583234850626517)
        ·
          refine ⟨4776235044919566811559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 203786028583234850626517 4776235044919566811559)
          ·
            refine ⟨7164352567379350217339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4776235044919566811559 7164352567379350217339)
            ·
              refine ⟨10746528851069025326009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7164352567379350217339 10746528851069025326009)
              ·
                refine ⟨8059896638301768994507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10746528851069025326009 8059896638301768994507)
                ·
                  refine ⟨12089844957452653491761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8059896638301768994507 12089844957452653491761)
                  ·
                    refine ⟨9067383718089490118821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12089844957452653491761 9067383718089490118821)
                    ·
                      refine ⟨1700134447141779397279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9067383718089490118821 1700134447141779397279)
                      ·
                        rfl

theorem cell23_3311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 4].length) (baseStart_3311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3311 prefixEnd_3311 := by exact prefixLift 3311
  have htrace : WordTrace (prefixWord ++ tailWord_3311) baseStart_3311 baseEnd_3311 := by
    simpa [prefixWord, tailWord_3311, baseEnd_3311] using wordTrace_append hprefix tailTrace_3311
  have hstable : (prefixWord ++ tailWord_3311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311).length < 2 ^ (prefixWord ++ tailWord_3311).sum := by decide
  have hdescent : baseEnd_3311 < baseStart_3311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332 : List Nat := [2, 3, 2, 2, 2, 2, 1, 4, 1, 2, 2]
def baseStart_3332 : Nat := 118140960795 + 3332 * 2 ^ 59
def prefixEnd_3332 : Nat := 4983230072969 + 3 ^ 40 * 3332 * 2
def baseEnd_3332 : Nat := 1710917540886197234683

theorem tailTrace_3332 : CollatzResearch.WordTrace tailWord_3332 prefixEnd_3332 1710917540886197234683 := by
  unfold tailWord_3332
  simp only [CollatzResearch.WordTrace]
  refine ⟨60764011968103952702125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81018682624138603602833 60764011968103952702125)
  ·
    refine ⟨22786504488038982263297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60764011968103952702125 22786504488038982263297)
    ·
      refine ⟨17089878366029236697473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22786504488038982263297 17089878366029236697473)
      ·
        refine ⟨12817408774521927523105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17089878366029236697473 12817408774521927523105)
        ·
          refine ⟨9613056580891445642329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12817408774521927523105 9613056580891445642329)
          ·
            refine ⟨7209792435668584231747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9613056580891445642329 7209792435668584231747)
            ·
              refine ⟨10814688653502876347621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7209792435668584231747 10814688653502876347621)
              ·
                refine ⟨2027754122531789315179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10814688653502876347621 2027754122531789315179)
                ·
                  refine ⟨3041631183797683972769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2027754122531789315179 3041631183797683972769)
                  ·
                    refine ⟨2281223387848262979577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3041631183797683972769 2281223387848262979577)
                    ·
                      refine ⟨1710917540886197234683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2281223387848262979577 1710917540886197234683)
                      ·
                        rfl

theorem cell23_3332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_3332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332 prefixEnd_3332 := by exact prefixLift 3332
  have htrace : WordTrace (prefixWord ++ tailWord_3332) baseStart_3332 baseEnd_3332 := by
    simpa [prefixWord, tailWord_3332, baseEnd_3332] using wordTrace_append hprefix tailTrace_3332
  have hstable : (prefixWord ++ tailWord_3332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332).length < 2 ^ (prefixWord ++ tailWord_3332).sum := by decide
  have hdescent : baseEnd_3332 < baseStart_3332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 1, 8]
def baseStart_3364 : Nat := 118140960795 + 3364 * 2 ^ 59
def prefixEnd_3364 : Nat := 4983230072969 + 3 ^ 40 * 3364 * 2
def baseEnd_3364 : Nat := 575782973943357344845

theorem tailTrace_3364 : CollatzResearch.WordTrace tailWord_3364 prefixEnd_3364 575782973943357344845 := by
  unfold tailWord_3364
  simp only [CollatzResearch.WordTrace]
  refine ⟨61347579910138685284573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81796773213518247046097 61347579910138685284573)
  ·
    refine ⟨23005342466302006981715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61347579910138685284573 23005342466302006981715)
    ·
      refine ⟨34508013699453010472573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23005342466302006981715 34508013699453010472573)
      ·
        refine ⟨12940505137294878927215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34508013699453010472573 12940505137294878927215)
        ·
          refine ⟨19410757705942318390823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12940505137294878927215 19410757705942318390823)
          ·
            refine ⟨29116136558913477586235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19410757705942318390823 29116136558913477586235)
            ·
              refine ⟨43674204838370216379353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29116136558913477586235 43674204838370216379353)
              ·
                refine ⟨32755653628777662284515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43674204838370216379353 32755653628777662284515)
                ·
                  refine ⟨49133480443166493426773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32755653628777662284515 49133480443166493426773)
                  ·
                    refine ⟨575782973943357344845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49133480443166493426773 575782973943357344845)
                    ·
                      rfl

theorem cell23_3364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_3364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364 prefixEnd_3364 := by exact prefixLift 3364
  have htrace : WordTrace (prefixWord ++ tailWord_3364) baseStart_3364 baseEnd_3364 := by
    simpa [prefixWord, tailWord_3364, baseEnd_3364] using wordTrace_append hprefix tailTrace_3364
  have hstable : (prefixWord ++ tailWord_3364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364).length < 2 ^ (prefixWord ++ tailWord_3364).sum := by decide
  have hdescent : baseEnd_3364 < baseStart_3364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_3382 : Nat := 118140960795 + 3382 * 2 ^ 59
def prefixEnd_3382 : Nat := 4983230072969 + 3 ^ 40 * 3382 * 2
def baseEnd_3382 : Nat := 1736591573611001609453

theorem tailTrace_3382 : CollatzResearch.WordTrace tailWord_3382 prefixEnd_3382 1736591573611001609453 := by
  unfold tailWord_3382
  simp only [CollatzResearch.WordTrace]
  refine ⟨7709479609691652795275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82234449170044296482933 7709479609691652795275)
  ·
    refine ⟨11564219414537479192913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7709479609691652795275 11564219414537479192913)
    ·
      refine ⟨8673164560903109394685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11564219414537479192913 8673164560903109394685)
      ·
        refine ⟨3252436710338666023007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8673164560903109394685 3252436710338666023007)
        ·
          refine ⟨4878655065507999034511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3252436710338666023007 4878655065507999034511)
          ·
            refine ⟨7317982598261998551767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4878655065507999034511 7317982598261998551767)
            ·
              refine ⟨10976973897392997827651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7317982598261998551767 10976973897392997827651)
              ·
                refine ⟨16465460846089496741477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10976973897392997827651 16465460846089496741477)
                ·
                  refine ⟨3087273908641780639027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16465460846089496741477 3087273908641780639027)
                  ·
                    refine ⟨4630910862962670958541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3087273908641780639027 4630910862962670958541)
                    ·
                      refine ⟨1736591573611001609453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4630910862962670958541 1736591573611001609453)
                      ·
                        rfl

theorem cell23_3382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_3382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382 prefixEnd_3382 := by exact prefixLift 3382
  have htrace : WordTrace (prefixWord ++ tailWord_3382) baseStart_3382 baseEnd_3382 := by
    simpa [prefixWord, tailWord_3382, baseEnd_3382] using wordTrace_append hprefix tailTrace_3382
  have hstable : (prefixWord ++ tailWord_3382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382).length < 2 ^ (prefixWord ++ tailWord_3382).sum := by decide
  have hdescent : baseEnd_3382 < baseStart_3382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428 : List Nat := [2, 3, 1, 1, 3, 2, 3, 3, 5]
def baseStart_3428 : Nat := 118140960795 + 3428 * 2 ^ 59
def prefixEnd_3428 : Nat := 4983230072969 + 3 ^ 40 * 3428 * 2
def baseEnd_3428 : Nat := 195579075968646848249

theorem tailTrace_3428 : CollatzResearch.WordTrace tailWord_3428 prefixEnd_3428 195579075968646848249 := by
  unfold tailWord_3428
  simp only [CollatzResearch.WordTrace]
  refine ⟨62514715794208150449469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83352954392277533932625 62514715794208150449469)
  ·
    refine ⟨23443018422828056418551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62514715794208150449469 23443018422828056418551)
    ·
      refine ⟨35164527634242084627827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23443018422828056418551 35164527634242084627827)
      ·
        refine ⟨52746791451363126941741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35164527634242084627827 52746791451363126941741)
        ·
          refine ⟨19780046794261172603153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52746791451363126941741 19780046794261172603153)
          ·
            refine ⟨14835035095695879452365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19780046794261172603153 14835035095695879452365)
            ·
              refine ⟨5563138160885954794637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14835035095695879452365 5563138160885954794637)
              ·
                refine ⟨2086176810332233047989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5563138160885954794637 2086176810332233047989)
                ·
                  refine ⟨195579075968646848249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2086176810332233047989 195579075968646848249)
                  ·
                    rfl

theorem cell23_3428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_3428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428 prefixEnd_3428 := by exact prefixLift 3428
  have htrace : WordTrace (prefixWord ++ tailWord_3428) baseStart_3428 baseEnd_3428 := by
    simpa [prefixWord, tailWord_3428, baseEnd_3428] using wordTrace_append hprefix tailTrace_3428
  have hstable : (prefixWord ++ tailWord_3428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428).length < 2 ^ (prefixWord ++ tailWord_3428).sum := by decide
  have hdescent : baseEnd_3428 < baseStart_3428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445 : List Nat := [1, 3, 4, 1, 4, 1, 1, 1, 7]
def baseStart_3445 : Nat := 118140960795 + 3445 * 2 ^ 59
def prefixEnd_3445 : Nat := 4983230072969 + 3 ^ 40 * 3445 * 2
def baseEnd_3445 : Nat := 196548983871583902407

theorem tailTrace_3445 : CollatzResearch.WordTrace tailWord_3445 prefixEnd_3445 196548983871583902407 := by
  unfold tailWord_3445
  simp only [CollatzResearch.WordTrace]
  refine ⟨125649472526828204267789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83766315017885469511859 125649472526828204267789)
  ·
    refine ⟨47118552197560576600421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125649472526828204267789 47118552197560576600421)
    ·
      refine ⟨8834728537042608112579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47118552197560576600421 8834728537042608112579)
      ·
        refine ⟨13252092805563912168869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8834728537042608112579 13252092805563912168869)
        ·
          refine ⟨2484767401043233531663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13252092805563912168869 2484767401043233531663)
          ·
            refine ⟨3727151101564850297495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2484767401043233531663 3727151101564850297495)
            ·
              refine ⟨5590726652347275446243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3727151101564850297495 5590726652347275446243)
              ·
                refine ⟨8386089978520913169365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5590726652347275446243 8386089978520913169365)
                ·
                  refine ⟨196548983871583902407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8386089978520913169365 196548983871583902407)
                  ·
                    rfl

theorem cell23_3445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 7].length) (baseStart_3445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3445 prefixEnd_3445 := by exact prefixLift 3445
  have htrace : WordTrace (prefixWord ++ tailWord_3445) baseStart_3445 baseEnd_3445 := by
    simpa [prefixWord, tailWord_3445, baseEnd_3445] using wordTrace_append hprefix tailTrace_3445
  have hstable : (prefixWord ++ tailWord_3445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445).length < 2 ^ (prefixWord ++ tailWord_3445).sum := by decide
  have hdescent : baseEnd_3445 < baseStart_3445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505 : List Nat := [1, 2, 2, 4, 1, 1, 3, 4, 1, 4]
def baseStart_3505 : Nat := 118140960795 + 3505 * 2 ^ 59
def prefixEnd_3505 : Nat := 4983230072969 + 3 ^ 40 * 3505 * 2
def baseEnd_3505 : Nat := 599916564704673457129

theorem tailTrace_3505 : CollatzResearch.WordTrace tailWord_3505 prefixEnd_3505 599916564704673457129 := by
  unfold tailWord_3505
  simp only [CollatzResearch.WordTrace]
  refine ⟨127837852309458451451969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85225234872972300967979 127837852309458451451969)
  ·
    refine ⟨95878389232093838588977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127837852309458451451969 95878389232093838588977)
    ·
      refine ⟨71908791924070378941733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95878389232093838588977 71908791924070378941733)
      ·
        refine ⟨13482898485763196051575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71908791924070378941733 13482898485763196051575)
        ·
          refine ⟨20224347728644794077363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13482898485763196051575 20224347728644794077363)
          ·
            refine ⟨30336521592967191116045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20224347728644794077363 30336521592967191116045)
            ·
              refine ⟨11376195597362696668517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30336521592967191116045 11376195597362696668517)
              ·
                refine ⟨2133036674505505625347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11376195597362696668517 2133036674505505625347)
                ·
                  refine ⟨3199555011758258438021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2133036674505505625347 3199555011758258438021)
                  ·
                    refine ⟨599916564704673457129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3199555011758258438021 599916564704673457129)
                    ·
                      rfl

theorem cell23_3505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 1, 4].length) (baseStart_3505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505 prefixEnd_3505 := by exact prefixLift 3505
  have htrace : WordTrace (prefixWord ++ tailWord_3505) baseStart_3505 baseEnd_3505 := by
    simpa [prefixWord, tailWord_3505, baseEnd_3505] using wordTrace_append hprefix tailTrace_3505
  have hstable : (prefixWord ++ tailWord_3505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505).length < 2 ^ (prefixWord ++ tailWord_3505).sum := by decide
  have hdescent : baseEnd_3505 < baseStart_3505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 3, 5]
def baseStart_3531 : Nat := 118140960795 + 3531 * 2 ^ 59
def prefixEnd_3531 : Nat := 4983230072969 + 3 ^ 40 * 3531 * 2
def baseEnd_3531 : Nat := 604366730376972882089

theorem tailTrace_3531 : CollatzResearch.WordTrace tailWord_3531 prefixEnd_3531 604366730376972882089 := by
  unfold tailWord_3531
  simp only [CollatzResearch.WordTrace]
  refine ⟨128786150215264891898447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85857433476843261265631 128786150215264891898447)
  ·
    refine ⟨193179225322897337847671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128786150215264891898447 193179225322897337847671)
    ·
      refine ⟨289768837984346006771507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193179225322897337847671 289768837984346006771507)
      ·
        refine ⟨434653256976519010157261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289768837984346006771507 434653256976519010157261)
        ·
          refine ⟨162994971366194628808973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 434653256976519010157261 162994971366194628808973)
          ·
            refine ⟨61123114262322985803365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162994971366194628808973 61123114262322985803365)
            ·
              refine ⟨11460583924185559838131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61123114262322985803365 11460583924185559838131)
              ·
                refine ⟨17190875886278339757197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11460583924185559838131 17190875886278339757197)
                ·
                  refine ⟨6446578457354377408949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17190875886278339757197 6446578457354377408949)
                  ·
                    refine ⟨604366730376972882089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6446578457354377408949 604366730376972882089)
                    ·
                      rfl

theorem cell23_3531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 5].length) (baseStart_3531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531 prefixEnd_3531 := by exact prefixLift 3531
  have htrace : WordTrace (prefixWord ++ tailWord_3531) baseStart_3531 baseEnd_3531 := by
    simpa [prefixWord, tailWord_3531, baseEnd_3531] using wordTrace_append hprefix tailTrace_3531
  have hstable : (prefixWord ++ tailWord_3531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531).length < 2 ^ (prefixWord ++ tailWord_3531).sum := by decide
  have hdescent : baseEnd_3531 < baseStart_3531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562 : List Nat := [3, 1, 3, 1, 4, 1, 2, 1, 3, 1, 3]
def baseStart_3562 : Nat := 118140960795 + 3562 * 2 ^ 59
def prefixEnd_3562 : Nat := 4983230072969 + 3 ^ 40 * 3562 * 2
def baseEnd_3562 : Nat := 1829018091420297358625

theorem tailTrace_3562 : CollatzResearch.WordTrace tailWord_3562 prefixEnd_3562 1829018091420297358625 := by
  unfold tailWord_3562
  simp only [CollatzResearch.WordTrace]
  refine ⟨32479203275739296569235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86611208735304790851293 32479203275739296569235)
  ·
    refine ⟨48718804913608944853853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32479203275739296569235 48718804913608944853853)
    ·
      refine ⟨18269551842603354320195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48718804913608944853853 18269551842603354320195)
      ·
        refine ⟨27404327763905031480293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18269551842603354320195 27404327763905031480293)
        ·
          refine ⟨5138311455732193402555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27404327763905031480293 5138311455732193402555)
          ·
            refine ⟨7707467183598290103833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5138311455732193402555 7707467183598290103833)
            ·
              refine ⟨5780600387698717577875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7707467183598290103833 5780600387698717577875)
              ·
                refine ⟨8670900581548076366813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5780600387698717577875 8670900581548076366813)
                ·
                  refine ⟨3251587718080528637555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8670900581548076366813 3251587718080528637555)
                  ·
                    refine ⟨4877381577120792956333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3251587718080528637555 4877381577120792956333)
                    ·
                      refine ⟨1829018091420297358625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4877381577120792956333 1829018091420297358625)
                      ·
                        rfl

theorem cell23_3562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_3562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562 prefixEnd_3562 := by exact prefixLift 3562
  have htrace : WordTrace (prefixWord ++ tailWord_3562) baseStart_3562 baseEnd_3562 := by
    simpa [prefixWord, tailWord_3562, baseEnd_3562] using wordTrace_append hprefix tailTrace_3562
  have hstable : (prefixWord ++ tailWord_3562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562).length < 2 ^ (prefixWord ++ tailWord_3562).sum := by decide
  have hdescent : baseEnd_3562 < baseStart_3562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 3]
def baseStart_3571 : Nat := 118140960795 + 3571 * 2 ^ 59
def prefixEnd_3571 : Nat := 4983230072969 + 3 ^ 40 * 3571 * 2
def baseEnd_3571 : Nat := 1833639417310762146083

theorem tailTrace_3571 : CollatzResearch.WordTrace tailWord_3571 prefixEnd_3571 1833639417310762146083 := by
  unfold tailWord_3571
  simp only [CollatzResearch.WordTrace]
  refine ⟨130245070070351723354567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86830046713567815569711 130245070070351723354567)
  ·
    refine ⟨195367605105527585031851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130245070070351723354567 195367605105527585031851)
    ·
      refine ⟨293051407658291377547777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195367605105527585031851 293051407658291377547777)
      ·
        refine ⟨219788555743718533160833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293051407658291377547777 219788555743718533160833)
        ·
          refine ⟨164841416807788899870625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219788555743718533160833 164841416807788899870625)
          ·
            refine ⟨123631062605841674902969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164841416807788899870625 123631062605841674902969)
            ·
              refine ⟨92723296954381256177227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123631062605841674902969 92723296954381256177227)
              ·
                refine ⟨139084945431571884265841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92723296954381256177227 139084945431571884265841)
                ·
                  refine ⟨104313709073678913199381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139084945431571884265841 104313709073678913199381)
                  ·
                    refine ⟨4889705112828699056221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104313709073678913199381 4889705112828699056221)
                    ·
                      refine ⟨1833639417310762146083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4889705112828699056221 1833639417310762146083)
                      ·
                        rfl

theorem cell23_3571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 3].length) (baseStart_3571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3571 prefixEnd_3571 := by exact prefixLift 3571
  have htrace : WordTrace (prefixWord ++ tailWord_3571) baseStart_3571 baseEnd_3571 := by
    simpa [prefixWord, tailWord_3571, baseEnd_3571] using wordTrace_append hprefix tailTrace_3571
  have hstable : (prefixWord ++ tailWord_3571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571).length < 2 ^ (prefixWord ++ tailWord_3571).sum := by decide
  have hdescent : baseEnd_3571 < baseStart_3571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590 : List Nat := [6, 2, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_3590 : Nat := 118140960795 + 3590 * 2 ^ 59
def prefixEnd_3590 : Nat := 4983230072969 + 3 ^ 40 * 3590 * 2
def baseEnd_3590 : Nat := 614465183248729269499

theorem tailTrace_3590 : CollatzResearch.WordTrace tailWord_3590 prefixEnd_3590 614465183248729269499 := by
  unfold tailWord_3590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4091814281297436509257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87292038001011978864149 4091814281297436509257)
  ·
    refine ⟨3068860710973077381943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4091814281297436509257 3068860710973077381943)
    ·
      refine ⟨4603291066459616072915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3068860710973077381943 4603291066459616072915)
      ·
        refine ⟨6904936599689424109373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4603291066459616072915 6904936599689424109373)
        ·
          refine ⟨2589351224883534041015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6904936599689424109373 2589351224883534041015)
          ·
            refine ⟨3884026837325301061523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2589351224883534041015 3884026837325301061523)
            ·
              refine ⟨5826040255987951592285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3884026837325301061523 5826040255987951592285)
              ·
                refine ⟨2184765095995481847107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5826040255987951592285 2184765095995481847107)
                ·
                  refine ⟨3277147643993222770661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2184765095995481847107 3277147643993222770661)
                  ·
                    refine ⟨614465183248729269499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3277147643993222770661 614465183248729269499)
                    ·
                      rfl

theorem cell23_3590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_3590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590 prefixEnd_3590 := by exact prefixLift 3590
  have htrace : WordTrace (prefixWord ++ tailWord_3590) baseStart_3590 baseEnd_3590 := by
    simpa [prefixWord, tailWord_3590, baseEnd_3590] using wordTrace_append hprefix tailTrace_3590
  have hstable : (prefixWord ++ tailWord_3590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590).length < 2 ^ (prefixWord ++ tailWord_3590).sum := by decide
  have hdescent : baseEnd_3590 < baseStart_3590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3596 : List Nat := [2, 2, 1, 2, 6, 1, 1, 3, 1, 1, 3]
def baseStart_3596 : Nat := 118140960795 + 3596 * 2 ^ 59
def prefixEnd_3596 : Nat := 4983230072969 + 3 ^ 40 * 3596 * 2
def baseEnd_3596 : Nat := 1846476433673164333469

theorem tailTrace_3596 : CollatzResearch.WordTrace tailWord_3596 prefixEnd_3596 1846476433673164333469 := by
  unfold tailWord_3596
  simp only [CollatzResearch.WordTrace]
  refine ⟨65578447489890496507321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87437929986520662009761 65578447489890496507321)
  ·
    refine ⟨49183835617417872380491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65578447489890496507321 49183835617417872380491)
    ·
      refine ⟨73775753426126808570737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49183835617417872380491 73775753426126808570737)
      ·
        refine ⟨55331815069595106428053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73775753426126808570737 55331815069595106428053)
        ·
          refine ⟨2593678831387270613815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55331815069595106428053 2593678831387270613815)
          ·
            refine ⟨3890518247080905920723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2593678831387270613815 3890518247080905920723)
            ·
              refine ⟨5835777370621358881085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3890518247080905920723 5835777370621358881085)
              ·
                refine ⟨2188416513983009580407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5835777370621358881085 2188416513983009580407)
                ·
                  refine ⟨3282624770974514370611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2188416513983009580407 3282624770974514370611)
                  ·
                    refine ⟨4923937156461771555917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3282624770974514370611 4923937156461771555917)
                    ·
                      refine ⟨1846476433673164333469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4923937156461771555917 1846476433673164333469)
                      ·
                        rfl

theorem cell23_3596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 1, 1, 3].length) (baseStart_3596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3596 prefixEnd_3596 := by exact prefixLift 3596
  have htrace : WordTrace (prefixWord ++ tailWord_3596) baseStart_3596 baseEnd_3596 := by
    simpa [prefixWord, tailWord_3596, baseEnd_3596] using wordTrace_append hprefix tailTrace_3596
  have hstable : (prefixWord ++ tailWord_3596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3596).length < 2 ^ (prefixWord ++ tailWord_3596).sum := by decide
  have hdescent : baseEnd_3596 < baseStart_3596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605 : List Nat := [1, 3, 2, 1, 3, 2, 2, 3, 1, 2, 3]
def baseStart_3605 : Nat := 118140960795 + 3605 * 2 ^ 59
def prefixEnd_3605 : Nat := 4983230072969 + 3 ^ 40 * 3605 * 2
def baseEnd_3605 : Nat := 1851097759563629120927

theorem tailTrace_3605 : CollatzResearch.WordTrace tailWord_3605 prefixEnd_3605 1851097759563629120927 := by
  unfold tailWord_3605
  simp only [CollatzResearch.WordTrace]
  refine ⟨131485151947175530092269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87656767964783686728179 131485151947175530092269)
  ·
    refine ⟨49306931980190823784601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131485151947175530092269 49306931980190823784601)
    ·
      refine ⟨36980198985143117838451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49306931980190823784601 36980198985143117838451)
      ·
        refine ⟨55470298477714676757677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36980198985143117838451 55470298477714676757677)
        ·
          refine ⟨20801361929143003784129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55470298477714676757677 20801361929143003784129)
          ·
            refine ⟨15601021446857252838097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20801361929143003784129 15601021446857252838097)
            ·
              refine ⟨11700766085142939628573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15601021446857252838097 11700766085142939628573)
              ·
                refine ⟨4387787281928602360715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11700766085142939628573 4387787281928602360715)
                ·
                  refine ⟨6581680922892903541073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4387787281928602360715 6581680922892903541073)
                  ·
                    refine ⟨4936260692169677655805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6581680922892903541073 4936260692169677655805)
                    ·
                      refine ⟨1851097759563629120927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4936260692169677655805 1851097759563629120927)
                      ·
                        rfl

theorem cell23_3605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_3605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605 prefixEnd_3605 := by exact prefixLift 3605
  have htrace : WordTrace (prefixWord ++ tailWord_3605) baseStart_3605 baseEnd_3605 := by
    simpa [prefixWord, tailWord_3605, baseEnd_3605] using wordTrace_append hprefix tailTrace_3605
  have hstable : (prefixWord ++ tailWord_3605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605).length < 2 ^ (prefixWord ++ tailWord_3605).sum := by decide
  have hdescent : baseEnd_3605 < baseStart_3605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608 : List Nat := [2, 1, 2, 3, 4, 2, 9]
def baseStart_3608 : Nat := 118140960795 + 3608 * 2 ^ 59
def prefixEnd_3608 : Nat := 4983230072969 + 3 ^ 40 * 3608 * 2
def baseEnd_3608 : Nat := 22872076562063177573

theorem tailTrace_3608 : CollatzResearch.WordTrace tailWord_3608 prefixEnd_3608 22872076562063177573 := by
  unfold tailWord_3608
  simp only [CollatzResearch.WordTrace]
  refine ⟨65797285468153521225739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87729713957538028300985 65797285468153521225739)
  ·
    refine ⟨98695928202230281838609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65797285468153521225739 98695928202230281838609)
    ·
      refine ⟨74021946151672711378957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98695928202230281838609 74021946151672711378957)
      ·
        refine ⟨27758229806877266767109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74021946151672711378957 27758229806877266767109)
        ·
          refine ⟨5204668088789487518833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27758229806877266767109 5204668088789487518833)
          ·
            refine ⟨3903501066592115639125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5204668088789487518833 3903501066592115639125)
            ·
              refine ⟨22872076562063177573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3903501066592115639125 22872076562063177573)
              ·
                rfl

theorem cell23_3608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 9].length) (baseStart_3608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608 prefixEnd_3608 := by exact prefixLift 3608
  have htrace : WordTrace (prefixWord ++ tailWord_3608) baseStart_3608 baseEnd_3608 := by
    simpa [prefixWord, tailWord_3608, baseEnd_3608] using wordTrace_append hprefix tailTrace_3608
  have hstable : (prefixWord ++ tailWord_3608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608).length < 2 ^ (prefixWord ++ tailWord_3608).sum := by decide
  have hdescent : baseEnd_3608 < baseStart_3608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619 : List Nat := [1, 1, 1, 4, 5, 2, 1, 1, 3, 2, 2]
def baseStart_3619 : Nat := 118140960795 + 3619 * 2 ^ 59
def prefixEnd_3619 : Nat := 4983230072969 + 3 ^ 40 * 3619 * 2
def baseEnd_3619 : Nat := 1858286488726574345863

theorem tailTrace_3619 : CollatzResearch.WordTrace tailWord_3619 prefixEnd_3619 1858286488726574345863 := by
  unfold tailWord_3619
  simp only [CollatzResearch.WordTrace]
  refine ⟨131995773896455921101911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87997182597637280734607 131995773896455921101911)
  ·
    refine ⟨197993660844683881652867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131995773896455921101911 197993660844683881652867)
    ·
      refine ⟨296990491267025822479301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197993660844683881652867 296990491267025822479301)
      ·
        refine ⟨55685717112567341714869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 296990491267025822479301 55685717112567341714869)
        ·
          refine ⟨5220535979303188285769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55685717112567341714869 5220535979303188285769)
          ·
            refine ⟨3915401984477391214327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5220535979303188285769 3915401984477391214327)
            ·
              refine ⟨5873102976716086821491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3915401984477391214327 5873102976716086821491)
              ·
                refine ⟨8809654465074130232237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5873102976716086821491 8809654465074130232237)
                ·
                  refine ⟨3303620424402798837089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8809654465074130232237 3303620424402798837089)
                  ·
                    refine ⟨2477715318302099127817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3303620424402798837089 2477715318302099127817)
                    ·
                      refine ⟨1858286488726574345863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2477715318302099127817 1858286488726574345863)
                      ·
                        rfl

theorem cell23_3619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 2, 2].length) (baseStart_3619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619 prefixEnd_3619 := by exact prefixLift 3619
  have htrace : WordTrace (prefixWord ++ tailWord_3619) baseStart_3619 baseEnd_3619 := by
    simpa [prefixWord, tailWord_3619, baseEnd_3619] using wordTrace_append hprefix tailTrace_3619
  have hstable : (prefixWord ++ tailWord_3619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619).length < 2 ^ (prefixWord ++ tailWord_3619).sum := by decide
  have hdescent : baseEnd_3619 < baseStart_3619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 2, 7]
def baseStart_3621 : Nat := 118140960795 + 3621 * 2 ^ 59
def prefixEnd_3621 : Nat := 4983230072969 + 3 ^ 40 * 3621 * 2
def baseEnd_3621 : Nat := 619771150011855506951

theorem tailTrace_3621 : CollatzResearch.WordTrace tailWord_3621 prefixEnd_3621 619771150011855506951 := by
  unfold tailWord_3621
  simp only [CollatzResearch.WordTrace]
  refine ⟨132068719889210262674717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88045813259473508449811 132068719889210262674717)
  ·
    refine ⟨49525769958453848503019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132068719889210262674717 49525769958453848503019)
    ·
      refine ⟨74288654937680772754529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49525769958453848503019 74288654937680772754529)
      ·
        refine ⟨55716491203260579565897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74288654937680772754529 55716491203260579565897)
        ·
          refine ⟨41787368402445434674423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55716491203260579565897 41787368402445434674423)
          ·
            refine ⟨62681052603668152011635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41787368402445434674423 62681052603668152011635)
            ·
              refine ⟨94021578905502228017453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62681052603668152011635 94021578905502228017453)
              ·
                refine ⟨35258092089563335506545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94021578905502228017453 35258092089563335506545)
                ·
                  refine ⟨26443569067172501629909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35258092089563335506545 26443569067172501629909)
                  ·
                    refine ⟨619771150011855506951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26443569067172501629909 619771150011855506951)
                    ·
                      rfl

theorem cell23_3621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_3621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621 prefixEnd_3621 := by exact prefixLift 3621
  have htrace : WordTrace (prefixWord ++ tailWord_3621) baseStart_3621 baseEnd_3621 := by
    simpa [prefixWord, tailWord_3621, baseEnd_3621] using wordTrace_append hprefix tailTrace_3621
  have hstable : (prefixWord ++ tailWord_3621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621).length < 2 ^ (prefixWord ++ tailWord_3621).sum := by decide
  have hdescent : baseEnd_3621 < baseStart_3621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 1, 9, 2]
def baseStart_3628 : Nat := 118140960795 + 3628 * 2 ^ 59
def prefixEnd_3628 : Nat := 4983230072969 + 3 ^ 40 * 3628 * 2
def baseEnd_3628 : Nat := 1862907814617039133321

theorem tailTrace_3628 : CollatzResearch.WordTrace tailWord_3628 prefixEnd_3628 1862907814617039133321 := by
  unfold tailWord_3628
  simp only [CollatzResearch.WordTrace]
  refine ⟨66162015431925229089769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88216020575900305453025 66162015431925229089769)
  ·
    refine ⟨49621511573943921817327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66162015431925229089769 49621511573943921817327)
    ·
      refine ⟨74432267360915882725991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49621511573943921817327 74432267360915882725991)
      ·
        refine ⟨111648401041373824088987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74432267360915882725991 111648401041373824088987)
        ·
          refine ⟨167472601562060736133481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111648401041373824088987 167472601562060736133481)
          ·
            refine ⟨125604451171545552100111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167472601562060736133481 125604451171545552100111)
            ·
              refine ⟨188406676757318328150167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125604451171545552100111 188406676757318328150167)
              ·
                refine ⟨282610015135977492225251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188406676757318328150167 282610015135977492225251)
                ·
                  refine ⟨423915022703966238337877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 282610015135977492225251 423915022703966238337877)
                  ·
                    refine ⟨2483877086156052177761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 423915022703966238337877 2483877086156052177761)
                    ·
                      refine ⟨1862907814617039133321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2483877086156052177761 1862907814617039133321)
                      ·
                        rfl

theorem cell23_3628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 9, 2].length) (baseStart_3628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628 prefixEnd_3628 := by exact prefixLift 3628
  have htrace : WordTrace (prefixWord ++ tailWord_3628) baseStart_3628 baseEnd_3628 := by
    simpa [prefixWord, tailWord_3628, baseEnd_3628] using wordTrace_append hprefix tailTrace_3628
  have hstable : (prefixWord ++ tailWord_3628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628).length < 2 ^ (prefixWord ++ tailWord_3628).sum := by decide
  have hdescent : baseEnd_3628 < baseStart_3628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 6, 6]
def baseStart_3651 : Nat := 118140960795 + 3651 * 2 ^ 59
def prefixEnd_3651 : Nat := 4983230072969 + 3 ^ 40 * 3651 * 2
def baseEnd_3651 : Nat := 624905956556816381905

theorem tailTrace_3651 : CollatzResearch.WordTrace tailWord_3651 prefixEnd_3651 624905956556816381905 := by
  unfold tailWord_3651
  simp only [CollatzResearch.WordTrace]
  refine ⟨133162909780525386266807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88775273187016924177871 133162909780525386266807)
  ·
    refine ⟨199744364670788079400211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133162909780525386266807 199744364670788079400211)
    ·
      refine ⟨299616547006182119100317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199744364670788079400211 299616547006182119100317)
      ·
        refine ⟨112356205127318294662619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299616547006182119100317 112356205127318294662619)
        ·
          refine ⟨168534307690977441993929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112356205127318294662619 168534307690977441993929)
          ·
            refine ⟨126400730768233081495447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168534307690977441993929 126400730768233081495447)
            ·
              refine ⟨189601096152349622243171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126400730768233081495447 189601096152349622243171)
              ·
                refine ⟨284401644228524433364757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189601096152349622243171 284401644228524433364757)
                ·
                  refine ⟨13331327073212082813973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 284401644228524433364757 13331327073212082813973)
                  ·
                    refine ⟨624905956556816381905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13331327073212082813973 624905956556816381905)
                    ·
                      rfl

theorem cell23_3651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 6].length) (baseStart_3651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651 prefixEnd_3651 := by exact prefixLift 3651
  have htrace : WordTrace (prefixWord ++ tailWord_3651) baseStart_3651 baseEnd_3651 := by
    simpa [prefixWord, tailWord_3651, baseEnd_3651] using wordTrace_append hprefix tailTrace_3651
  have hstable : (prefixWord ++ tailWord_3651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651).length < 2 ^ (prefixWord ++ tailWord_3651).sum := by decide
  have hdescent : baseEnd_3651 < baseStart_3651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 2, 6]
def baseStart_3668 : Nat := 118140960795 + 3668 * 2 ^ 59
def prefixEnd_3668 : Nat := 4983230072969 + 3 ^ 40 * 3668 * 2
def baseEnd_3668 : Nat := 627815680265627544379

theorem tailTrace_3668 : CollatzResearch.WordTrace tailWord_3668 prefixEnd_3668 627815680265627544379 := by
  unfold tailWord_3668
  simp only [CollatzResearch.WordTrace]
  refine ⟨66891475359468644817829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89188633812624859757105 66891475359468644817829)
  ·
    refine ⟨12542151629900370903343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66891475359468644817829 12542151629900370903343)
    ·
      refine ⟨18813227444850556355015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12542151629900370903343 18813227444850556355015)
      ·
        refine ⟨28219841167275834532523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18813227444850556355015 28219841167275834532523)
        ·
          refine ⟨42329761750913751798785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28219841167275834532523 42329761750913751798785)
          ·
            refine ⟨31747321313185313849089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42329761750913751798785 31747321313185313849089)
            ·
              refine ⟨23810490984888985386817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31747321313185313849089 23810490984888985386817)
              ·
                refine ⟨17857868238666739040113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23810490984888985386817 17857868238666739040113)
                ·
                  refine ⟨13393401179000054280085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17857868238666739040113 13393401179000054280085)
                  ·
                    refine ⟨627815680265627544379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13393401179000054280085 627815680265627544379)
                    ·
                      rfl

theorem cell23_3668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_3668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3668 prefixEnd_3668 := by exact prefixLift 3668
  have htrace : WordTrace (prefixWord ++ tailWord_3668) baseStart_3668 baseEnd_3668 := by
    simpa [prefixWord, tailWord_3668, baseEnd_3668] using wordTrace_append hprefix tailTrace_3668
  have hstable : (prefixWord ++ tailWord_3668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668).length < 2 ^ (prefixWord ++ tailWord_3668).sum := by decide
  have hdescent : baseEnd_3668 < baseStart_3668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670 : List Nat := [5, 2, 2, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_3670 : Nat := 118140960795 + 3670 * 2 ^ 59
def prefixEnd_3670 : Nat := 4983230072969 + 3 ^ 40 * 3670 * 2
def baseEnd_3670 : Nat := 1884474002105874808129

theorem tailTrace_3670 : CollatzResearch.WordTrace tailWord_3670 prefixEnd_3670 1884474002105874808129 := by
  unfold tailWord_3670
  simp only [CollatzResearch.WordTrace]
  refine ⟨8365993544480726950529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89237264474461087472309 8365993544480726950529)
  ·
    refine ⟨6274495158360545212897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8365993544480726950529 6274495158360545212897)
    ·
      refine ⟨4705871368770408909673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6274495158360545212897 4705871368770408909673)
      ·
        refine ⟨3529403526577806682255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4705871368770408909673 3529403526577806682255)
        ·
          refine ⟨5294105289866710023383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3529403526577806682255 5294105289866710023383)
          ·
            refine ⟨7941157934800065035075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5294105289866710023383 7941157934800065035075)
            ·
              refine ⟨11911736902200097552613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7941157934800065035075 11911736902200097552613)
              ·
                refine ⟨2233450669162518291115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11911736902200097552613 2233450669162518291115)
                ·
                  refine ⟨3350176003743777436673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2233450669162518291115 3350176003743777436673)
                  ·
                    refine ⟨2512632002807833077505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3350176003743777436673 2512632002807833077505)
                    ·
                      refine ⟨1884474002105874808129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2512632002807833077505 1884474002105874808129)
                      ·
                        rfl

theorem cell23_3670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_3670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3670 prefixEnd_3670 := by exact prefixLift 3670
  have htrace : WordTrace (prefixWord ++ tailWord_3670) baseStart_3670 baseEnd_3670 := by
    simpa [prefixWord, tailWord_3670, baseEnd_3670] using wordTrace_append hprefix tailTrace_3670
  have hstable : (prefixWord ++ tailWord_3670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670).length < 2 ^ (prefixWord ++ tailWord_3670).sum := by decide
  have hdescent : baseEnd_3670 < baseStart_3670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 7]
def baseStart_3691 : Nat := 118140960795 + 3691 * 2 ^ 59
def prefixEnd_3691 : Nat := 4983230072969 + 3 ^ 40 * 3691 * 2
def baseEnd_3691 : Nat := 1895257095850292645531

theorem tailTrace_3691 : CollatzResearch.WordTrace tailWord_3691 prefixEnd_3691 1895257095850292645531 := by
  unfold tailWord_3691
  simp only [CollatzResearch.WordTrace]
  refine ⟨134621829635612217722927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89747886423741478481951 134621829635612217722927)
  ·
    refine ⟨201932744453418326584391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134621829635612217722927 201932744453418326584391)
    ·
      refine ⟨302899116680127489876587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201932744453418326584391 302899116680127489876587)
      ·
        refine ⟨454348675020191234814881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302899116680127489876587 454348675020191234814881)
        ·
          refine ⟨340761506265143426111161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454348675020191234814881 340761506265143426111161)
          ·
            refine ⟨255571129698857569583371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340761506265143426111161 255571129698857569583371)
            ·
              refine ⟨383356694548286354375057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255571129698857569583371 383356694548286354375057)
              ·
                refine ⟨287517520911214765781293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383356694548286354375057 287517520911214765781293)
                ·
                  refine ⟨107819070341705537167985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287517520911214765781293 107819070341705537167985)
                  ·
                    refine ⟨80864302756279152875989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107819070341705537167985 80864302756279152875989)
                    ·
                      refine ⟨1895257095850292645531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80864302756279152875989 1895257095850292645531)
                      ·
                        rfl

theorem cell23_3691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 7].length) (baseStart_3691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691 prefixEnd_3691 := by exact prefixLift 3691
  have htrace : WordTrace (prefixWord ++ tailWord_3691) baseStart_3691 baseEnd_3691 := by
    simpa [prefixWord, tailWord_3691, baseEnd_3691] using wordTrace_append hprefix tailTrace_3691
  have hstable : (prefixWord ++ tailWord_3691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691).length < 2 ^ (prefixWord ++ tailWord_3691).sum := by decide
  have hdescent : baseEnd_3691 < baseStart_3691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 9]
def baseStart_3698 : Nat := 118140960795 + 3698 * 2 ^ 59
def prefixEnd_3698 : Nat := 4983230072969 + 3 ^ 40 * 3698 * 2
def baseEnd_3698 : Nat := 210983495603529473111

theorem tailTrace_3698 : CollatzResearch.WordTrace tailWord_3698 prefixEnd_3698 210983495603529473111 := by
  unfold tailWord_3698
  simp only [CollatzResearch.WordTrace]
  refine ⟨33719285152563103306937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89918093740168275485165 33719285152563103306937)
  ·
    refine ⟨25289463864422327480203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33719285152563103306937 25289463864422327480203)
    ·
      refine ⟨37934195796633491220305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25289463864422327480203 37934195796633491220305)
      ·
        refine ⟨28450646847475118415229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37934195796633491220305 28450646847475118415229)
        ·
          refine ⟨10668992567803169405711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28450646847475118415229 10668992567803169405711)
          ·
            refine ⟨16003488851704754108567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10668992567803169405711 16003488851704754108567)
            ·
              refine ⟨24005233277557131162851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16003488851704754108567 24005233277557131162851)
              ·
                refine ⟨36007849916335696744277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24005233277557131162851 36007849916335696744277)
                ·
                  refine ⟨210983495603529473111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36007849916335696744277 210983495603529473111)
                  ·
                    rfl

theorem cell23_3698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_3698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698 prefixEnd_3698 := by exact prefixLift 3698
  have htrace : WordTrace (prefixWord ++ tailWord_3698) baseStart_3698 baseEnd_3698 := by
    simpa [prefixWord, tailWord_3698, baseEnd_3698] using wordTrace_append hprefix tailTrace_3698
  have hstable : (prefixWord ++ tailWord_3698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698).length < 2 ^ (prefixWord ++ tailWord_3698).sum := by decide
  have hdescent : baseEnd_3698 < baseStart_3698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 3, 5, 3]
def baseStart_3708 : Nat := 118140960795 + 3708 * 2 ^ 59
def prefixEnd_3708 : Nat := 4983230072969 + 3 ^ 40 * 3708 * 2
def baseEnd_3708 : Nat := 1903986266976726132953

theorem tailTrace_3708 : CollatzResearch.WordTrace tailWord_3708 prefixEnd_3708 1903986266976726132953 := by
  unfold tailWord_3708
  simp only [CollatzResearch.WordTrace]
  refine ⟨67620935287012060545889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90161247049349414061185 67620935287012060545889)
  ·
    refine ⟨50715701465259045409417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67620935287012060545889 50715701465259045409417)
    ·
      refine ⟨38036776098944284057063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50715701465259045409417 38036776098944284057063)
      ·
        refine ⟨57055164148416426085595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38036776098944284057063 57055164148416426085595)
        ·
          refine ⟨85582746222624639128393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57055164148416426085595 85582746222624639128393)
          ·
            refine ⟨64187059666968479346295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85582746222624639128393 64187059666968479346295)
            ·
              refine ⟨96280589500452719019443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64187059666968479346295 96280589500452719019443)
              ·
                refine ⟨144420884250679078529165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96280589500452719019443 144420884250679078529165)
                ·
                  refine ⟨54157831594004654448437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144420884250679078529165 54157831594004654448437)
                  ·
                    refine ⟨5077296711937936354541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54157831594004654448437 5077296711937936354541)
                    ·
                      refine ⟨1903986266976726132953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5077296711937936354541 1903986266976726132953)
                      ·
                        rfl

theorem cell23_3708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_3708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708 prefixEnd_3708 := by exact prefixLift 3708
  have htrace : WordTrace (prefixWord ++ tailWord_3708) baseStart_3708 baseEnd_3708 := by
    simpa [prefixWord, tailWord_3708, baseEnd_3708] using wordTrace_append hprefix tailTrace_3708
  have hstable : (prefixWord ++ tailWord_3708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708).length < 2 ^ (prefixWord ++ tailWord_3708).sum := by decide
  have hdescent : baseEnd_3708 < baseStart_3708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726 : List Nat := [4, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2]
def baseStart_3726 : Nat := 118140960795 + 3726 * 2 ^ 59
def prefixEnd_3726 : Nat := 4983230072969 + 3 ^ 40 * 3726 * 2
def baseEnd_3726 : Nat := 1913228918757655707871

theorem tailTrace_3726 : CollatzResearch.WordTrace tailWord_3726 prefixEnd_3726 1913228918757655707871 := by
  unfold tailWord_3726
  simp only [CollatzResearch.WordTrace]
  refine ⟨16987298063601649405879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90598923005875463498021 16987298063601649405879)
  ·
    refine ⟨25480947095402474108819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16987298063601649405879 25480947095402474108819)
    ·
      refine ⟨38221420643103711163229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25480947095402474108819 38221420643103711163229)
      ·
        refine ⟨14333032741163891686211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38221420643103711163229 14333032741163891686211)
        ·
          refine ⟨21499549111745837529317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14333032741163891686211 21499549111745837529317)
          ·
            refine ⟨4031165458452344536747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21499549111745837529317 4031165458452344536747)
            ·
              refine ⟨6046748187678516805121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4031165458452344536747 6046748187678516805121)
              ·
                refine ⟨4535061140758887603841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6046748187678516805121 4535061140758887603841)
                ·
                  refine ⟨3401295855569165702881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4535061140758887603841 3401295855569165702881)
                  ·
                    refine ⟨2550971891676874277161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3401295855569165702881 2550971891676874277161)
                    ·
                      refine ⟨1913228918757655707871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2550971891676874277161 1913228918757655707871)
                      ·
                        rfl

theorem cell23_3726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_3726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726 prefixEnd_3726 := by exact prefixLift 3726
  have htrace : WordTrace (prefixWord ++ tailWord_3726) baseStart_3726 baseEnd_3726 := by
    simpa [prefixWord, tailWord_3726, baseEnd_3726] using wordTrace_append hprefix tailTrace_3726
  have hstable : (prefixWord ++ tailWord_3726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726).length < 2 ^ (prefixWord ++ tailWord_3726).sum := by decide
  have hdescent : baseEnd_3726 < baseStart_3726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728 : List Nat := [2, 1, 1, 1, 1, 1, 3, 6, 2, 5]
def baseStart_3728 : Nat := 118140960795 + 3728 * 2 ^ 59
def prefixEnd_3728 : Nat := 4983230072969 + 3 ^ 40 * 3728 * 2
def baseEnd_3728 : Nat := 638085293355549294287

theorem tailTrace_3728 : CollatzResearch.WordTrace tailWord_3728 prefixEnd_3728 638085293355549294287 := by
  unfold tailWord_3728
  simp only [CollatzResearch.WordTrace]
  refine ⟨67985665250783768409919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90647553667711691213225 67985665250783768409919)
  ·
    refine ⟨101978497876175652614879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67985665250783768409919 101978497876175652614879)
    ·
      refine ⟨152967746814263478922319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101978497876175652614879 152967746814263478922319)
      ·
        refine ⟨229451620221395218383479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152967746814263478922319 229451620221395218383479)
        ·
          refine ⟨344177430332092827575219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229451620221395218383479 344177430332092827575219)
          ·
            refine ⟨516266145498139241362829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344177430332092827575219 516266145498139241362829)
            ·
              refine ⟨193599804561802215511061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 516266145498139241362829 193599804561802215511061)
              ·
                refine ⟨9074990838834478852081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 193599804561802215511061 9074990838834478852081)
                ·
                  refine ⟨6806243129125859139061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9074990838834478852081 6806243129125859139061)
                  ·
                    refine ⟨638085293355549294287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6806243129125859139061 638085293355549294287)
                    ·
                      rfl

theorem cell23_3728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 2, 5].length) (baseStart_3728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728 prefixEnd_3728 := by exact prefixLift 3728
  have htrace : WordTrace (prefixWord ++ tailWord_3728) baseStart_3728 baseEnd_3728 := by
    simpa [prefixWord, tailWord_3728, baseEnd_3728] using wordTrace_append hprefix tailTrace_3728
  have hstable : (prefixWord ++ tailWord_3728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728).length < 2 ^ (prefixWord ++ tailWord_3728).sum := by decide
  have hdescent : baseEnd_3728 < baseStart_3728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732 : List Nat := [2, 4, 2, 2, 2, 1, 2, 1, 7]
def baseStart_3732 : Nat := 118140960795 + 3732 * 2 ^ 59
def prefixEnd_3732 : Nat := 4983230072969 + 3 ^ 40 * 3732 * 2
def baseEnd_3732 : Nat := 212923311409403581427

theorem tailTrace_3732 : CollatzResearch.WordTrace tailWord_3732 prefixEnd_3732 212923311409403581427 := by
  unfold tailWord_3732
  simp only [CollatzResearch.WordTrace]
  refine ⟨68058611243538109982725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90744814991384146643633 68058611243538109982725)
  ·
    refine ⟨12760989608163395621761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68058611243538109982725 12760989608163395621761)
    ·
      refine ⟨9570742206122546716321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12760989608163395621761 9570742206122546716321)
      ·
        refine ⟨7178056654591910037241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9570742206122546716321 7178056654591910037241)
        ·
          refine ⟨5383542490943932527931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7178056654591910037241 5383542490943932527931)
          ·
            refine ⟨8075313736415898791897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5383542490943932527931 8075313736415898791897)
            ·
              refine ⟨6056485302311924093923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8075313736415898791897 6056485302311924093923)
              ·
                refine ⟨9084727953467886140885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6056485302311924093923 9084727953467886140885)
                ·
                  refine ⟨212923311409403581427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9084727953467886140885 212923311409403581427)
                  ·
                    rfl

theorem cell23_3732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_3732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732 prefixEnd_3732 := by exact prefixLift 3732
  have htrace : WordTrace (prefixWord ++ tailWord_3732) baseStart_3732 baseEnd_3732 := by
    simpa [prefixWord, tailWord_3732, baseEnd_3732] using wordTrace_append hprefix tailTrace_3732
  have hstable : (prefixWord ++ tailWord_3732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732).length < 2 ^ (prefixWord ++ tailWord_3732).sum := by decide
  have hdescent : baseEnd_3732 < baseStart_3732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_3742 : Nat := 118140960795 + 3742 * 2 ^ 59
def prefixEnd_3742 : Nat := 4983230072969 + 3 ^ 40 * 3742 * 2
def baseEnd_3742 : Nat := 1921444609229593107797

theorem tailTrace_3742 : CollatzResearch.WordTrace tailWord_3742 prefixEnd_3742 1921444609229593107797 := by
  unfold tailWord_3742
  simp only [CollatzResearch.WordTrace]
  refine ⟨17060244056355990978685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90987968300565285219653 17060244056355990978685)
  ·
    refine ⟨6397591521133496617007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17060244056355990978685 6397591521133496617007)
    ·
      refine ⟨9596387281700244925511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6397591521133496617007 9596387281700244925511)
      ·
        refine ⟨14394580922550367388267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9596387281700244925511 14394580922550367388267)
        ·
          refine ⟨21591871383825551082401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14394580922550367388267 21591871383825551082401)
          ·
            refine ⟨16193903537869163311801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21591871383825551082401 16193903537869163311801)
            ·
              refine ⟨12145427653401872483851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16193903537869163311801 12145427653401872483851)
              ·
                refine ⟨18218141480102808725777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12145427653401872483851 18218141480102808725777)
                ·
                  refine ⟨13663606110077106544333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18218141480102808725777 13663606110077106544333)
                  ·
                    refine ⟨5123852291278914954125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13663606110077106544333 5123852291278914954125)
                    ·
                      refine ⟨1921444609229593107797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5123852291278914954125 1921444609229593107797)
                      ·
                        rfl

theorem cell23_3742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_3742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3742 prefixEnd_3742 := by exact prefixLift 3742
  have htrace : WordTrace (prefixWord ++ tailWord_3742) baseStart_3742 baseEnd_3742 := by
    simpa [prefixWord, tailWord_3742, baseEnd_3742] using wordTrace_append hprefix tailTrace_3742
  have hstable : (prefixWord ++ tailWord_3742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742).length < 2 ^ (prefixWord ++ tailWord_3742).sum := by decide
  have hdescent : baseEnd_3742 < baseStart_3742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743 : List Nat := [1, 1, 2, 7, 1, 1, 3, 1, 2, 2, 2]
def baseStart_3743 : Nat := 118140960795 + 3743 * 2 ^ 59
def prefixEnd_3743 : Nat := 4983230072969 + 3 ^ 40 * 3743 * 2
def baseEnd_3743 : Nat := 1921958089884089195293

theorem tailTrace_3743 : CollatzResearch.WordTrace tailWord_3743 prefixEnd_3743 1921958089884089195293 := by
  unfold tailWord_3743
  simp only [CollatzResearch.WordTrace]
  refine ⟨136518425447225098615883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91012283631483399077255 136518425447225098615883)
  ·
    refine ⟨204777638170837647923825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136518425447225098615883 204777638170837647923825)
    ·
      refine ⟨153583228628128235942869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204777638170837647923825 153583228628128235942869)
      ·
        refine ⟨3599606920971755529911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 153583228628128235942869 3599606920971755529911)
        ·
          refine ⟨5399410381457633294867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3599606920971755529911 5399410381457633294867)
          ·
            refine ⟨8099115572186449942301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5399410381457633294867 8099115572186449942301)
            ·
              refine ⟨3037168339569918728363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8099115572186449942301 3037168339569918728363)
              ·
                refine ⟨4555752509354878092545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3037168339569918728363 4555752509354878092545)
                ·
                  refine ⟨3416814382016158569409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4555752509354878092545 3416814382016158569409)
                  ·
                    refine ⟨2562610786512118927057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3416814382016158569409 2562610786512118927057)
                    ·
                      refine ⟨1921958089884089195293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2562610786512118927057 1921958089884089195293)
                      ·
                        rfl

theorem cell23_3743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_3743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743 prefixEnd_3743 := by exact prefixLift 3743
  have htrace : WordTrace (prefixWord ++ tailWord_3743) baseStart_3743 baseEnd_3743 := by
    simpa [prefixWord, tailWord_3743, baseEnd_3743] using wordTrace_append hprefix tailTrace_3743
  have hstable : (prefixWord ++ tailWord_3743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743).length < 2 ^ (prefixWord ++ tailWord_3743).sum := by decide
  have hdescent : baseEnd_3743 < baseStart_3743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766 : List Nat := [5, 1, 3, 1, 1, 3, 1, 3, 5]
def baseStart_3766 : Nat := 118140960795 + 3766 * 2 ^ 59
def prefixEnd_3766 : Nat := 4983230072969 + 3 ^ 40 * 3766 * 2
def baseEnd_3766 : Nat := 214863127215277689743

theorem tailTrace_3766 : CollatzResearch.WordTrace tailWord_3766 prefixEnd_3766 214863127215277689743 := by
  unfold tailWord_3766
  simp only [CollatzResearch.WordTrace]
  refine ⟨8584831522743751668947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91571536242600017802101 8584831522743751668947)
  ·
    refine ⟨12877247284115627503421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8584831522743751668947 12877247284115627503421)
    ·
      refine ⟨4828967731543360313783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12877247284115627503421 4828967731543360313783)
      ·
        refine ⟨7243451597315040470675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4828967731543360313783 7243451597315040470675)
        ·
          refine ⟨10865177395972560706013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7243451597315040470675 10865177395972560706013)
          ·
            refine ⟨4074441523489710264755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10865177395972560706013 4074441523489710264755)
            ·
              refine ⟨6111662285234565397133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4074441523489710264755 6111662285234565397133)
              ·
                refine ⟨2291873356962962023925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6111662285234565397133 2291873356962962023925)
                ·
                  refine ⟨214863127215277689743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2291873356962962023925 214863127215277689743)
                  ·
                    rfl

theorem cell23_3766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_3766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766 prefixEnd_3766 := by exact prefixLift 3766
  have htrace : WordTrace (prefixWord ++ tailWord_3766) baseStart_3766 baseEnd_3766 := by
    simpa [prefixWord, tailWord_3766, baseEnd_3766] using wordTrace_append hprefix tailTrace_3766
  have hstable : (prefixWord ++ tailWord_3766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766).length < 2 ^ (prefixWord ++ tailWord_3766).sum := by decide
  have hdescent : baseEnd_3766 < baseStart_3766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 6]
def baseStart_3808 : Nat := 118140960795 + 3808 * 2 ^ 59
def prefixEnd_3808 : Nat := 4983230072969 + 3 ^ 40 * 3808 * 2
def baseEnd_3808 : Nat := 1955334332426334882493

theorem tailTrace_3808 : CollatzResearch.WordTrace tailWord_3808 prefixEnd_3808 1955334332426334882493 := by
  unfold tailWord_3808
  simp only [CollatzResearch.WordTrace]
  refine ⟨69444585105870599866039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92592780141160799821385 69444585105870599866039)
  ·
    refine ⟨104166877658805899799059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69444585105870599866039 104166877658805899799059)
    ·
      refine ⟨156250316488208849698589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104166877658805899799059 156250316488208849698589)
      ·
        refine ⟨58593868683078318636971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156250316488208849698589 58593868683078318636971)
        ·
          refine ⟨87890803024617477955457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58593868683078318636971 87890803024617477955457)
          ·
            refine ⟨65918102268463108466593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87890803024617477955457 65918102268463108466593)
            ·
              refine ⟨49438576701347331349945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65918102268463108466593 49438576701347331349945)
              ·
                refine ⟨37078932526010498512459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49438576701347331349945 37078932526010498512459)
                ·
                  refine ⟨55618398789015747768689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37078932526010498512459 55618398789015747768689)
                  ·
                    refine ⟨41713799091761810826517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55618398789015747768689 41713799091761810826517)
                    ·
                      refine ⟨1955334332426334882493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41713799091761810826517 1955334332426334882493)
                      ·
                        rfl

theorem cell23_3808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_3808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808 prefixEnd_3808 := by exact prefixLift 3808
  have htrace : WordTrace (prefixWord ++ tailWord_3808) baseStart_3808 baseEnd_3808 := by
    simpa [prefixWord, tailWord_3808, baseEnd_3808] using wordTrace_append hprefix tailTrace_3808
  have hstable : (prefixWord ++ tailWord_3808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808).length < 2 ^ (prefixWord ++ tailWord_3808).sum := by decide
  have hdescent : baseEnd_3808 < baseStart_3808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870 : List Nat := [4, 3, 2, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_3870 : Nat := 118140960795 + 3870 * 2 ^ 59
def prefixEnd_3870 : Nat := 4983230072969 + 3 ^ 40 * 3870 * 2
def baseEnd_3870 : Nat := 1987170133005092307209

theorem tailTrace_3870 : CollatzResearch.WordTrace tailWord_3870 prefixEnd_3870 1987170133005092307209 := by
  unfold tailWord_3870
  simp only [CollatzResearch.WordTrace]
  refine ⟨17643811998390723561133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94100330658083858992709 17643811998390723561133)
  ·
    refine ⟨6616429499396521335425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17643811998390723561133 6616429499396521335425)
    ·
      refine ⟨4962322124547391001569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6616429499396521335425 4962322124547391001569)
      ·
        refine ⟨3721741593410543251177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4962322124547391001569 3721741593410543251177)
        ·
          refine ⟨2791306195057907438383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3721741593410543251177 2791306195057907438383)
          ·
            refine ⟨4186959292586861157575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2791306195057907438383 4186959292586861157575)
            ·
              refine ⟨6280438938880291736363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4186959292586861157575 6280438938880291736363)
              ·
                refine ⟨9420658408320437604545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6280438938880291736363 9420658408320437604545)
                ·
                  refine ⟨7065493806240328203409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9420658408320437604545 7065493806240328203409)
                  ·
                    refine ⟨5299120354680246152557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7065493806240328203409 5299120354680246152557)
                    ·
                      refine ⟨1987170133005092307209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5299120354680246152557 1987170133005092307209)
                      ·
                        rfl

theorem cell23_3870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_3870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870 prefixEnd_3870 := by exact prefixLift 3870
  have htrace : WordTrace (prefixWord ++ tailWord_3870) baseStart_3870 baseEnd_3870 := by
    simpa [prefixWord, tailWord_3870, baseEnd_3870] using wordTrace_append hprefix tailTrace_3870
  have hstable : (prefixWord ++ tailWord_3870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870).length < 2 ^ (prefixWord ++ tailWord_3870).sum := by decide
  have hdescent : baseEnd_3870 < baseStart_3870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872 : List Nat := [2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 4]
def baseStart_3872 : Nat := 118140960795 + 3872 * 2 ^ 59
def prefixEnd_3872 : Nat := 4983230072969 + 3 ^ 40 * 3872 * 2
def baseEnd_3872 : Nat := 1988197094314084482199

theorem tailTrace_3872 : CollatzResearch.WordTrace tailWord_3872 prefixEnd_3872 1988197094314084482199 := by
  unfold tailWord_3872
  simp only [CollatzResearch.WordTrace]
  refine ⟨70611720989940065030935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94148961319920086707913 70611720989940065030935)
  ·
    refine ⟨105917581484910097546403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70611720989940065030935 105917581484910097546403)
    ·
      refine ⟨158876372227365146319605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105917581484910097546403 158876372227365146319605)
      ·
        refine ⟨14894659896315482467463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158876372227365146319605 14894659896315482467463)
        ·
          refine ⟨22341989844473223701195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14894659896315482467463 22341989844473223701195)
          ·
            refine ⟨33512984766709835551793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22341989844473223701195 33512984766709835551793)
            ·
              refine ⟨25134738575032376663845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33512984766709835551793 25134738575032376663845)
              ·
                refine ⟨4712763482818570624471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25134738575032376663845 4712763482818570624471)
                ·
                  refine ⟨7069145224227855936707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4712763482818570624471 7069145224227855936707)
                  ·
                    refine ⟨10603717836341783905061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7069145224227855936707 10603717836341783905061)
                    ·
                      refine ⟨1988197094314084482199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10603717836341783905061 1988197094314084482199)
                      ·
                        rfl

theorem cell23_3872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_3872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872 prefixEnd_3872 := by exact prefixLift 3872
  have htrace : WordTrace (prefixWord ++ tailWord_3872) baseStart_3872 baseEnd_3872 := by
    simpa [prefixWord, tailWord_3872, baseEnd_3872] using wordTrace_append hprefix tailTrace_3872
  have hstable : (prefixWord ++ tailWord_3872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872).length < 2 ^ (prefixWord ++ tailWord_3872).sum := by decide
  have hdescent : baseEnd_3872 < baseStart_3872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876 : List Nat := [2, 3, 1, 3, 2, 3, 1, 1, 2, 3, 2]
def baseStart_3876 : Nat := 118140960795 + 3876 * 2 ^ 59
def prefixEnd_3876 : Nat := 4983230072969 + 3 ^ 40 * 3876 * 2
def baseEnd_3876 : Nat := 1990251016932068832181

theorem tailTrace_3876 : CollatzResearch.WordTrace tailWord_3876 prefixEnd_3876 1990251016932068832181 := by
  unfold tailWord_3876
  simp only [CollatzResearch.WordTrace]
  refine ⟨70684666982694406603741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94246222643592542138321 70684666982694406603741)
  ·
    refine ⟨26506750118510402476403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70684666982694406603741 26506750118510402476403)
    ·
      refine ⟨39760125177765603714605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26506750118510402476403 39760125177765603714605)
      ·
        refine ⟨14910046941662101392977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39760125177765603714605 14910046941662101392977)
        ·
          refine ⟨11182535206246576044733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14910046941662101392977 11182535206246576044733)
          ·
            refine ⟨4193450702342466016775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11182535206246576044733 4193450702342466016775)
            ·
              refine ⟨6290176053513699025163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4193450702342466016775 6290176053513699025163)
              ·
                refine ⟨9435264080270548537745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6290176053513699025163 9435264080270548537745)
                ·
                  refine ⟨7076448060202911403309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9435264080270548537745 7076448060202911403309)
                  ·
                    refine ⟨2653668022576091776241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7076448060202911403309 2653668022576091776241)
                    ·
                      refine ⟨1990251016932068832181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2653668022576091776241 1990251016932068832181)
                      ·
                        rfl

theorem cell23_3876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_3876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876 prefixEnd_3876 := by exact prefixLift 3876
  have htrace : WordTrace (prefixWord ++ tailWord_3876) baseStart_3876 baseEnd_3876 := by
    simpa [prefixWord, tailWord_3876, baseEnd_3876] using wordTrace_append hprefix tailTrace_3876
  have hstable : (prefixWord ++ tailWord_3876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876).length < 2 ^ (prefixWord ++ tailWord_3876).sum := by decide
  have hdescent : baseEnd_3876 < baseStart_3876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889 : List Nat := [1, 2, 2, 3, 2, 2, 4, 1, 1, 1, 4]
def baseStart_3889 : Nat := 118140960795 + 3889 * 2 ^ 59
def prefixEnd_3889 : Nat := 4983230072969 + 3 ^ 40 * 3889 * 2
def baseEnd_3889 : Nat := 1996926265440517969621

theorem tailTrace_3889 : CollatzResearch.WordTrace tailWord_3889 prefixEnd_3889 1996926265440517969621 := by
  unfold tailWord_3889
  simp only [CollatzResearch.WordTrace]
  refine ⟨141843482918292033430721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94562321945528022287147 141843482918292033430721)
  ·
    refine ⟨106382612188719025073041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141843482918292033430721 106382612188719025073041)
    ·
      refine ⟨79786959141539268804781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106382612188719025073041 79786959141539268804781)
      ·
        refine ⟨29920109678077225801793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79786959141539268804781 29920109678077225801793)
        ·
          refine ⟨22440082258557919351345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29920109678077225801793 22440082258557919351345)
          ·
            refine ⟨16830061693918439513509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22440082258557919351345 16830061693918439513509)
            ·
              refine ⟨3155636567609707408783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16830061693918439513509 3155636567609707408783)
              ·
                refine ⟨4733454851414561113175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3155636567609707408783 4733454851414561113175)
                ·
                  refine ⟨7100182277121841669763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4733454851414561113175 7100182277121841669763)
                  ·
                    refine ⟨10650273415682762504645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7100182277121841669763 10650273415682762504645)
                    ·
                      refine ⟨1996926265440517969621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10650273415682762504645 1996926265440517969621)
                      ·
                        rfl

theorem cell23_3889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_3889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3889 prefixEnd_3889 := by exact prefixLift 3889
  have htrace : WordTrace (prefixWord ++ tailWord_3889) baseStart_3889 baseEnd_3889 := by
    simpa [prefixWord, tailWord_3889, baseEnd_3889] using wordTrace_append hprefix tailTrace_3889
  have hstable : (prefixWord ++ tailWord_3889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889).length < 2 ^ (prefixWord ++ tailWord_3889).sum := by decide
  have hdescent : baseEnd_3889 < baseStart_3889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916 : List Nat := [2, 2, 1, 3, 4, 1, 3, 1, 2, 4]
def baseStart_3916 : Nat := 118140960795 + 3916 * 2 ^ 59
def prefixEnd_3916 : Nat := 4983230072969 + 3 ^ 40 * 3916 * 2
def baseEnd_3916 : Nat := 670263414370637443999

theorem tailTrace_3916 : CollatzResearch.WordTrace tailWord_3916 prefixEnd_3916 670263414370637443999 := by
  unfold tailWord_3916
  simp only [CollatzResearch.WordTrace]
  refine ⟨71414126910237822331801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95218835880317096442401 71414126910237822331801)
  ·
    refine ⟨53560595182678366748851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71414126910237822331801 53560595182678366748851)
    ·
      refine ⟨80340892774017550123277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53560595182678366748851 80340892774017550123277)
      ·
        refine ⟨30127834790256581296229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80340892774017550123277 30127834790256581296229)
        ·
          refine ⟨5648969023173108993043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30127834790256581296229 5648969023173108993043)
          ·
            refine ⟨8473453534759663489565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5648969023173108993043 8473453534759663489565)
            ·
              refine ⟨3177545075534873808587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8473453534759663489565 3177545075534873808587)
              ·
                refine ⟨4766317613302310712881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3177545075534873808587 4766317613302310712881)
                ·
                  refine ⟨3574738209976733034661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4766317613302310712881 3574738209976733034661)
                  ·
                    refine ⟨670263414370637443999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3574738209976733034661 670263414370637443999)
                    ·
                      rfl

theorem cell23_3916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 2, 4].length) (baseStart_3916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3916 prefixEnd_3916 := by exact prefixLift 3916
  have htrace : WordTrace (prefixWord ++ tailWord_3916) baseStart_3916 baseEnd_3916 := by
    simpa [prefixWord, tailWord_3916, baseEnd_3916] using wordTrace_append hprefix tailTrace_3916
  have hstable : (prefixWord ++ tailWord_3916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916).length < 2 ^ (prefixWord ++ tailWord_3916).sum := by decide
  have hdescent : baseEnd_3916 < baseStart_3916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 5]
def baseStart_3935 : Nat := 118140960795 + 3935 * 2 ^ 59
def prefixEnd_3935 : Nat := 4983230072969 + 3 ^ 40 * 3935 * 2
def baseEnd_3935 : Nat := 2020546375547337994409

theorem tailTrace_3935 : CollatzResearch.WordTrace tailWord_3935 prefixEnd_3935 2020546375547337994409 := by
  unfold tailWord_3935
  simp only [CollatzResearch.WordTrace]
  refine ⟨143521240751641889605259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95680827167761259736839 143521240751641889605259)
  ·
    refine ⟨215281861127462834407889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143521240751641889605259 215281861127462834407889)
    ·
      refine ⟨161461395845597125805917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215281861127462834407889 161461395845597125805917)
      ·
        refine ⟨60548023442098922177219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161461395845597125805917 60548023442098922177219)
        ·
          refine ⟨90822035163148383265829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60548023442098922177219 90822035163148383265829)
          ·
            refine ⟨17029131593090321862343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90822035163148383265829 17029131593090321862343)
            ·
              refine ⟨25543697389635482793515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17029131593090321862343 25543697389635482793515)
              ·
                refine ⟨38315546084453224190273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25543697389635482793515 38315546084453224190273)
                ·
                  refine ⟨28736659563339918142705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38315546084453224190273 28736659563339918142705)
                  ·
                    refine ⟨21552494672504938607029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28736659563339918142705 21552494672504938607029)
                    ·
                      refine ⟨2020546375547337994409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21552494672504938607029 2020546375547337994409)
                      ·
                        rfl

theorem cell23_3935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_3935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3935 prefixEnd_3935 := by exact prefixLift 3935
  have htrace : WordTrace (prefixWord ++ tailWord_3935) baseStart_3935 baseEnd_3935 := by
    simpa [prefixWord, tailWord_3935, baseEnd_3935] using wordTrace_append hprefix tailTrace_3935
  have hstable : (prefixWord ++ tailWord_3935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935).length < 2 ^ (prefixWord ++ tailWord_3935).sum := by decide
  have hdescent : baseEnd_3935 < baseStart_3935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940 : List Nat := [2, 3, 1, 1, 5, 2, 1, 3, 1, 2, 2]
def baseStart_3940 : Nat := 118140960795 + 3940 * 2 ^ 59
def prefixEnd_3940 : Nat := 4983230072969 + 3 ^ 40 * 3940 * 2
def baseEnd_3940 : Nat := 2023113778819818431887

theorem tailTrace_3940 : CollatzResearch.WordTrace tailWord_3940 prefixEnd_3940 2023113778819818431887 := by
  unfold tailWord_3940
  simp only [CollatzResearch.WordTrace]
  refine ⟨71851802866763871768637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95802403822351829024849 71851802866763871768637)
  ·
    refine ⟨26944426075036451913239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71851802866763871768637 26944426075036451913239)
    ·
      refine ⟨40416639112554677869859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26944426075036451913239 40416639112554677869859)
      ·
        refine ⟨60624958668832016804789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40416639112554677869859 60624958668832016804789)
        ·
          refine ⟨5683589875203001575449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60624958668832016804789 5683589875203001575449)
          ·
            refine ⟨4262692406402251181587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5683589875203001575449 4262692406402251181587)
            ·
              refine ⟨6394038609603376772381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4262692406402251181587 6394038609603376772381)
              ·
                refine ⟨2397764478601266289643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6394038609603376772381 2397764478601266289643)
                ·
                  refine ⟨3596646717901899434465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2397764478601266289643 3596646717901899434465)
                  ·
                    refine ⟨2697485038426424575849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3596646717901899434465 2697485038426424575849)
                    ·
                      refine ⟨2023113778819818431887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2697485038426424575849 2023113778819818431887)
                      ·
                        rfl

theorem cell23_3940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 1, 2, 2].length) (baseStart_3940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940 prefixEnd_3940 := by exact prefixLift 3940
  have htrace : WordTrace (prefixWord ++ tailWord_3940) baseStart_3940 baseEnd_3940 := by
    simpa [prefixWord, tailWord_3940, baseEnd_3940] using wordTrace_append hprefix tailTrace_3940
  have hstable : (prefixWord ++ tailWord_3940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940).length < 2 ^ (prefixWord ++ tailWord_3940).sum := by decide
  have hdescent : baseEnd_3940 < baseStart_3940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 3, 3, 5]
def baseStart_3965 : Nat := 118140960795 + 3965 * 2 ^ 59
def prefixEnd_3965 : Nat := 4983230072969 + 3 ^ 40 * 3965 * 2
def baseEnd_3965 : Nat := 2035950795182220619271

theorem tailTrace_3965 : CollatzResearch.WordTrace tailWord_3965 prefixEnd_3965 2035950795182220619271 := by
  unfold tailWord_3965
  simp only [CollatzResearch.WordTrace]
  refine ⟨144615430642957013197349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96410287095304675464899 144615430642957013197349)
  ·
    refine ⟨27115393245554439974503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144615430642957013197349 27115393245554439974503)
    ·
      refine ⟨40673089868331659961755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27115393245554439974503 40673089868331659961755)
      ·
        refine ⟨61009634802497489942633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40673089868331659961755 61009634802497489942633)
        ·
          refine ⟨45757226101873117456975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61009634802497489942633 45757226101873117456975)
          ·
            refine ⟨68635839152809676185463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45757226101873117456975 68635839152809676185463)
            ·
              refine ⟨102953758729214514278195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68635839152809676185463 102953758729214514278195)
              ·
                refine ⟨154430638093821771417293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102953758729214514278195 154430638093821771417293)
                ·
                  refine ⟨57911489285183164281485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154430638093821771417293 57911489285183164281485)
                  ·
                    refine ⟨21716808481943686605557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57911489285183164281485 21716808481943686605557)
                    ·
                      refine ⟨2035950795182220619271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21716808481943686605557 2035950795182220619271)
                      ·
                        rfl

theorem cell23_3965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_3965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965 prefixEnd_3965 := by exact prefixLift 3965
  have htrace : WordTrace (prefixWord ++ tailWord_3965) baseStart_3965 baseEnd_3965 := by
    simpa [prefixWord, tailWord_3965, baseEnd_3965] using wordTrace_append hprefix tailTrace_3965
  have hstable : (prefixWord ++ tailWord_3965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965).length < 2 ^ (prefixWord ++ tailWord_3965).sum := by decide
  have hdescent : baseEnd_3965 < baseStart_3965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985 : List Nat := [1, 2, 2, 1, 1, 1, 4, 4, 7]
def baseStart_3985 : Nat := 118140960795 + 3985 * 2 ^ 59
def prefixEnd_3985 : Nat := 4983230072969 + 3 ^ 40 * 3985 * 2
def baseEnd_3985 : Nat := 227357823141349152131

theorem tailTrace_3985 : CollatzResearch.WordTrace tailWord_3985 prefixEnd_3985 227357823141349152131 := by
  unfold tailWord_3985
  simp only [CollatzResearch.WordTrace]
  refine ⟨145344890570500428925409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96896593713666952616939 145344890570500428925409)
  ·
    refine ⟨109008667927875321694057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145344890570500428925409 109008667927875321694057)
    ·
      refine ⟨81756500945906491270543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109008667927875321694057 81756500945906491270543)
      ·
        refine ⟨122634751418859736905815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81756500945906491270543 122634751418859736905815)
        ·
          refine ⟨183952127128289605358723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122634751418859736905815 183952127128289605358723)
          ·
            refine ⟨275928190692434408038085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183952127128289605358723 275928190692434408038085)
            ·
              refine ⟨51736535754831451507141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 275928190692434408038085 51736535754831451507141)
              ·
                refine ⟨9700600454030897157589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51736535754831451507141 9700600454030897157589)
                ·
                  refine ⟨227357823141349152131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9700600454030897157589 227357823141349152131)
                  ·
                    rfl

theorem cell23_3985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 7].length) (baseStart_3985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985 prefixEnd_3985 := by exact prefixLift 3985
  have htrace : WordTrace (prefixWord ++ tailWord_3985) baseStart_3985 baseEnd_3985 := by
    simpa [prefixWord, tailWord_3985, baseEnd_3985] using wordTrace_append hprefix tailTrace_3985
  have hstable : (prefixWord ++ tailWord_3985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985).length < 2 ^ (prefixWord ++ tailWord_3985).sum := by decide
  have hdescent : baseEnd_3985 < baseStart_3985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996 : List Nat := [2, 2, 3, 3, 1, 2, 1, 2, 1, 4, 2]
def baseStart_3996 : Nat := 118140960795 + 3996 * 2 ^ 59
def prefixEnd_3996 : Nat := 4983230072969 + 3 ^ 40 * 3996 * 2
def baseEnd_3996 : Nat := 2051868695471599331629

theorem tailTrace_3996 : CollatzResearch.WordTrace tailWord_3996 prefixEnd_3996 2051868695471599331629 := by
  unfold tailWord_3996
  simp only [CollatzResearch.WordTrace]
  refine ⟨72873046765324653787921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97164062353766205050561 72873046765324653787921)
  ·
    refine ⟨54654785073993490340941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72873046765324653787921 54654785073993490340941)
    ·
      refine ⟨20495544402747558877853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54654785073993490340941 20495544402747558877853)
      ·
        refine ⟨7685829151030334579195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20495544402747558877853 7685829151030334579195)
        ·
          refine ⟨11528743726545501868793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7685829151030334579195 11528743726545501868793)
          ·
            refine ⟨8646557794909126401595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11528743726545501868793 8646557794909126401595)
            ·
              refine ⟨12969836692363689602393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8646557794909126401595 12969836692363689602393)
              ·
                refine ⟨9727377519272767201795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12969836692363689602393 9727377519272767201795)
                ·
                  refine ⟨14591066278909150802693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9727377519272767201795 14591066278909150802693)
                  ·
                    refine ⟨2735824927295465775505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14591066278909150802693 2735824927295465775505)
                    ·
                      refine ⟨2051868695471599331629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2735824927295465775505 2051868695471599331629)
                      ·
                        rfl

theorem cell23_3996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_3996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996 prefixEnd_3996 := by exact prefixLift 3996
  have htrace : WordTrace (prefixWord ++ tailWord_3996) baseStart_3996 baseEnd_3996 := by
    simpa [prefixWord, tailWord_3996, baseEnd_3996] using wordTrace_append hprefix tailTrace_3996
  have hstable : (prefixWord ++ tailWord_3996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996).length < 2 ^ (prefixWord ++ tailWord_3996).sum := by decide
  have hdescent : baseEnd_3996 < baseStart_3996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 2, 3, 3]
def baseStart_4029 : Nat := 118140960795 + 4029 * 2 ^ 59
def prefixEnd_4029 : Nat := 4983230072969 + 3 ^ 40 * 4029 * 2
def baseEnd_4029 : Nat := 2068813557069970218977

theorem tailTrace_4029 : CollatzResearch.WordTrace tailWord_4029 prefixEnd_4029 2068813557069970218977 := by
  unfold tailWord_4029
  simp only [CollatzResearch.WordTrace]
  refine ⟨146949702411095943527141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97966468274063962351427 146949702411095943527141)
  ·
    refine ⟨27553069202080489411339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146949702411095943527141 27553069202080489411339)
    ·
      refine ⟨41329603803120734117009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27553069202080489411339 41329603803120734117009)
      ·
        refine ⟨30997202852340550587757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41329603803120734117009 30997202852340550587757)
        ·
          refine ⟨11623951069627706470409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30997202852340550587757 11623951069627706470409)
          ·
            refine ⟨8717963302220779852807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11623951069627706470409 8717963302220779852807)
            ·
              refine ⟨13076944953331169779211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8717963302220779852807 13076944953331169779211)
              ·
                refine ⟨19615417429996754668817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13076944953331169779211 19615417429996754668817)
                ·
                  refine ⟨14711563072497566001613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19615417429996754668817 14711563072497566001613)
                  ·
                    refine ⟨5516836152186587250605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14711563072497566001613 5516836152186587250605)
                    ·
                      refine ⟨2068813557069970218977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5516836152186587250605 2068813557069970218977)
                      ·
                        rfl

theorem cell23_4029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_4029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029 prefixEnd_4029 := by exact prefixLift 4029
  have htrace : WordTrace (prefixWord ++ tailWord_4029) baseStart_4029 baseEnd_4029 := by
    simpa [prefixWord, tailWord_4029, baseEnd_4029] using wordTrace_append hprefix tailTrace_4029
  have hstable : (prefixWord ++ tailWord_4029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029).length < 2 ^ (prefixWord ++ tailWord_4029).sum := by decide
  have hdescent : baseEnd_4029 < baseStart_4029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079 : List Nat := [1, 1, 2, 1, 4, 2, 4, 1, 3, 4]
def baseStart_4079 : Nat := 118140960795 + 4079 * 2 ^ 59
def prefixEnd_4079 : Nat := 4983230072969 + 3 ^ 40 * 4079 * 2
def baseEnd_4079 : Nat := 698162529931591531249

theorem tailTrace_4079 : CollatzResearch.WordTrace tailWord_4079 prefixEnd_4079 698162529931591531249 := by
  unfold tailWord_4079
  simp only [CollatzResearch.WordTrace]
  refine ⟨148773352229954482847291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99182234819969655231527 148773352229954482847291)
  ·
    refine ⟨223160028344931724270937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148773352229954482847291 223160028344931724270937)
    ·
      refine ⟨167370021258698793203203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223160028344931724270937 167370021258698793203203)
      ·
        refine ⟨251055031888048189804805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167370021258698793203203 251055031888048189804805)
        ·
          refine ⟨47072818479009035588401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251055031888048189804805 47072818479009035588401)
          ·
            refine ⟨35304613859256776691301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47072818479009035588401 35304613859256776691301)
            ·
              refine ⟨6619615098610645629619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35304613859256776691301 6619615098610645629619)
              ·
                refine ⟨9929422647915968444429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6619615098610645629619 9929422647915968444429)
                ·
                  refine ⟨3723533492968488166661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9929422647915968444429 3723533492968488166661)
                  ·
                    refine ⟨698162529931591531249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3723533492968488166661 698162529931591531249)
                    ·
                      rfl

theorem cell23_4079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 4].length) (baseStart_4079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079 prefixEnd_4079 := by exact prefixLift 4079
  have htrace : WordTrace (prefixWord ++ tailWord_4079) baseStart_4079 baseEnd_4079 := by
    simpa [prefixWord, tailWord_4079, baseEnd_4079] using wordTrace_append hprefix tailTrace_4079
  have hstable : (prefixWord ++ tailWord_4079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079).length < 2 ^ (prefixWord ++ tailWord_4079).sum := by decide
  have hdescent : baseEnd_4079 < baseStart_4079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 2, 6, 2]
def baseStart_4159 : Nat := 118140960795 + 4159 * 2 ^ 59
def prefixEnd_4159 : Nat := 4983230072969 + 3 ^ 40 * 4159 * 2
def baseEnd_4159 : Nat := 2135566042154461593379

theorem tailTrace_4159 : CollatzResearch.WordTrace tailWord_4159 prefixEnd_4159 2135566042154461593379 := by
  unfold tailWord_4159
  simp only [CollatzResearch.WordTrace]
  refine ⟨151691191940128145759531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101127461293418763839687 151691191940128145759531)
  ·
    refine ⟨227536787910192218639297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151691191940128145759531 227536787910192218639297)
    ·
      refine ⟨170652590932644163979473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227536787910192218639297 170652590932644163979473)
      ·
        refine ⟨127989443199483122984605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170652590932644163979473 127989443199483122984605)
        ·
          refine ⟨47996041199806171119227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127989443199483122984605 47996041199806171119227)
          ·
            refine ⟨71994061799709256678841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47996041199806171119227 71994061799709256678841)
            ·
              refine ⟨53995546349781942509131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71994061799709256678841 53995546349781942509131)
              ·
                refine ⟨80993319524672913763697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53995546349781942509131 80993319524672913763697)
                ·
                  refine ⟨60744989643504685322773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80993319524672913763697 60744989643504685322773)
                  ·
                    refine ⟨2847421389539282124505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 60744989643504685322773 2847421389539282124505)
                    ·
                      refine ⟨2135566042154461593379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2847421389539282124505 2135566042154461593379)
                      ·
                        rfl

theorem cell23_4159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 6, 2].length) (baseStart_4159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159 prefixEnd_4159 := by exact prefixLift 4159
  have htrace : WordTrace (prefixWord ++ tailWord_4159) baseStart_4159 baseEnd_4159 := by
    simpa [prefixWord, tailWord_4159, baseEnd_4159] using wordTrace_append hprefix tailTrace_4159
  have hstable : (prefixWord ++ tailWord_4159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159).length < 2 ^ (prefixWord ++ tailWord_4159).sum := by decide
  have hdescent : baseEnd_4159 < baseStart_4159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173 : List Nat := [1, 6, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_4173 : Nat := 118140960795 + 4173 * 2 ^ 59
def prefixEnd_4173 : Nat := 4983230072969 + 3 ^ 40 * 4173 * 2
def baseEnd_4173 : Nat := 714251590439135606105

theorem tailTrace_4173 : CollatzResearch.WordTrace tailWord_4173 prefixEnd_4173 714251590439135606105 := by
  unfold tailWord_4173
  simp only [CollatzResearch.WordTrace]
  refine ⟨152201813889408536769173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101467875926272357846115 152201813889408536769173)
  ·
    refine ⟨7134460026066025161055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152201813889408536769173 7134460026066025161055)
    ·
      refine ⟨10701690039099037741583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7134460026066025161055 10701690039099037741583)
      ·
        refine ⟨16052535058648556612375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10701690039099037741583 16052535058648556612375)
        ·
          refine ⟨24078802587972834918563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16052535058648556612375 24078802587972834918563)
          ·
            refine ⟨36118203881959252377845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24078802587972834918563 36118203881959252377845)
            ·
              refine ⟨3386081613933679910423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36118203881959252377845 3386081613933679910423)
              ·
                refine ⟨5079122420900519865635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3386081613933679910423 5079122420900519865635)
                ·
                  refine ⟨7618683631350779798453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5079122420900519865635 7618683631350779798453)
                  ·
                    refine ⟨714251590439135606105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7618683631350779798453 714251590439135606105)
                    ·
                      rfl

theorem cell23_4173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_4173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173 prefixEnd_4173 := by exact prefixLift 4173
  have htrace : WordTrace (prefixWord ++ tailWord_4173) baseStart_4173 baseEnd_4173 := by
    simpa [prefixWord, tailWord_4173, baseEnd_4173] using wordTrace_append hprefix tailTrace_4173
  have hstable : (prefixWord ++ tailWord_4173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173).length < 2 ^ (prefixWord ++ tailWord_4173).sum := by decide
  have hdescent : baseEnd_4173 < baseStart_4173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186 : List Nat := [3, 1, 1, 2, 1, 1, 6, 2, 2, 4]
def baseStart_4186 : Nat := 118140960795 + 4186 * 2 ^ 59
def prefixEnd_4186 : Nat := 4983230072969 + 3 ^ 40 * 4186 * 2
def baseEnd_4186 : Nat := 716476673275285318585

theorem tailTrace_4186 : CollatzResearch.WordTrace tailWord_4186 prefixEnd_4186 716476673275285318585 := by
  unfold tailWord_4186
  simp only [CollatzResearch.WordTrace]
  refine ⟨38168990710577939248103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101783975228207837994941 38168990710577939248103)
  ·
    refine ⟨57253486065866908872155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38168990710577939248103 57253486065866908872155)
    ·
      refine ⟨85880229098800363308233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57253486065866908872155 85880229098800363308233)
      ·
        refine ⟨64410171824100272481175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85880229098800363308233 64410171824100272481175)
        ·
          refine ⟨96615257736150408721763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64410171824100272481175 96615257736150408721763)
          ·
            refine ⟨144922886604225613082645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96615257736150408721763 144922886604225613082645)
            ·
              refine ⟨6793260309573075613249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144922886604225613082645 6793260309573075613249)
              ·
                refine ⟨5094945232179806709937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6793260309573075613249 5094945232179806709937)
                ·
                  refine ⟨3821208924134855032453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5094945232179806709937 3821208924134855032453)
                  ·
                    refine ⟨716476673275285318585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3821208924134855032453 716476673275285318585)
                    ·
                      rfl

theorem cell23_4186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 2, 4].length) (baseStart_4186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186 prefixEnd_4186 := by exact prefixLift 4186
  have htrace : WordTrace (prefixWord ++ tailWord_4186) baseStart_4186 baseEnd_4186 := by
    simpa [prefixWord, tailWord_4186, baseEnd_4186] using wordTrace_append hprefix tailTrace_4186
  have hstable : (prefixWord ++ tailWord_4186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186).length < 2 ^ (prefixWord ++ tailWord_4186).sum := by decide
  have hdescent : baseEnd_4186 < baseStart_4186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206 : List Nat := [4, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4]
def baseStart_4206 : Nat := 118140960795 + 4206 * 2 ^ 59
def prefixEnd_4206 : Nat := 4983230072969 + 3 ^ 40 * 4206 * 2
def baseEnd_4206 : Nat := 2159699632915777705663

theorem tailTrace_4206 : CollatzResearch.WordTrace tailWord_4206 prefixEnd_4206 2159699632915777705663 := by
  unfold tailWord_4206
  simp only [CollatzResearch.WordTrace]
  refine ⟨19175677846231896590059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102270281846570115146981 19175677846231896590059)
  ·
    refine ⟨28763516769347844885089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19175677846231896590059 28763516769347844885089)
    ·
      refine ⟨21572637577010883663817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28763516769347844885089 21572637577010883663817)
      ·
        refine ⟨16179478182758162747863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21572637577010883663817 16179478182758162747863)
        ·
          refine ⟨24269217274137244121795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16179478182758162747863 24269217274137244121795)
          ·
            refine ⟨36403825911205866182693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24269217274137244121795 36403825911205866182693)
            ·
              refine ⟨6825717358351099909255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36403825911205866182693 6825717358351099909255)
              ·
                refine ⟨10238576037526649863883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6825717358351099909255 10238576037526649863883)
                ·
                  refine ⟨15357864056289974795825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10238576037526649863883 15357864056289974795825)
                  ·
                    refine ⟨11518398042217481096869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15357864056289974795825 11518398042217481096869)
                    ·
                      refine ⟨2159699632915777705663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11518398042217481096869 2159699632915777705663)
                      ·
                        rfl

theorem cell23_4206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_4206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206 prefixEnd_4206 := by exact prefixLift 4206
  have htrace : WordTrace (prefixWord ++ tailWord_4206) baseStart_4206 baseEnd_4206 := by
    simpa [prefixWord, tailWord_4206, baseEnd_4206] using wordTrace_append hprefix tailTrace_4206
  have hstable : (prefixWord ++ tailWord_4206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206).length < 2 ^ (prefixWord ++ tailWord_4206).sum := by decide
  have hdescent : baseEnd_4206 < baseStart_4206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260 : List Nat := [2, 3, 1, 2, 5, 1, 1, 1, 1, 3, 3]
def baseStart_4260 : Nat := 118140960795 + 4260 * 2 ^ 59
def prefixEnd_4260 : Nat := 4983230072969 + 3 ^ 40 * 4260 * 2
def baseEnd_4260 : Nat := 2187427588258566430415

theorem tailTrace_4260 : CollatzResearch.WordTrace tailWord_4260 prefixEnd_4260 2187427588258566430415 := by
  unfold tailWord_4260
  simp only [CollatzResearch.WordTrace]
  refine ⟨77687482287111197593117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103583309716148263457489 77687482287111197593117)
  ·
    refine ⟨29132805857666699097419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77687482287111197593117 29132805857666699097419)
    ·
      refine ⟨43699208786500048646129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29132805857666699097419 43699208786500048646129)
      ·
        refine ⟨32774406589875036484597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43699208786500048646129 32774406589875036484597)
        ·
          refine ⟨3072600617800784670431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32774406589875036484597 3072600617800784670431)
          ·
            refine ⟨4608900926701177005647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3072600617800784670431 4608900926701177005647)
            ·
              refine ⟨6913351390051765508471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4608900926701177005647 6913351390051765508471)
              ·
                refine ⟨10370027085077648262707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6913351390051765508471 10370027085077648262707)
                ·
                  refine ⟨15555040627616472394061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10370027085077648262707 15555040627616472394061)
                  ·
                    refine ⟨5833140235356177147773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15555040627616472394061 5833140235356177147773)
                    ·
                      refine ⟨2187427588258566430415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5833140235356177147773 2187427588258566430415)
                      ·
                        rfl

theorem cell23_4260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_4260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260 prefixEnd_4260 := by exact prefixLift 4260
  have htrace : WordTrace (prefixWord ++ tailWord_4260) baseStart_4260 baseEnd_4260 := by
    simpa [prefixWord, tailWord_4260, baseEnd_4260] using wordTrace_append hprefix tailTrace_4260
  have hstable : (prefixWord ++ tailWord_4260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260).length < 2 ^ (prefixWord ++ tailWord_4260).sum := by decide
  have hdescent : baseEnd_4260 < baseStart_4260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306 : List Nat := [3, 2, 2, 2, 1, 2, 3, 1, 7]
def baseStart_4306 : Nat := 118140960795 + 4306 * 2 ^ 59
def prefixEnd_4306 : Nat := 4983230072969 + 3 ^ 40 * 4306 * 2
def baseEnd_4306 : Nat := 245671966485042939467

theorem tailTrace_4306 : CollatzResearch.WordTrace tailWord_4306 prefixEnd_4306 245671966485042939467 := by
  unfold tailWord_4306
  simp only [CollatzResearch.WordTrace]
  refine ⟨39263180601893062840193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104701814938381500907181 39263180601893062840193)
  ·
    refine ⟨29447385451419797130145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39263180601893062840193 29447385451419797130145)
    ·
      refine ⟨22085539088564847847609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29447385451419797130145 22085539088564847847609)
      ·
        refine ⟨16564154316423635885707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22085539088564847847609 16564154316423635885707)
        ·
          refine ⟨24846231474635453828561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16564154316423635885707 24846231474635453828561)
          ·
            refine ⟨18634673605976590371421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24846231474635453828561 18634673605976590371421)
            ·
              refine ⟨6988002602241221389283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18634673605976590371421 6988002602241221389283)
              ·
                refine ⟨10482003903361832083925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6988002602241221389283 10482003903361832083925)
                ·
                  refine ⟨245671966485042939467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10482003903361832083925 245671966485042939467)
                  ·
                    rfl

theorem cell23_4306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_4306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306 prefixEnd_4306 := by exact prefixLift 4306
  have htrace : WordTrace (prefixWord ++ tailWord_4306) baseStart_4306 baseEnd_4306 := by
    simpa [prefixWord, tailWord_4306, baseEnd_4306] using wordTrace_append hprefix tailTrace_4306
  have hstable : (prefixWord ++ tailWord_4306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306).length < 2 ^ (prefixWord ++ tailWord_4306).sum := by decide
  have hdescent : baseEnd_4306 < baseStart_4306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317 : List Nat := [1, 4, 3, 2, 1, 2, 1, 3, 2, 2, 2]
def baseStart_4317 : Nat := 118140960795 + 4317 * 2 ^ 59
def prefixEnd_4317 : Nat := 4983230072969 + 3 ^ 40 * 4317 * 2
def baseEnd_4317 : Nat := 2216695985564843417653

theorem tailTrace_4317 : CollatzResearch.WordTrace tailWord_4317 prefixEnd_4317 2216695985564843417653 := by
  unfold tailWord_4317
  simp only [CollatzResearch.WordTrace]
  refine ⟨157453925367721130011205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104969283578480753340803 157453925367721130011205)
  ·
    refine ⟨29522611006447711877101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157453925367721130011205 29522611006447711877101)
    ·
      refine ⟨11070979127417891953913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29522611006447711877101 11070979127417891953913)
      ·
        refine ⟨8303234345563418965435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11070979127417891953913 8303234345563418965435)
        ·
          refine ⟨12454851518345128448153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8303234345563418965435 12454851518345128448153)
          ·
            refine ⟨9341138638758846336115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12454851518345128448153 9341138638758846336115)
            ·
              refine ⟨14011707958138269504173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9341138638758846336115 14011707958138269504173)
              ·
                refine ⟨5254390484301851064065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14011707958138269504173 5254390484301851064065)
                ·
                  refine ⟨3940792863226388298049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5254390484301851064065 3940792863226388298049)
                  ·
                    refine ⟨2955594647419791223537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3940792863226388298049 2955594647419791223537)
                    ·
                      refine ⟨2216695985564843417653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2955594647419791223537 2216695985564843417653)
                      ·
                        rfl

theorem cell23_4317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_4317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317 prefixEnd_4317 := by exact prefixLift 4317
  have htrace : WordTrace (prefixWord ++ tailWord_4317) baseStart_4317 baseEnd_4317 := by
    simpa [prefixWord, tailWord_4317, baseEnd_4317] using wordTrace_append hprefix tailTrace_4317
  have hstable : (prefixWord ++ tailWord_4317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317).length < 2 ^ (prefixWord ++ tailWord_4317).sum := by decide
  have hdescent : baseEnd_4317 < baseStart_4317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4319 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 6, 5]
def baseStart_4319 : Nat := 118140960795 + 4319 * 2 ^ 59
def prefixEnd_4319 : Nat := 4983230072969 + 3 ^ 40 * 4319 * 2
def baseEnd_4319 : Nat := 739240982291278530881

theorem tailTrace_4319 : CollatzResearch.WordTrace tailWord_4319 prefixEnd_4319 739240982291278530881 := by
  unfold tailWord_4319
  simp only [CollatzResearch.WordTrace]
  refine ⟨157526871360475471584011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105017914240316981056007 157526871360475471584011)
  ·
    refine ⟨236290307040713207376017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157526871360475471584011 236290307040713207376017)
    ·
      refine ⟨177217730280534905532013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236290307040713207376017 177217730280534905532013)
      ·
        refine ⟨66456648855200589574505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177217730280534905532013 66456648855200589574505)
        ·
          refine ⟨49842486641400442180879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66456648855200589574505 49842486641400442180879)
          ·
            refine ⟨74763729962100663271319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49842486641400442180879 74763729962100663271319)
            ·
              refine ⟨112145594943150994906979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74763729962100663271319 112145594943150994906979)
              ·
                refine ⟨168218392414726492360469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112145594943150994906979 168218392414726492360469)
                ·
                  refine ⟨7885237144440304329397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 168218392414726492360469 7885237144440304329397)
                  ·
                    refine ⟨739240982291278530881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7885237144440304329397 739240982291278530881)
                    ·
                      rfl

theorem cell23_4319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 5].length) (baseStart_4319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4319 prefixEnd_4319 := by exact prefixLift 4319
  have htrace : WordTrace (prefixWord ++ tailWord_4319) baseStart_4319 baseEnd_4319 := by
    simpa [prefixWord, tailWord_4319, baseEnd_4319] using wordTrace_append hprefix tailTrace_4319
  have hstable : (prefixWord ++ tailWord_4319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4319).length < 2 ^ (prefixWord ++ tailWord_4319).sum := by decide
  have hdescent : baseEnd_4319 < baseStart_4319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 1, 4, 3]
def baseStart_4376 : Nat := 118140960795 + 4376 * 2 ^ 59
def prefixEnd_4376 : Nat := 4983230072969 + 3 ^ 40 * 4376 * 2
def baseEnd_4376 : Nat := 2246991344180112579881

theorem tailTrace_4376 : CollatzResearch.WordTrace tailWord_4376 prefixEnd_4376 2246991344180112579881 := by
  unfold tailWord_4376
  simp only [CollatzResearch.WordTrace]
  refine ⟨79802916076987103204491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106403888102649470939321 79802916076987103204491)
  ·
    refine ⟨119704374115480654806737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79802916076987103204491 119704374115480654806737)
    ·
      refine ⟨89778280586610491105053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119704374115480654806737 89778280586610491105053)
      ·
        refine ⟨33666855219978934164395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89778280586610491105053 33666855219978934164395)
        ·
          refine ⟨50500282829968401246593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33666855219978934164395 50500282829968401246593)
          ·
            refine ⟨37875212122476300934945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50500282829968401246593 37875212122476300934945)
            ·
              refine ⟨28406409091857225701209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37875212122476300934945 28406409091857225701209)
              ·
                refine ⟨21304806818892919275907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28406409091857225701209 21304806818892919275907)
                ·
                  refine ⟨31957210228339378913861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21304806818892919275907 31957210228339378913861)
                  ·
                    refine ⟨5991976917813633546349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31957210228339378913861 5991976917813633546349)
                    ·
                      refine ⟨2246991344180112579881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5991976917813633546349 2246991344180112579881)
                      ·
                        rfl

theorem cell23_4376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_4376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376 prefixEnd_4376 := by exact prefixLift 4376
  have htrace : WordTrace (prefixWord ++ tailWord_4376) baseStart_4376 baseEnd_4376 := by
    simpa [prefixWord, tailWord_4376, baseEnd_4376] using wordTrace_append hprefix tailTrace_4376
  have hstable : (prefixWord ++ tailWord_4376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376).length < 2 ^ (prefixWord ++ tailWord_4376).sum := by decide
  have hdescent : baseEnd_4376 < baseStart_4376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383 : List Nat := [1, 1, 2, 4, 3, 2, 1, 2, 3, 4]
def baseStart_4383 : Nat := 118140960795 + 4383 * 2 ^ 59
def prefixEnd_4383 : Nat := 4983230072969 + 3 ^ 40 * 4383 * 2
def baseEnd_4383 : Nat := 750195236253861730783

theorem tailTrace_4383 : CollatzResearch.WordTrace tailWord_4383 prefixEnd_4383 750195236253861730783 := by
  unfold tailWord_4383
  simp only [CollatzResearch.WordTrace]
  refine ⟨159861143128614401913803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106574095419076267942535 159861143128614401913803)
  ·
    refine ⟨239791714692921602870705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159861143128614401913803 239791714692921602870705)
    ·
      refine ⟨179843786019691202153029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239791714692921602870705 179843786019691202153029)
      ·
        refine ⟨33720709878692100403693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179843786019691202153029 33720709878692100403693)
        ·
          refine ⟨12645266204509537651385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33720709878692100403693 12645266204509537651385)
          ·
            refine ⟨9483949653382153238539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12645266204509537651385 9483949653382153238539)
            ·
              refine ⟨14225924480073229857809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9483949653382153238539 14225924480073229857809)
              ·
                refine ⟨10669443360054922393357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14225924480073229857809 10669443360054922393357)
                ·
                  refine ⟨4001041260020595897509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10669443360054922393357 4001041260020595897509)
                  ·
                    refine ⟨750195236253861730783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4001041260020595897509 750195236253861730783)
                    ·
                      rfl

theorem cell23_4383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 4].length) (baseStart_4383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383 prefixEnd_4383 := by exact prefixLift 4383
  have htrace : WordTrace (prefixWord ++ tailWord_4383) baseStart_4383 baseEnd_4383 := by
    simpa [prefixWord, tailWord_4383, baseEnd_4383] using wordTrace_append hprefix tailTrace_4383
  have hstable : (prefixWord ++ tailWord_4383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383).length < 2 ^ (prefixWord ++ tailWord_4383).sum := by decide
  have hdescent : baseEnd_4383 < baseStart_4383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 1, 5, 2]
def baseStart_4433 : Nat := 118140960795 + 4433 * 2 ^ 59
def prefixEnd_4433 : Nat := 4983230072969 + 3 ^ 40 * 4433 * 2
def baseEnd_4433 : Nat := 2276259741486389567119

theorem tailTrace_4433 : CollatzResearch.WordTrace tailWord_4433 prefixEnd_4433 2276259741486389567119 := by
  unfold tailWord_4433
  simp only [CollatzResearch.WordTrace]
  refine ⟨161684792947472941233953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107789861964981960822635 161684792947472941233953)
  ·
    refine ⟨121263594710604705925465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161684792947472941233953 121263594710604705925465)
    ·
      refine ⟨90947696032953529444099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121263594710604705925465 90947696032953529444099)
      ·
        refine ⟨136421544049430294166149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90947696032953529444099 136421544049430294166149)
        ·
          refine ⟨25579039509268180156153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136421544049430294166149 25579039509268180156153)
          ·
            refine ⟨19184279631951135117115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25579039509268180156153 19184279631951135117115)
            ·
              refine ⟨28776419447926702675673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19184279631951135117115 28776419447926702675673)
              ·
                refine ⟨21582314585945027006755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28776419447926702675673 21582314585945027006755)
                ·
                  refine ⟨32373471878917540510133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21582314585945027006755 32373471878917540510133)
                  ·
                    refine ⟨3035012988648519422825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32373471878917540510133 3035012988648519422825)
                    ·
                      refine ⟨2276259741486389567119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3035012988648519422825 2276259741486389567119)
                      ·
                        rfl

theorem cell23_4433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 5, 2].length) (baseStart_4433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433 prefixEnd_4433 := by exact prefixLift 4433
  have htrace : WordTrace (prefixWord ++ tailWord_4433) baseStart_4433 baseEnd_4433 := by
    simpa [prefixWord, tailWord_4433, baseEnd_4433] using wordTrace_append hprefix tailTrace_4433
  have hstable : (prefixWord ++ tailWord_4433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433).length < 2 ^ (prefixWord ++ tailWord_4433).sum := by decide
  have hdescent : baseEnd_4433 < baseStart_4433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4450 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 1, 5, 2]
def baseStart_4450 : Nat := 118140960795 + 4450 * 2 ^ 59
def prefixEnd_4450 : Nat := 4983230072969 + 3 ^ 40 * 4450 * 2
def baseEnd_4450 : Nat := 2284988912612823054541

theorem tailTrace_4450 : CollatzResearch.WordTrace tailWord_4450 prefixEnd_4450 2284988912612823054541 := by
  unfold tailWord_4450
  simp only [CollatzResearch.WordTrace]
  refine ⟨40576208471471211150701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108203222590589896401869 40576208471471211150701)
  ·
    refine ⟨15216078176801704181513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40576208471471211150701 15216078176801704181513)
    ·
      refine ⟨11412058632601278136135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15216078176801704181513 11412058632601278136135)
      ·
        refine ⟨17118087948901917204203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11412058632601278136135 17118087948901917204203)
        ·
          refine ⟨25677131923352875806305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17118087948901917204203 25677131923352875806305)
          ·
            refine ⟨19257848942514656854729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25677131923352875806305 19257848942514656854729)
            ·
              refine ⟨14443386706885992641047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19257848942514656854729 14443386706885992641047)
              ·
                refine ⟨21665080060328988961571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14443386706885992641047 21665080060328988961571)
                ·
                  refine ⟨32497620090493483442357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21665080060328988961571 32497620090493483442357)
                  ·
                    refine ⟨3046651883483764072721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32497620090493483442357 3046651883483764072721)
                    ·
                      refine ⟨2284988912612823054541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3046651883483764072721 2284988912612823054541)
                      ·
                        rfl

theorem cell23_4450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_4450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4450 prefixEnd_4450 := by exact prefixLift 4450
  have htrace : WordTrace (prefixWord ++ tailWord_4450) baseStart_4450 baseEnd_4450 := by
    simpa [prefixWord, tailWord_4450, baseEnd_4450] using wordTrace_append hprefix tailTrace_4450
  have hstable : (prefixWord ++ tailWord_4450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4450).length < 2 ^ (prefixWord ++ tailWord_4450).sum := by decide
  have hdescent : baseEnd_4450 < baseStart_4450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473 : List Nat := [1, 2, 1, 3, 2, 1, 1, 6, 2, 4]
def baseStart_4473 : Nat := 118140960795 + 4473 * 2 ^ 59
def prefixEnd_4473 : Nat := 4983230072969 + 3 ^ 40 * 4473 * 2
def baseEnd_4473 : Nat := 765599655888744355645

theorem tailTrace_4473 : CollatzResearch.WordTrace tailWord_4473 prefixEnd_4473 765599655888744355645 := by
  unfold tailWord_4473
  simp only [CollatzResearch.WordTrace]
  refine ⟨163143712802559772690073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108762475201706515126715 163143712802559772690073)
  ·
    refine ⟨122357784601919829517555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163143712802559772690073 122357784601919829517555)
    ·
      refine ⟨183536676902879744276333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122357784601919829517555 183536676902879744276333)
      ·
        refine ⟨68826253838579904103625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183536676902879744276333 68826253838579904103625)
        ·
          refine ⟨51619690378934928077719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68826253838579904103625 51619690378934928077719)
          ·
            refine ⟨77429535568402392116579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51619690378934928077719 77429535568402392116579)
            ·
              refine ⟨116144303352603588174869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77429535568402392116579 116144303352603588174869)
              ·
                refine ⟨5444264219653293195697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 116144303352603588174869 5444264219653293195697)
                ·
                  refine ⟨4083198164739969896773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5444264219653293195697 4083198164739969896773)
                  ·
                    refine ⟨765599655888744355645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4083198164739969896773 765599655888744355645)
                    ·
                      rfl

theorem cell23_4473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 4].length) (baseStart_4473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473 prefixEnd_4473 := by exact prefixLift 4473
  have htrace : WordTrace (prefixWord ++ tailWord_4473) baseStart_4473 baseEnd_4473 := by
    simpa [prefixWord, tailWord_4473, baseEnd_4473] using wordTrace_append hprefix tailTrace_4473
  have hstable : (prefixWord ++ tailWord_4473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473).length < 2 ^ (prefixWord ++ tailWord_4473).sum := by decide
  have hdescent : baseEnd_4473 < baseStart_4473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 5, 2, 4]
def baseStart_4476 : Nat := 118140960795 + 4476 * 2 ^ 59
def prefixEnd_4476 : Nat := 4983230072969 + 3 ^ 40 * 4476 * 2
def baseEnd_4476 : Nat := 2298339409629721329421

theorem tailTrace_4476 : CollatzResearch.WordTrace tailWord_4476 prefixEnd_4476 2298339409629721329421 := by
  unfold tailWord_4476
  simp only [CollatzResearch.WordTrace]
  refine ⟨81626565895845642524641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108835421194460856699521 81626565895845642524641)
  ·
    refine ⟨61219924421884231893481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81626565895845642524641 61219924421884231893481)
    ·
      refine ⟨45914943316413173920111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61219924421884231893481 45914943316413173920111)
      ·
        refine ⟨68872414974619760880167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45914943316413173920111 68872414974619760880167)
        ·
          refine ⟨103308622461929641320251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68872414974619760880167 103308622461929641320251)
          ·
            refine ⟨154962933692894461980377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103308622461929641320251 154962933692894461980377)
            ·
              refine ⟨116222200269670846485283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154962933692894461980377 116222200269670846485283)
              ·
                refine ⟨174333300404506269727925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116222200269670846485283 174333300404506269727925)
                ·
                  refine ⟨16343746912922462786993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 174333300404506269727925 16343746912922462786993)
                  ·
                    refine ⟨12257810184691847090245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16343746912922462786993 12257810184691847090245)
                    ·
                      refine ⟨2298339409629721329421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12257810184691847090245 2298339409629721329421)
                      ·
                        rfl

theorem cell23_4476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_4476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476 prefixEnd_4476 := by exact prefixLift 4476
  have htrace : WordTrace (prefixWord ++ tailWord_4476) baseStart_4476 baseEnd_4476 := by
    simpa [prefixWord, tailWord_4476, baseEnd_4476] using wordTrace_append hprefix tailTrace_4476
  have hstable : (prefixWord ++ tailWord_4476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476).length < 2 ^ (prefixWord ++ tailWord_4476).sum := by decide
  have hdescent : baseEnd_4476 < baseStart_4476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_4510 : Nat := 118140960795 + 4510 * 2 ^ 59
def prefixEnd_4510 : Nat := 4983230072969 + 3 ^ 40 * 4510 * 2
def baseEnd_4510 : Nat := 2315797751882588304265

theorem tailTrace_4510 : CollatzResearch.WordTrace tailWord_4510 prefixEnd_4510 2315797751882588304265 := by
  unfold tailWord_4510
  simp only [CollatzResearch.WordTrace]
  refine ⟨20561651708564386473373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109662142445676727857989 20561651708564386473373)
  ·
    refine ⟨7710619390711644927515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20561651708564386473373 7710619390711644927515)
    ·
      refine ⟨11565929086067467391273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7710619390711644927515 11565929086067467391273)
      ·
        refine ⟨8674446814550600543455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11565929086067467391273 8674446814550600543455)
        ·
          refine ⟨13011670221825900815183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8674446814550600543455 13011670221825900815183)
          ·
            refine ⟨19517505332738851222775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13011670221825900815183 19517505332738851222775)
            ·
              refine ⟨29276257999108276834163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19517505332738851222775 29276257999108276834163)
              ·
                refine ⟨43914386998662415251245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29276257999108276834163 43914386998662415251245)
                ·
                  refine ⟨16467895124498405719217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43914386998662415251245 16467895124498405719217)
                  ·
                    refine ⟨12350921343373804289413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16467895124498405719217 12350921343373804289413)
                    ·
                      refine ⟨2315797751882588304265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12350921343373804289413 2315797751882588304265)
                      ·
                        rfl

theorem cell23_4510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_4510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510 prefixEnd_4510 := by exact prefixLift 4510
  have htrace : WordTrace (prefixWord ++ tailWord_4510) baseStart_4510 baseEnd_4510 := by
    simpa [prefixWord, tailWord_4510, baseEnd_4510] using wordTrace_append hprefix tailTrace_4510
  have hstable : (prefixWord ++ tailWord_4510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510).length < 2 ^ (prefixWord ++ tailWord_4510).sum := by decide
  have hdescent : baseEnd_4510 < baseStart_4510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4514 : List Nat := [3, 3, 1, 2, 1, 1, 2, 5, 1, 2, 2]
def baseStart_4514 : Nat := 118140960795 + 4514 * 2 ^ 59
def prefixEnd_4514 : Nat := 4983230072969 + 3 ^ 40 * 4514 * 2
def baseEnd_4514 : Nat := 2317851674500572654247

theorem tailTrace_4514 : CollatzResearch.WordTrace tailWord_4514 prefixEnd_4514 2317851674500572654247 := by
  unfold tailWord_4514
  simp only [CollatzResearch.WordTrace]
  refine ⟨41159776413505943733149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109759403769349183288397 41159776413505943733149)
  ·
    refine ⟨15434916155064728899931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41159776413505943733149 15434916155064728899931)
    ·
      refine ⟨23152374232597093349897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15434916155064728899931 23152374232597093349897)
      ·
        refine ⟨17364280674447820012423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23152374232597093349897 17364280674447820012423)
        ·
          refine ⟨26046421011671730018635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17364280674447820012423 26046421011671730018635)
          ·
            refine ⟨39069631517507595027953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26046421011671730018635 39069631517507595027953)
            ·
              refine ⟨29302223638130696270965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39069631517507595027953 29302223638130696270965)
              ·
                refine ⟨2747083466074752775403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29302223638130696270965 2747083466074752775403)
                ·
                  refine ⟨4120625199112129163105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2747083466074752775403 4120625199112129163105)
                  ·
                    refine ⟨3090468899334096872329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4120625199112129163105 3090468899334096872329)
                    ·
                      refine ⟨2317851674500572654247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3090468899334096872329 2317851674500572654247)
                      ·
                        rfl

theorem cell23_4514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_4514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4514 prefixEnd_4514 := by exact prefixLift 4514
  have htrace : WordTrace (prefixWord ++ tailWord_4514) baseStart_4514 baseEnd_4514 := by
    simpa [prefixWord, tailWord_4514, baseEnd_4514] using wordTrace_append hprefix tailTrace_4514
  have hstable : (prefixWord ++ tailWord_4514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4514).length < 2 ^ (prefixWord ++ tailWord_4514).sum := by decide
  have hdescent : baseEnd_4514 < baseStart_4514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570 : List Nat := [3, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2]
def baseStart_4570 : Nat := 118140960795 + 4570 * 2 ^ 59
def prefixEnd_4570 : Nat := 4983230072969 + 3 ^ 40 * 4570 * 2
def baseEnd_4570 : Nat := 2346606591152353553989

theorem tailTrace_4570 : CollatzResearch.WordTrace tailWord_4570 prefixEnd_4570 2346606591152353553989 := by
  unfold tailWord_4570
  simp only [CollatzResearch.WordTrace]
  refine ⟨41670398362786334742791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111121062300763559314109 41670398362786334742791)
  ·
    refine ⟨62505597544179502114187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41670398362786334742791 62505597544179502114187)
    ·
      refine ⟨93758396316269253171281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62505597544179502114187 93758396316269253171281)
      ·
        refine ⟨70318797237201939878461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93758396316269253171281 70318797237201939878461)
        ·
          refine ⟨26369548963950727454423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70318797237201939878461 26369548963950727454423)
          ·
            refine ⟨39554323445926091181635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26369548963950727454423 39554323445926091181635)
            ·
              refine ⟨59331485168889136772453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39554323445926091181635 59331485168889136772453)
              ·
                refine ⟨11124653469166713144835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59331485168889136772453 11124653469166713144835)
                ·
                  refine ⟨16686980203750069717253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11124653469166713144835 16686980203750069717253)
                  ·
                    refine ⟨3128808788203138071985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16686980203750069717253 3128808788203138071985)
                    ·
                      refine ⟨2346606591152353553989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3128808788203138071985 2346606591152353553989)
                      ·
                        rfl

theorem cell23_4570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2].length) (baseStart_4570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570 prefixEnd_4570 := by exact prefixLift 4570
  have htrace : WordTrace (prefixWord ++ tailWord_4570) baseStart_4570 baseEnd_4570 := by
    simpa [prefixWord, tailWord_4570, baseEnd_4570] using wordTrace_append hprefix tailTrace_4570
  have hstable : (prefixWord ++ tailWord_4570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570).length < 2 ^ (prefixWord ++ tailWord_4570).sum := by decide
  have hdescent : baseEnd_4570 < baseStart_4570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_4573 : Nat := 118140960795 + 4573 * 2 ^ 59
def prefixEnd_4573 : Nat := 4983230072969 + 3 ^ 40 * 4573 * 2
def baseEnd_4573 : Nat := 2348147033115841816475

theorem tailTrace_4573 : CollatzResearch.WordTrace tailWord_4573 prefixEnd_4573 2348147033115841816475 := by
  unfold tailWord_4573
  simp only [CollatzResearch.WordTrace]
  refine ⟨166791012440276851330373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111194008293517900886915 166791012440276851330373)
  ·
    refine ⟨31273314832551909624445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166791012440276851330373 31273314832551909624445)
    ·
      refine ⟨11727493062206966109167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31273314832551909624445 11727493062206966109167)
      ·
        refine ⟨17591239593310449163751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11727493062206966109167 17591239593310449163751)
        ·
          refine ⟨26386859389965673745627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17591239593310449163751 26386859389965673745627)
          ·
            refine ⟨39580289084948510618441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26386859389965673745627 39580289084948510618441)
            ·
              refine ⟨29685216813711382963831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39580289084948510618441 29685216813711382963831)
              ·
                refine ⟨44527825220567074445747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29685216813711382963831 44527825220567074445747)
                ·
                  refine ⟨66791737830850611668621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44527825220567074445747 66791737830850611668621)
                  ·
                    refine ⟨25046901686568979375733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66791737830850611668621 25046901686568979375733)
                    ·
                      refine ⟨2348147033115841816475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25046901686568979375733 2348147033115841816475)
                      ·
                        rfl

theorem cell23_4573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_4573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573 prefixEnd_4573 := by exact prefixLift 4573
  have htrace : WordTrace (prefixWord ++ tailWord_4573) baseStart_4573 baseEnd_4573 := by
    simpa [prefixWord, tailWord_4573, baseEnd_4573] using wordTrace_append hprefix tailTrace_4573
  have hstable : (prefixWord ++ tailWord_4573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573).length < 2 ^ (prefixWord ++ tailWord_4573).sum := by decide
  have hdescent : baseEnd_4573 < baseStart_4573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 9]
def baseStart_4576 : Nat := 118140960795 + 4576 * 2 ^ 59
def prefixEnd_4576 : Nat := 4983230072969 + 3 ^ 40 * 4576 * 2
def baseEnd_4576 : Nat := 261076386119925564329

theorem tailTrace_4576 : CollatzResearch.WordTrace tailWord_4576 prefixEnd_4576 261076386119925564329 := by
  unfold tailWord_4576
  simp only [CollatzResearch.WordTrace]
  refine ⟨83450215714704181844791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111266954286272242459721 83450215714704181844791)
  ·
    refine ⟨125175323572056272767187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83450215714704181844791 125175323572056272767187)
    ·
      refine ⟨187762985358084409150781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125175323572056272767187 187762985358084409150781)
      ·
        refine ⟨70411119509281653431543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187762985358084409150781 70411119509281653431543)
        ·
          refine ⟨105616679263922480147315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70411119509281653431543 105616679263922480147315)
          ·
            refine ⟨158425018895883720220973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105616679263922480147315 158425018895883720220973)
            ·
              refine ⟨59409382085956395082865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158425018895883720220973 59409382085956395082865)
              ·
                refine ⟨44557036564467296312149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59409382085956395082865 44557036564467296312149)
                ·
                  refine ⟨261076386119925564329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44557036564467296312149 261076386119925564329)
                  ·
                    rfl

theorem cell23_4576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 9].length) (baseStart_4576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576 prefixEnd_4576 := by exact prefixLift 4576
  have htrace : WordTrace (prefixWord ++ tailWord_4576) baseStart_4576 baseEnd_4576 := by
    simpa [prefixWord, tailWord_4576, baseEnd_4576] using wordTrace_append hprefix tailTrace_4576
  have hstable : (prefixWord ++ tailWord_4576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576).length < 2 ^ (prefixWord ++ tailWord_4576).sum := by decide
  have hdescent : baseEnd_4576 < baseStart_4576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581 : List Nat := [1, 3, 1, 5, 3, 1, 1, 2, 2, 1, 3]
def baseStart_4581 : Nat := 118140960795 + 4581 * 2 ^ 59
def prefixEnd_4581 : Nat := 4983230072969 + 3 ^ 40 * 4581 * 2
def baseEnd_4581 : Nat := 2352254878351810516439

theorem tailTrace_4581 : CollatzResearch.WordTrace tailWord_4581 prefixEnd_4581 2352254878351810516439 := by
  unfold tailWord_4581
  simp only [CollatzResearch.WordTrace]
  refine ⟨167082796411294217621597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111388530940862811747731 167082796411294217621597)
  ·
    refine ⟨62656048654235331608099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167082796411294217621597 62656048654235331608099)
    ·
      refine ⟨93984072981352997412149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62656048654235331608099 93984072981352997412149)
      ·
        refine ⟨8811006842001843507389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93984072981352997412149 8811006842001843507389)
        ·
          refine ⟨3304127565750691315271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8811006842001843507389 3304127565750691315271)
          ·
            refine ⟨4956191348626036972907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3304127565750691315271 4956191348626036972907)
            ·
              refine ⟨7434287022939055459361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4956191348626036972907 7434287022939055459361)
              ·
                refine ⟨5575715267204291594521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7434287022939055459361 5575715267204291594521)
                ·
                  refine ⟨4181786450403218695891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5575715267204291594521 4181786450403218695891)
                  ·
                    refine ⟨6272679675604828043837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4181786450403218695891 6272679675604828043837)
                    ·
                      refine ⟨2352254878351810516439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6272679675604828043837 2352254878351810516439)
                      ·
                        rfl

theorem cell23_4581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_4581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581 prefixEnd_4581 := by exact prefixLift 4581
  have htrace : WordTrace (prefixWord ++ tailWord_4581) baseStart_4581 baseEnd_4581 := by
    simpa [prefixWord, tailWord_4581, baseEnd_4581] using wordTrace_append hprefix tailTrace_4581
  have hstable : (prefixWord ++ tailWord_4581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581).length < 2 ^ (prefixWord ++ tailWord_4581).sum := by decide
  have hdescent : baseEnd_4581 < baseStart_4581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_4583 : Nat := 118140960795 + 4583 * 2 ^ 59
def prefixEnd_4583 : Nat := 4983230072969 + 3 ^ 40 * 4583 * 2
def baseEnd_4583 : Nat := 2353281839660802691429

theorem tailTrace_4583 : CollatzResearch.WordTrace tailWord_4583 prefixEnd_4583 2353281839660802691429 := by
  unfold tailWord_4583
  simp only [CollatzResearch.WordTrace]
  refine ⟨167155742404048559194403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111437161602699039462935 167155742404048559194403)
  ·
    refine ⟨250733613606072838791605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167155742404048559194403 250733613606072838791605)
    ·
      refine ⟨23506276275569328636713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 250733613606072838791605 23506276275569328636713)
      ·
        refine ⟨17629707206676996477535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23506276275569328636713 17629707206676996477535)
        ·
          refine ⟨26444560810015494716303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17629707206676996477535 26444560810015494716303)
          ·
            refine ⟨39666841215023242074455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26444560810015494716303 39666841215023242074455)
            ·
              refine ⟨59500261822534863111683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39666841215023242074455 59500261822534863111683)
              ·
                refine ⟨89250392733802294667525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59500261822534863111683 89250392733802294667525)
                ·
                  refine ⟨16734448637587930250161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89250392733802294667525 16734448637587930250161)
                  ·
                    refine ⟨12550836478190947687621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16734448637587930250161 12550836478190947687621)
                    ·
                      refine ⟨2353281839660802691429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12550836478190947687621 2353281839660802691429)
                      ·
                        rfl

theorem cell23_4583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_4583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583 prefixEnd_4583 := by exact prefixLift 4583
  have htrace : WordTrace (prefixWord ++ tailWord_4583) baseStart_4583 baseEnd_4583 := by
    simpa [prefixWord, tailWord_4583, baseEnd_4583] using wordTrace_append hprefix tailTrace_4583
  have hstable : (prefixWord ++ tailWord_4583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583).length < 2 ^ (prefixWord ++ tailWord_4583).sum := by decide
  have hdescent : baseEnd_4583 < baseStart_4583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593 : List Nat := [1, 2, 2, 2, 3, 1, 4, 1, 7]
def baseStart_4593 : Nat := 118140960795 + 4593 * 2 ^ 59
def prefixEnd_4593 : Nat := 4983230072969 + 3 ^ 40 * 4593 * 2
def baseEnd_4593 : Nat := 262046294022862618487

theorem tailTrace_4593 : CollatzResearch.WordTrace tailWord_4593 prefixEnd_4593 262046294022862618487 := by
  unfold tailWord_4593
  simp only [CollatzResearch.WordTrace]
  refine ⟨167520472367820267058433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111680314911880178038955 167520472367820267058433)
  ·
    refine ⟨125640354275865200293825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167520472367820267058433 125640354275865200293825)
    ·
      refine ⟨94230265706898900220369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125640354275865200293825 94230265706898900220369)
      ·
        refine ⟨70672699280174175165277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94230265706898900220369 70672699280174175165277)
        ·
          refine ⟨26502262230065315686979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70672699280174175165277 26502262230065315686979)
          ·
            refine ⟨39753393345097973530469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26502262230065315686979 39753393345097973530469)
            ·
              refine ⟨7453761252205870036963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39753393345097973530469 7453761252205870036963)
              ·
                refine ⟨11180641878308805055445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7453761252205870036963 11180641878308805055445)
                ·
                  refine ⟨262046294022862618487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11180641878308805055445 262046294022862618487)
                  ·
                    rfl

theorem cell23_4593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 7].length) (baseStart_4593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593 prefixEnd_4593 := by exact prefixLift 4593
  have htrace : WordTrace (prefixWord ++ tailWord_4593) baseStart_4593 baseEnd_4593 := by
    simpa [prefixWord, tailWord_4593, baseEnd_4593] using wordTrace_append hprefix tailTrace_4593
  have hstable : (prefixWord ++ tailWord_4593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593).length < 2 ^ (prefixWord ++ tailWord_4593).sum := by decide
  have hdescent : baseEnd_4593 < baseStart_4593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4621 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_4621 : Nat := 118140960795 + 4621 * 2 ^ 59
def prefixEnd_4621 : Nat := 4983230072969 + 3 ^ 40 * 4621 * 2
def baseEnd_4621 : Nat := 2372794104531654016255

theorem tailTrace_4621 : CollatzResearch.WordTrace tailWord_4621 prefixEnd_4621 2372794104531654016255 := by
  unfold tailWord_4621
  simp only [CollatzResearch.WordTrace]
  refine ⟨168541716266381049077717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112361144177587366051811 168541716266381049077717)
  ·
    refine ⟨3950196474993305837759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 168541716266381049077717 3950196474993305837759)
    ·
      refine ⟨5925294712489958756639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3950196474993305837759 5925294712489958756639)
      ·
        refine ⟨8887942068734938134959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5925294712489958756639 8887942068734938134959)
        ·
          refine ⟨13331913103102407202439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8887942068734938134959 13331913103102407202439)
          ·
            refine ⟨19997869654653610803659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13331913103102407202439 19997869654653610803659)
            ·
              refine ⟨29996804481980416205489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19997869654653610803659 29996804481980416205489)
              ·
                refine ⟨22497603361485312154117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29996804481980416205489 22497603361485312154117)
                ·
                  refine ⟨4218300630278496028897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22497603361485312154117 4218300630278496028897)
                  ·
                    refine ⟨3163725472708872021673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4218300630278496028897 3163725472708872021673)
                    ·
                      refine ⟨2372794104531654016255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3163725472708872021673 2372794104531654016255)
                      ·
                        rfl

theorem cell23_4621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_4621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4621 prefixEnd_4621 := by exact prefixLift 4621
  have htrace : WordTrace (prefixWord ++ tailWord_4621) baseStart_4621 baseEnd_4621 := by
    simpa [prefixWord, tailWord_4621, baseEnd_4621] using wordTrace_append hprefix tailTrace_4621
  have hstable : (prefixWord ++ tailWord_4621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4621).length < 2 ^ (prefixWord ++ tailWord_4621).sum := by decide
  have hdescent : baseEnd_4621 < baseStart_4621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644 : List Nat := [2, 3, 1, 5, 2, 1, 1, 1, 7]
def baseStart_4644 : Nat := 118140960795 + 4644 * 2 ^ 59
def prefixEnd_4644 : Nat := 4983230072969 + 3 ^ 40 * 4644 * 2
def baseEnd_4644 : Nat := 264956017731673780961

theorem tailTrace_4644 : CollatzResearch.WordTrace tailWord_4644 prefixEnd_4644 264956017731673780961 := by
  unfold tailWord_4644
  simp only [CollatzResearch.WordTrace]
  refine ⟨84690297591527988582493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112920396788703984776657 84690297591527988582493)
  ·
    refine ⟨31758861596822995718435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84690297591527988582493 31758861596822995718435)
    ·
      refine ⟨47638292395234493577653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31758861596822995718435 47638292395234493577653)
      ·
        refine ⟨4466089912053233772905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47638292395234493577653 4466089912053233772905)
        ·
          refine ⟨3349567434039925329679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4466089912053233772905 3349567434039925329679)
          ·
            refine ⟨5024351151059887994519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3349567434039925329679 5024351151059887994519)
            ·
              refine ⟨7536526726589831991779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5024351151059887994519 7536526726589831991779)
              ·
                refine ⟨11304790089884747987669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7536526726589831991779 11304790089884747987669)
                ·
                  refine ⟨264956017731673780961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11304790089884747987669 264956017731673780961)
                  ·
                    rfl

theorem cell23_4644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_4644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644 prefixEnd_4644 := by exact prefixLift 4644
  have htrace : WordTrace (prefixWord ++ tailWord_4644) baseStart_4644 baseEnd_4644 := by
    simpa [prefixWord, tailWord_4644, baseEnd_4644] using wordTrace_append hprefix tailTrace_4644
  have hstable : (prefixWord ++ tailWord_4644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644).length < 2 ^ (prefixWord ++ tailWord_4644).sum := by decide
  have hdescent : baseEnd_4644 < baseStart_4644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4650 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_4650 : Nat := 118140960795 + 4650 * 2 ^ 59
def prefixEnd_4650 : Nat := 4983230072969 + 3 ^ 40 * 4650 * 2
def baseEnd_4650 : Nat := 2387685043512040553621

theorem tailTrace_4650 : CollatzResearch.WordTrace tailWord_4650 prefixEnd_4650 2387685043512040553621 := by
  unfold tailWord_4650
  simp only [CollatzResearch.WordTrace]
  refine ⟨42399858290329750470851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113066288774212667922269 42399858290329750470851)
  ·
    refine ⟨63599787435494625706277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42399858290329750470851 63599787435494625706277)
    ·
      refine ⟨11924960144155242319927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63599787435494625706277 11924960144155242319927)
      ·
        refine ⟨17887440216232863479891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11924960144155242319927 17887440216232863479891)
        ·
          refine ⟨26831160324349295219837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17887440216232863479891 26831160324349295219837)
          ·
            refine ⟨10061685121630985707439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26831160324349295219837 10061685121630985707439)
            ·
              refine ⟨15092527682446478561159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10061685121630985707439 15092527682446478561159)
              ·
                refine ⟨22638791523669717841739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15092527682446478561159 22638791523669717841739)
                ·
                  refine ⟨33958187285504576762609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22638791523669717841739 33958187285504576762609)
                  ·
                    refine ⟨25468640464128432571957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33958187285504576762609 25468640464128432571957)
                    ·
                      refine ⟨2387685043512040553621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25468640464128432571957 2387685043512040553621)
                      ·
                        rfl

theorem cell23_4650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_4650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4650 prefixEnd_4650 := by exact prefixLift 4650
  have htrace : WordTrace (prefixWord ++ tailWord_4650) baseStart_4650 baseEnd_4650 := by
    simpa [prefixWord, tailWord_4650, baseEnd_4650] using wordTrace_append hprefix tailTrace_4650
  have hstable : (prefixWord ++ tailWord_4650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4650).length < 2 ^ (prefixWord ++ tailWord_4650).sum := by decide
  have hdescent : baseEnd_4650 < baseStart_4650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4704 : List Nat := [2, 1, 1, 3, 2, 1, 6, 2, 1, 4]
def baseStart_4704 : Nat := 118140960795 + 4704 * 2 ^ 59
def prefixEnd_4704 : Nat := 4983230072969 + 3 ^ 40 * 4704 * 2
def baseEnd_4704 : Nat := 805137666284943092791

theorem tailTrace_4704 : CollatzResearch.WordTrace tailWord_4704 prefixEnd_4704 805137666284943092791 := by
  unfold tailWord_4704
  simp only [CollatzResearch.WordTrace]
  refine ⟨85784487482843112174583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114379316643790816232777 85784487482843112174583)
  ·
    refine ⟨128676731224264668261875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85784487482843112174583 128676731224264668261875)
    ·
      refine ⟨193015096836397002392813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128676731224264668261875 193015096836397002392813)
      ·
        refine ⟨72380661313648875897305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193015096836397002392813 72380661313648875897305)
        ·
          refine ⟨54285495985236656922979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72380661313648875897305 54285495985236656922979)
          ·
            refine ⟨81428243977854985384469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54285495985236656922979 81428243977854985384469)
            ·
              refine ⟨3816948936461952439897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 81428243977854985384469 3816948936461952439897)
              ·
                refine ⟨2862711702346464329923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3816948936461952439897 2862711702346464329923)
                ·
                  refine ⟨4294067553519696494885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2862711702346464329923 4294067553519696494885)
                  ·
                    refine ⟨805137666284943092791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4294067553519696494885 805137666284943092791)
                    ·
                      rfl

theorem cell23_4704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 1, 4].length) (baseStart_4704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4704 prefixEnd_4704 := by exact prefixLift 4704
  have htrace : WordTrace (prefixWord ++ tailWord_4704) baseStart_4704 baseEnd_4704 := by
    simpa [prefixWord, tailWord_4704, baseEnd_4704] using wordTrace_append hprefix tailTrace_4704
  have hstable : (prefixWord ++ tailWord_4704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4704).length < 2 ^ (prefixWord ++ tailWord_4704).sum := by decide
  have hdescent : baseEnd_4704 < baseStart_4704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4737 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 1, 5, 2]
def baseStart_4737 : Nat := 118140960795 + 4737 * 2 ^ 59
def prefixEnd_4737 : Nat := 4983230072969 + 3 ^ 40 * 4737 * 2
def baseEnd_4737 : Nat := 2432357860453200165721

theorem tailTrace_4737 : CollatzResearch.WordTrace tailWord_4737 prefixEnd_4737 2432357860453200165721 := by
  unfold tailWord_4737
  simp only [CollatzResearch.WordTrace]
  refine ⟨172772583846132860300465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115181722564088573533643 172772583846132860300465)
  ·
    refine ⟨129579437884599645225349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172772583846132860300465 129579437884599645225349)
    ·
      refine ⟨24296144603362433479753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129579437884599645225349 24296144603362433479753)
      ·
        refine ⟨18222108452521825109815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24296144603362433479753 18222108452521825109815)
        ·
          refine ⟨27333162678782737664723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18222108452521825109815 27333162678782737664723)
          ·
            refine ⟨40999744018174106497085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27333162678782737664723 40999744018174106497085)
            ·
              refine ⟨15374904006815289936407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40999744018174106497085 15374904006815289936407)
              ·
                refine ⟨23062356010222934904611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15374904006815289936407 23062356010222934904611)
                ·
                  refine ⟨34593534015334402356917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23062356010222934904611 34593534015334402356917)
                  ·
                    refine ⟨3243143813937600220961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34593534015334402356917 3243143813937600220961)
                    ·
                      refine ⟨2432357860453200165721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3243143813937600220961 2432357860453200165721)
                      ·
                        rfl

theorem cell23_4737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_4737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4737 prefixEnd_4737 := by exact prefixLift 4737
  have htrace : WordTrace (prefixWord ++ tailWord_4737) baseStart_4737 baseEnd_4737 := by
    simpa [prefixWord, tailWord_4737, baseEnd_4737] using wordTrace_append hprefix tailTrace_4737
  have hstable : (prefixWord ++ tailWord_4737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4737).length < 2 ^ (prefixWord ++ tailWord_4737).sum := by decide
  have hdescent : baseEnd_4737 < baseStart_4737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4773 : List Nat := [1, 3, 1, 2, 1, 2, 1, 12]
def baseStart_4773 : Nat := 118140960795 + 4773 * 2 ^ 59
def prefixEnd_4773 : Nat := 4983230072969 + 3 ^ 40 * 4773 * 2
def baseEnd_4773 : Nat := 90771969037594789465

theorem tailTrace_4773 : CollatzResearch.WordTrace tailWord_4773 prefixEnd_4773 90771969037594789465 := by
  unfold tailWord_4773
  simp only [CollatzResearch.WordTrace]
  refine ⟨174085611715711008610973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116057074477140672407315 174085611715711008610973)
  ·
    refine ⟨65282104393391628229115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174085611715711008610973 65282104393391628229115)
    ·
      refine ⟨97923156590087442343673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65282104393391628229115 97923156590087442343673)
      ·
        refine ⟨73442367442565581757755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97923156590087442343673 73442367442565581757755)
        ·
          refine ⟨110163551163848372636633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73442367442565581757755 110163551163848372636633)
          ·
            refine ⟨82622663372886279477475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110163551163848372636633 82622663372886279477475)
            ·
              refine ⟨123933995059329419216213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82622663372886279477475 123933995059329419216213)
              ·
                refine ⟨90771969037594789465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 123933995059329419216213 90771969037594789465)
                ·
                  rfl

theorem cell23_4773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 12].length) (baseStart_4773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4773 prefixEnd_4773 := by exact prefixLift 4773
  have htrace : WordTrace (prefixWord ++ tailWord_4773) baseStart_4773 baseEnd_4773 := by
    simpa [prefixWord, tailWord_4773, baseEnd_4773] using wordTrace_append hprefix tailTrace_4773
  have hstable : (prefixWord ++ tailWord_4773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4773).length < 2 ^ (prefixWord ++ tailWord_4773).sum := by decide
  have hdescent : baseEnd_4773 < baseStart_4773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4787 : List Nat := [1, 1, 1, 2, 3, 4, 1, 4, 1, 2, 3]
def baseStart_4787 : Nat := 118140960795 + 4787 * 2 ^ 59
def prefixEnd_4787 : Nat := 4983230072969 + 3 ^ 40 * 4787 * 2
def baseEnd_4787 : Nat := 2458031893178004540491

theorem tailTrace_4787 : CollatzResearch.WordTrace tailWord_4787 prefixEnd_4787 2458031893178004540491 := by
  unfold tailWord_4787
  simp only [CollatzResearch.WordTrace]
  refine ⟨174596233664991399620615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116397489109994266413743 174596233664991399620615)
  ·
    refine ⟨261894350497487099430923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174596233664991399620615 261894350497487099430923)
    ·
      refine ⟨392841525746230649146385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261894350497487099430923 392841525746230649146385)
      ·
        refine ⟨294631144309672986859789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 392841525746230649146385 294631144309672986859789)
        ·
          refine ⟨110486679116127370072421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 294631144309672986859789 110486679116127370072421)
          ·
            refine ⟨20716252334273881888579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110486679116127370072421 20716252334273881888579)
            ·
              refine ⟨31074378501410822832869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20716252334273881888579 31074378501410822832869)
              ·
                refine ⟨5826445969014529281163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31074378501410822832869 5826445969014529281163)
                ·
                  refine ⟨8739668953521793921745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5826445969014529281163 8739668953521793921745)
                  ·
                    refine ⟨6554751715141345441309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8739668953521793921745 6554751715141345441309)
                    ·
                      refine ⟨2458031893178004540491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6554751715141345441309 2458031893178004540491)
                      ·
                        rfl

theorem cell23_4787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 2, 3].length) (baseStart_4787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4787 prefixEnd_4787 := by exact prefixLift 4787
  have htrace : WordTrace (prefixWord ++ tailWord_4787) baseStart_4787 baseEnd_4787 := by
    simpa [prefixWord, tailWord_4787, baseEnd_4787] using wordTrace_append hprefix tailTrace_4787
  have hstable : (prefixWord ++ tailWord_4787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4787).length < 2 ^ (prefixWord ++ tailWord_4787).sum := by decide
  have hdescent : baseEnd_4787 < baseStart_4787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4804 : List Nat := [2, 3, 3, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_4804 : Nat := 118140960795 + 4804 * 2 ^ 59
def prefixEnd_4804 : Nat := 4983230072969 + 3 ^ 40 * 4804 * 2
def baseEnd_4804 : Nat := 2466761064304438027913

theorem tailTrace_4804 : CollatzResearch.WordTrace tailWord_4804 prefixEnd_4804 2466761064304438027913 := by
  unfold tailWord_4804
  simp only [CollatzResearch.WordTrace]
  refine ⟨87608137301701651494733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116810849735602201992977 87608137301701651494733)
  ·
    refine ⟨32853051488138119310525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87608137301701651494733 32853051488138119310525)
    ·
      refine ⟨12319894308051794741447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32853051488138119310525 12319894308051794741447)
      ·
        refine ⟨18479841462077692112171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12319894308051794741447 18479841462077692112171)
        ·
          refine ⟨27719762193116538168257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18479841462077692112171 27719762193116538168257)
          ·
            refine ⟨20789821644837403626193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27719762193116538168257 20789821644837403626193)
            ·
              refine ⟨15592366233628052719645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20789821644837403626193 15592366233628052719645)
              ·
                refine ⟨5847137337610519769867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15592366233628052719645 5847137337610519769867)
                ·
                  refine ⟨8770706006415779654801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5847137337610519769867 8770706006415779654801)
                  ·
                    refine ⟨6578029504811834741101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8770706006415779654801 6578029504811834741101)
                    ·
                      refine ⟨2466761064304438027913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6578029504811834741101 2466761064304438027913)
                      ·
                        rfl

theorem cell23_4804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_4804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4804 prefixEnd_4804 := by exact prefixLift 4804
  have htrace : WordTrace (prefixWord ++ tailWord_4804) baseStart_4804 baseEnd_4804 := by
    simpa [prefixWord, tailWord_4804, baseEnd_4804] using wordTrace_append hprefix tailTrace_4804
  have hstable : (prefixWord ++ tailWord_4804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4804).length < 2 ^ (prefixWord ++ tailWord_4804).sum := by decide
  have hdescent : baseEnd_4804 < baseStart_4804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 4, 1, 3]
def baseStart_4817 : Nat := 118140960795 + 4817 * 2 ^ 59
def prefixEnd_4817 : Nat := 4983230072969 + 3 ^ 40 * 4817 * 2
def baseEnd_4817 : Nat := 2473436312812887165353

theorem tailTrace_4817 : CollatzResearch.WordTrace tailWord_4817 prefixEnd_4817 2473436312812887165353 := by
  unfold tailWord_4817
  simp only [CollatzResearch.WordTrace]
  refine ⟨175690423556306523212705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117126949037537682141803 175690423556306523212705)
  ·
    refine ⟨131767817667229892409529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175690423556306523212705 131767817667229892409529)
    ·
      refine ⟨98825863250422419307147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131767817667229892409529 98825863250422419307147)
      ·
        refine ⟨148238794875633628960721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98825863250422419307147 148238794875633628960721)
        ·
          refine ⟨111179096156725221720541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148238794875633628960721 111179096156725221720541)
          ·
            refine ⟨41692161058771958145203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111179096156725221720541 41692161058771958145203)
            ·
              refine ⟨62538241588157937217805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41692161058771958145203 62538241588157937217805)
              ·
                refine ⟨23451840595559226456677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62538241588157937217805 23451840595559226456677)
                ·
                  refine ⟨4397220111667354960627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23451840595559226456677 4397220111667354960627)
                  ·
                    refine ⟨6595830167501032440941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4397220111667354960627 6595830167501032440941)
                    ·
                      refine ⟨2473436312812887165353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6595830167501032440941 2473436312812887165353)
                      ·
                        rfl

theorem cell23_4817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 1, 3].length) (baseStart_4817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817 prefixEnd_4817 := by exact prefixLift 4817
  have htrace : WordTrace (prefixWord ++ tailWord_4817) baseStart_4817 baseEnd_4817 := by
    simpa [prefixWord, tailWord_4817, baseEnd_4817] using wordTrace_append hprefix tailTrace_4817
  have hstable : (prefixWord ++ tailWord_4817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817).length < 2 ^ (prefixWord ++ tailWord_4817).sum := by decide
  have hdescent : baseEnd_4817 < baseStart_4817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818 : List Nat := [3, 2, 2, 2, 3, 2, 1, 1, 3, 2, 2]
def baseStart_4818 : Nat := 118140960795 + 4818 * 2 ^ 59
def prefixEnd_4818 : Nat := 4983230072969 + 3 ^ 40 * 4818 * 2
def baseEnd_4818 : Nat := 2473949793467383252849

theorem tailTrace_4818 : CollatzResearch.WordTrace tailWord_4818 prefixEnd_4818 2473949793467383252849 := by
  unfold tailWord_4818
  simp only [CollatzResearch.WordTrace]
  refine ⟨43931724138170923499777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117151264368455795999405 43931724138170923499777)
  ·
    refine ⟨32948793103628192624833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43931724138170923499777 32948793103628192624833)
    ·
      refine ⟨24711594827721144468625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32948793103628192624833 24711594827721144468625)
      ·
        refine ⟨18533696120790858351469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24711594827721144468625 18533696120790858351469)
        ·
          refine ⟨6950136045296571881801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18533696120790858351469 6950136045296571881801)
          ·
            refine ⟨5212602033972428911351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6950136045296571881801 5212602033972428911351)
            ·
              refine ⟨7818903050958643367027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5212602033972428911351 7818903050958643367027)
              ·
                refine ⟨11728354576437965050541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7818903050958643367027 11728354576437965050541)
                ·
                  refine ⟨4398132966164236893953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11728354576437965050541 4398132966164236893953)
                  ·
                    refine ⟨3298599724623177670465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4398132966164236893953 3298599724623177670465)
                    ·
                      refine ⟨2473949793467383252849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3298599724623177670465 2473949793467383252849)
                      ·
                        rfl

theorem cell23_4818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_4818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818 prefixEnd_4818 := by exact prefixLift 4818
  have htrace : WordTrace (prefixWord ++ tailWord_4818) baseStart_4818 baseEnd_4818 := by
    simpa [prefixWord, tailWord_4818, baseEnd_4818] using wordTrace_append hprefix tailTrace_4818
  have hstable : (prefixWord ++ tailWord_4818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818).length < 2 ^ (prefixWord ++ tailWord_4818).sum := by decide
  have hdescent : baseEnd_4818 < baseStart_4818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828 : List Nat := [2, 2, 5, 1, 1, 3, 2, 1, 2, 4]
def baseStart_4828 : Nat := 118140960795 + 4828 * 2 ^ 59
def prefixEnd_4828 : Nat := 4983230072969 + 3 ^ 40 * 4828 * 2
def baseEnd_4828 : Nat := 826361533337448042601

theorem tailTrace_4828 : CollatzResearch.WordTrace tailWord_4828 prefixEnd_4828 826361533337448042601 := by
  unfold tailWord_4828
  simp only [CollatzResearch.WordTrace]
  refine ⟨88045813258227700931569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117394417677636934575425 88045813258227700931569)
  ·
    refine ⟨66034359943670775698677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88045813258227700931569 66034359943670775698677)
    ·
      refine ⟨6190721244719135221751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66034359943670775698677 6190721244719135221751)
      ·
        refine ⟨9286081867078702832627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6190721244719135221751 9286081867078702832627)
        ·
          refine ⟨13929122800618054248941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9286081867078702832627 13929122800618054248941)
          ·
            refine ⟨5223421050231770343353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13929122800618054248941 5223421050231770343353)
            ·
              refine ⟨3917565787673827757515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5223421050231770343353 3917565787673827757515)
              ·
                refine ⟨5876348681510741636273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3917565787673827757515 5876348681510741636273)
                ·
                  refine ⟨4407261511133056227205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5876348681510741636273 4407261511133056227205)
                  ·
                    refine ⟨826361533337448042601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4407261511133056227205 826361533337448042601)
                    ·
                      rfl

theorem cell23_4828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_4828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828 prefixEnd_4828 := by exact prefixLift 4828
  have htrace : WordTrace (prefixWord ++ tailWord_4828) baseStart_4828 baseEnd_4828 := by
    simpa [prefixWord, tailWord_4828, baseEnd_4828] using wordTrace_append hprefix tailTrace_4828
  have hstable : (prefixWord ++ tailWord_4828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828).length < 2 ^ (prefixWord ++ tailWord_4828).sum := by decide
  have hdescent : baseEnd_4828 < baseStart_4828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861 : List Nat := [1, 4, 1, 1, 1, 1, 7, 1, 1, 3, 2]
def baseStart_4861 : Nat := 118140960795 + 4861 * 2 ^ 59
def prefixEnd_4861 : Nat := 4983230072969 + 3 ^ 40 * 4861 * 2
def baseEnd_4861 : Nat := 2496029461610715015151

theorem tailTrace_4861 : CollatzResearch.WordTrace tailWord_4861 prefixEnd_4861 2496029461610715015151 := by
  unfold tailWord_4861
  simp only [CollatzResearch.WordTrace]
  refine ⟨177295235396902037814437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118196823597934691876291 177295235396902037814437)
  ·
    refine ⟨33242856636919132090207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177295235396902037814437 33242856636919132090207)
    ·
      refine ⟨49864284955378698135311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33242856636919132090207 49864284955378698135311)
      ·
        refine ⟨74796427433068047202967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49864284955378698135311 74796427433068047202967)
        ·
          refine ⟨112194641149602070804451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74796427433068047202967 112194641149602070804451)
          ·
            refine ⟨168291961724403106206677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112194641149602070804451 168291961724403106206677)
            ·
              refine ⟨3944342852915697801719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 168291961724403106206677 3944342852915697801719)
              ·
                refine ⟨5916514279373546702579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3944342852915697801719 5916514279373546702579)
                ·
                  refine ⟨8874771419060320053869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5916514279373546702579 8874771419060320053869)
                  ·
                    refine ⟨3328039282147620020201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8874771419060320053869 3328039282147620020201)
                    ·
                      refine ⟨2496029461610715015151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3328039282147620020201 2496029461610715015151)
                      ·
                        rfl

theorem cell23_4861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 1, 3, 2].length) (baseStart_4861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861 prefixEnd_4861 := by exact prefixLift 4861
  have htrace : WordTrace (prefixWord ++ tailWord_4861) baseStart_4861 baseEnd_4861 := by
    simpa [prefixWord, tailWord_4861, baseEnd_4861] using wordTrace_append hprefix tailTrace_4861
  have hstable : (prefixWord ++ tailWord_4861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861).length < 2 ^ (prefixWord ++ tailWord_4861).sum := by decide
  have hdescent : baseEnd_4861 < baseStart_4861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4914 : List Nat := [3, 2, 1, 1, 3, 1, 4, 3, 5]
def baseStart_4914 : Nat := 118140960795 + 4914 * 2 ^ 59
def prefixEnd_4914 : Nat := 4983230072969 + 3 ^ 40 * 4914 * 2
def baseEnd_4914 : Nat := 280360437366556405823

theorem tailTrace_4914 : CollatzResearch.WordTrace tailWord_4914 prefixEnd_4914 280360437366556405823 := by
  unfold tailWord_4914
  simp only [CollatzResearch.WordTrace]
  refine ⟨44807076051223022373449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119485536136594726329197 44807076051223022373449)
  ·
    refine ⟨33605307038417266780087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44807076051223022373449 33605307038417266780087)
    ·
      refine ⟨50407960557625900170131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33605307038417266780087 50407960557625900170131)
      ·
        refine ⟨75611940836438850255197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50407960557625900170131 75611940836438850255197)
        ·
          refine ⟨28354477813664568845699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75611940836438850255197 28354477813664568845699)
          ·
            refine ⟨42531716720496853268549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28354477813664568845699 42531716720496853268549)
            ·
              refine ⟨7974696885093159987853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42531716720496853268549 7974696885093159987853)
              ·
                refine ⟨2990511331909934995445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7974696885093159987853 2990511331909934995445)
                ·
                  refine ⟨280360437366556405823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2990511331909934995445 280360437366556405823)
                  ·
                    rfl

theorem cell23_4914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_4914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4914 prefixEnd_4914 := by exact prefixLift 4914
  have htrace : WordTrace (prefixWord ++ tailWord_4914) baseStart_4914 baseEnd_4914 := by
    simpa [prefixWord, tailWord_4914, baseEnd_4914] using wordTrace_append hprefix tailTrace_4914
  have hstable : (prefixWord ++ tailWord_4914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4914).length < 2 ^ (prefixWord ++ tailWord_4914).sum := by decide
  have hdescent : baseEnd_4914 < baseStart_4914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4925 : List Nat := [1, 4, 1, 4, 2, 2, 1, 2, 2, 2, 2]
def baseStart_4925 : Nat := 118140960795 + 4925 * 2 ^ 59
def prefixEnd_4925 : Nat := 4983230072969 + 3 ^ 40 * 4925 * 2
def baseEnd_4925 : Nat := 2528892223498464614857

theorem tailTrace_4925 : CollatzResearch.WordTrace tailWord_4925 prefixEnd_4925 2528892223498464614857 := by
  unfold tailWord_4925
  simp only [CollatzResearch.WordTrace]
  refine ⟨179629507165040968144229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119753004776693978762819 179629507165040968144229)
  ·
    refine ⟨33680532593445181527043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179629507165040968144229 33680532593445181527043)
    ·
      refine ⟨50520798890167772290565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33680532593445181527043 50520798890167772290565)
      ·
        refine ⟨9472649791906457304481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50520798890167772290565 9472649791906457304481)
        ·
          refine ⟨7104487343929842978361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9472649791906457304481 7104487343929842978361)
          ·
            refine ⟨5328365507947382233771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7104487343929842978361 5328365507947382233771)
            ·
              refine ⟨7992548261921073350657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5328365507947382233771 7992548261921073350657)
              ·
                refine ⟨5994411196440805012993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7992548261921073350657 5994411196440805012993)
                ·
                  refine ⟨4495808397330603759745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5994411196440805012993 4495808397330603759745)
                  ·
                    refine ⟨3371856297997952819809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4495808397330603759745 3371856297997952819809)
                    ·
                      refine ⟨2528892223498464614857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3371856297997952819809 2528892223498464614857)
                      ·
                        rfl

theorem cell23_4925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_4925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4925 prefixEnd_4925 := by exact prefixLift 4925
  have htrace : WordTrace (prefixWord ++ tailWord_4925) baseStart_4925 baseEnd_4925 := by
    simpa [prefixWord, tailWord_4925, baseEnd_4925] using wordTrace_append hprefix tailTrace_4925
  have hstable : (prefixWord ++ tailWord_4925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4925).length < 2 ^ (prefixWord ++ tailWord_4925).sum := by decide
  have hdescent : baseEnd_4925 < baseStart_4925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004 : List Nat := [2, 2, 1, 2, 1, 2, 6, 1, 6]
def baseStart_5004 : Nat := 118140960795 + 5004 * 2 ^ 59
def prefixEnd_5004 : Nat := 4983230072969 + 3 ^ 40 * 5004 * 2
def baseEnd_5004 : Nat := 285495243911517280777

theorem tailTrace_5004 : CollatzResearch.WordTrace tailWord_5004 prefixEnd_5004 285495243911517280777 := by
  unfold tailWord_5004
  simp only [CollatzResearch.WordTrace]
  refine ⟨91255436939418730135033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121673915919224973513377 91255436939418730135033)
  ·
    refine ⟨68441577704564047601275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91255436939418730135033 68441577704564047601275)
    ·
      refine ⟨102662366556846071401913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68441577704564047601275 102662366556846071401913)
      ·
        refine ⟨76996774917634553551435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102662366556846071401913 76996774917634553551435)
        ·
          refine ⟨115495162376451830327153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76996774917634553551435 115495162376451830327153)
          ·
            refine ⟨86621371782338872745365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115495162376451830327153 86621371782338872745365)
            ·
              refine ⟨4060376802297134659939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86621371782338872745365 4060376802297134659939)
              ·
                refine ⟨6090565203445701989909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4060376802297134659939 6090565203445701989909)
                ·
                  refine ⟨285495243911517280777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6090565203445701989909 285495243911517280777)
                  ·
                    rfl

theorem cell23_5004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 6].length) (baseStart_5004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004 prefixEnd_5004 := by exact prefixLift 5004
  have htrace : WordTrace (prefixWord ++ tailWord_5004) baseStart_5004 baseEnd_5004 := by
    simpa [prefixWord, tailWord_5004, baseEnd_5004] using wordTrace_append hprefix tailTrace_5004
  have hstable : (prefixWord ++ tailWord_5004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004).length < 2 ^ (prefixWord ++ tailWord_5004).sum := by decide
  have hdescent : baseEnd_5004 < baseStart_5004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 1, 5, 2]
def baseStart_5024 : Nat := 118140960795 + 5024 * 2 ^ 59
def prefixEnd_5024 : Nat := 4983230072969 + 3 ^ 40 * 5024 * 2
def baseEnd_5024 : Nat := 2579726808293577276901

theorem tailTrace_5024 : CollatzResearch.WordTrace tailWord_5024 prefixEnd_5024 2579726808293577276901 := by
  unfold tailWord_5024
  simp only [CollatzResearch.WordTrace]
  refine ⟨91620166903190437999063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122160222537587250665417 91620166903190437999063)
  ·
    refine ⟨137430250354785656998595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91620166903190437999063 137430250354785656998595)
    ·
      refine ⟨206145375532178485497893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137430250354785656998595 206145375532178485497893)
      ·
        refine ⟨38652257912283466030855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 206145375532178485497893 38652257912283466030855)
        ·
          refine ⟨57978386868425199046283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38652257912283466030855 57978386868425199046283)
          ·
            refine ⟨86967580302637798569425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57978386868425199046283 86967580302637798569425)
            ·
              refine ⟨65225685226978348927069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86967580302637798569425 65225685226978348927069)
              ·
                refine ⟨24459631960116880847651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65225685226978348927069 24459631960116880847651)
                ·
                  refine ⟨36689447940175321271477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24459631960116880847651 36689447940175321271477)
                  ·
                    refine ⟨3439635744391436369201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36689447940175321271477 3439635744391436369201)
                    ·
                      refine ⟨2579726808293577276901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3439635744391436369201 2579726808293577276901)
                      ·
                        rfl

theorem cell23_5024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_5024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024 prefixEnd_5024 := by exact prefixLift 5024
  have htrace : WordTrace (prefixWord ++ tailWord_5024) baseStart_5024 baseEnd_5024 := by
    simpa [prefixWord, tailWord_5024, baseEnd_5024] using wordTrace_append hprefix tailTrace_5024
  have hstable : (prefixWord ++ tailWord_5024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024).length < 2 ^ (prefixWord ++ tailWord_5024).sum := by decide
  have hdescent : baseEnd_5024 < baseStart_5024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048 : List Nat := [2, 1, 2, 1, 2, 5, 1, 4, 1, 1, 3]
def baseStart_5048 : Nat := 118140960795 + 5048 * 2 ^ 59
def prefixEnd_5048 : Nat := 4983230072969 + 3 ^ 40 * 5048 * 2
def baseEnd_5048 : Nat := 2592050344001483376791

theorem tailTrace_5048 : CollatzResearch.WordTrace tailWord_5048 prefixEnd_5048 2592050344001483376791 := by
  unfold tailWord_5048
  simp only [CollatzResearch.WordTrace]
  refine ⟨92057842859716487435899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122743790479621983247865 92057842859716487435899)
  ·
    refine ⟨138086764289574731153849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92057842859716487435899 138086764289574731153849)
    ·
      refine ⟨103565073217181048365387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138086764289574731153849 103565073217181048365387)
      ·
        refine ⟨155347609825771572548081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103565073217181048365387 155347609825771572548081)
        ·
          refine ⟨116510707369328679411061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155347609825771572548081 116510707369328679411061)
          ·
            refine ⟨10922878815874563694787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116510707369328679411061 10922878815874563694787)
            ·
              refine ⟨16384318223811845542181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10922878815874563694787 16384318223811845542181)
              ·
                refine ⟨3072059666964721039159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16384318223811845542181 3072059666964721039159)
                ·
                  refine ⟨4608089500447081558739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3072059666964721039159 4608089500447081558739)
                  ·
                    refine ⟨6912134250670622338109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4608089500447081558739 6912134250670622338109)
                    ·
                      refine ⟨2592050344001483376791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6912134250670622338109 2592050344001483376791)
                      ·
                        rfl

theorem cell23_5048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 1, 1, 3].length) (baseStart_5048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048 prefixEnd_5048 := by exact prefixLift 5048
  have htrace : WordTrace (prefixWord ++ tailWord_5048) baseStart_5048 baseEnd_5048 := by
    simpa [prefixWord, tailWord_5048, baseEnd_5048] using wordTrace_append hprefix tailTrace_5048
  have hstable : (prefixWord ++ tailWord_5048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048).length < 2 ^ (prefixWord ++ tailWord_5048).sum := by decide
  have hdescent : baseEnd_5048 < baseStart_5048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_5054 : Nat := 118140960795 + 5054 * 2 ^ 59
def prefixEnd_5054 : Nat := 4983230072969 + 3 ^ 40 * 5054 * 2
def baseEnd_5054 : Nat := 2595131227928459901763

theorem tailTrace_5054 : CollatzResearch.WordTrace tailWord_5054 prefixEnd_5054 2595131227928459901763 := by
  unfold tailWord_5054
  simp only [CollatzResearch.WordTrace]
  refine ⟨23041815462211999948777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122889682465130666393477 23041815462211999948777)
  ·
    refine ⟨17281361596658999961583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23041815462211999948777 17281361596658999961583)
    ·
      refine ⟨25922042394988499942375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17281361596658999961583 25922042394988499942375)
      ·
        refine ⟨38883063592482749913563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25922042394988499942375 38883063592482749913563)
        ·
          refine ⟨58324595388724124870345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38883063592482749913563 58324595388724124870345)
          ·
            refine ⟨43743446541543093652759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58324595388724124870345 43743446541543093652759)
            ·
              refine ⟨65615169812314640479139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43743446541543093652759 65615169812314640479139)
              ·
                refine ⟨98422754718471960718709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65615169812314640479139 98422754718471960718709)
                ·
                  refine ⟨9227133254856746317379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98422754718471960718709 9227133254856746317379)
                  ·
                    refine ⟨13840699882285119476069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9227133254856746317379 13840699882285119476069)
                    ·
                      refine ⟨2595131227928459901763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13840699882285119476069 2595131227928459901763)
                      ·
                        rfl

theorem cell23_5054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_5054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054 prefixEnd_5054 := by exact prefixLift 5054
  have htrace : WordTrace (prefixWord ++ tailWord_5054) baseStart_5054 baseEnd_5054 := by
    simpa [prefixWord, tailWord_5054, baseEnd_5054] using wordTrace_append hprefix tailTrace_5054
  have hstable : (prefixWord ++ tailWord_5054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054).length < 2 ^ (prefixWord ++ tailWord_5054).sum := by decide
  have hdescent : baseEnd_5054 < baseStart_5054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069 : List Nat := [1, 6, 3, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_5069 : Nat := 118140960795 + 5069 * 2 ^ 59
def prefixEnd_5069 : Nat := 4983230072969 + 3 ^ 40 * 5069 * 2
def baseEnd_5069 : Nat := 2602833437745901214195

theorem tailTrace_5069 : CollatzResearch.WordTrace tailWord_5069 prefixEnd_5069 2602833437745901214195 := by
  unfold tailWord_5069
  simp only [CollatzResearch.WordTrace]
  refine ⟨184881618643353561386261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123254412428902374257507 184881618643353561386261)
  ·
    refine ⟨8666325873907198189981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 184881618643353561386261 8666325873907198189981)
    ·
      refine ⟨3249872202715199321243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8666325873907198189981 3249872202715199321243)
      ·
        refine ⟨4874808304072798981865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3249872202715199321243 4874808304072798981865)
        ·
          refine ⟨3656106228054599236399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4874808304072798981865 3656106228054599236399)
          ·
            refine ⟨5484159342081898854599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3656106228054599236399 5484159342081898854599)
            ·
              refine ⟨8226239013122848281899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5484159342081898854599 8226239013122848281899)
              ·
                refine ⟨12339358519684272422849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8226239013122848281899 12339358519684272422849)
                ·
                  refine ⟨9254518889763204317137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12339358519684272422849 9254518889763204317137)
                  ·
                    refine ⟨6940889167322403237853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9254518889763204317137 6940889167322403237853)
                    ·
                      refine ⟨2602833437745901214195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6940889167322403237853 2602833437745901214195)
                      ·
                        rfl

theorem cell23_5069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_5069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069 prefixEnd_5069 := by exact prefixLift 5069
  have htrace : WordTrace (prefixWord ++ tailWord_5069) baseStart_5069 baseEnd_5069 := by
    simpa [prefixWord, tailWord_5069, baseEnd_5069] using wordTrace_append hprefix tailTrace_5069
  have hstable : (prefixWord ++ tailWord_5069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069).length < 2 ^ (prefixWord ++ tailWord_5069).sum := by decide
  have hdescent : baseEnd_5069 < baseStart_5069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 5, 2, 2]
def baseStart_5071 : Nat := 118140960795 + 5071 * 2 ^ 59
def prefixEnd_5071 : Nat := 4983230072969 + 3 ^ 40 * 5071 * 2
def baseEnd_5071 : Nat := 2603860399054893389185

theorem tailTrace_5071 : CollatzResearch.WordTrace tailWord_5071 prefixEnd_5071 2603860399054893389185 := by
  unfold tailWord_5071
  simp only [CollatzResearch.WordTrace]
  refine ⟨184954564636107902959067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123303043090738601972711 184954564636107902959067)
  ·
    refine ⟨277431846954161854438601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184954564636107902959067 277431846954161854438601)
    ·
      refine ⟨208073885215621390828951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277431846954161854438601 208073885215621390828951)
      ·
        refine ⟨312110827823432086243427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208073885215621390828951 312110827823432086243427)
        ·
          refine ⟨468166241735148129365141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312110827823432086243427 468166241735148129365141)
          ·
            refine ⟨21945292581335068563991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 468166241735148129365141 21945292581335068563991)
            ·
              refine ⟨32917938872002602845987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21945292581335068563991 32917938872002602845987)
              ·
                refine ⟨49376908308003904268981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32917938872002602845987 49376908308003904268981)
                ·
                  refine ⟨4629085153875366025217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49376908308003904268981 4629085153875366025217)
                  ·
                    refine ⟨3471813865406524518913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4629085153875366025217 3471813865406524518913)
                    ·
                      refine ⟨2603860399054893389185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3471813865406524518913 2603860399054893389185)
                      ·
                        rfl

theorem cell23_5071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 2, 2].length) (baseStart_5071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071 prefixEnd_5071 := by exact prefixLift 5071
  have htrace : WordTrace (prefixWord ++ tailWord_5071) baseStart_5071 baseEnd_5071 := by
    simpa [prefixWord, tailWord_5071, baseEnd_5071] using wordTrace_append hprefix tailTrace_5071
  have hstable : (prefixWord ++ tailWord_5071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071).length < 2 ^ (prefixWord ++ tailWord_5071).sum := by decide
  have hdescent : baseEnd_5071 < baseStart_5071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5091 : List Nat := [1, 1, 1, 6, 1, 1, 3, 3, 1, 2, 3]
def baseStart_5091 : Nat := 118140960795 + 5091 * 2 ^ 59
def prefixEnd_5091 : Nat := 4983230072969 + 3 ^ 40 * 5091 * 2
def baseEnd_5091 : Nat := 2614130012144815139093

theorem tailTrace_5091 : CollatzResearch.WordTrace tailWord_5091 prefixEnd_5091 2614130012144815139093 := by
  unfold tailWord_5091
  simp only [CollatzResearch.WordTrace]
  refine ⟨185684024563651318687127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123789349709100879124751 185684024563651318687127)
  ·
    refine ⟨278526036845476978030691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185684024563651318687127 278526036845476978030691)
    ·
      refine ⟨417789055268215467046037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278526036845476978030691 417789055268215467046037)
      ·
        refine ⟨19583861965697600017783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 417789055268215467046037 19583861965697600017783)
        ·
          refine ⟨29375792948546400026675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19583861965697600017783 29375792948546400026675)
          ·
            refine ⟨44063689422819600040013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29375792948546400026675 44063689422819600040013)
            ·
              refine ⟨16523883533557350015005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44063689422819600040013 16523883533557350015005)
              ·
                refine ⟨6196456325084006255627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16523883533557350015005 6196456325084006255627)
                ·
                  refine ⟨9294684487626009383441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6196456325084006255627 9294684487626009383441)
                  ·
                    refine ⟨6971013365719507037581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9294684487626009383441 6971013365719507037581)
                    ·
                      refine ⟨2614130012144815139093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6971013365719507037581 2614130012144815139093)
                      ·
                        rfl

theorem cell23_5091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_5091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5091 prefixEnd_5091 := by exact prefixLift 5091
  have htrace : WordTrace (prefixWord ++ tailWord_5091) baseStart_5091 baseEnd_5091 := by
    simpa [prefixWord, tailWord_5091, baseEnd_5091] using wordTrace_append hprefix tailTrace_5091
  have hstable : (prefixWord ++ tailWord_5091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5091).length < 2 ^ (prefixWord ++ tailWord_5091).sum := by decide
  have hdescent : baseEnd_5091 < baseStart_5091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098 : List Nat := [3, 1, 3, 1, 2, 4, 1, 2, 2, 4]
def baseStart_5098 : Nat := 118140960795 + 5098 * 2 ^ 59
def prefixEnd_5098 : Nat := 4983230072969 + 3 ^ 40 * 5098 * 2
def baseEnd_5098 : Nat := 872574792242095917187

theorem tailTrace_5098 : CollatzResearch.WordTrace tailWord_5098 prefixEnd_5098 872574792242095917187 := by
  unfold tailWord_5098
  simp only [CollatzResearch.WordTrace]
  refine ⟨46484833884572878547987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123959557025527676127965 46484833884572878547987)
  ·
    refine ⟨69727250826859317821981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46484833884572878547987 69727250826859317821981)
    ·
      refine ⟨26147719060072244183243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69727250826859317821981 26147719060072244183243)
      ·
        refine ⟨39221578590108366274865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26147719060072244183243 39221578590108366274865)
        ·
          refine ⟨29416183942581274706149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39221578590108366274865 29416183942581274706149)
          ·
            refine ⟨5515534489233989007403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29416183942581274706149 5515534489233989007403)
            ·
              refine ⟨8273301733850983511105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5515534489233989007403 8273301733850983511105)
              ·
                refine ⟨6204976300388237633329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8273301733850983511105 6204976300388237633329)
                ·
                  refine ⟨4653732225291178224997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6204976300388237633329 4653732225291178224997)
                  ·
                    refine ⟨872574792242095917187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4653732225291178224997 872574792242095917187)
                    ·
                      rfl

theorem cell23_5098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_5098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098 prefixEnd_5098 := by exact prefixLift 5098
  have htrace : WordTrace (prefixWord ++ tailWord_5098) baseStart_5098 baseEnd_5098 := by
    simpa [prefixWord, tailWord_5098, baseEnd_5098] using wordTrace_append hprefix tailTrace_5098
  have hstable : (prefixWord ++ tailWord_5098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098).length < 2 ^ (prefixWord ++ tailWord_5098).sum := by decide
  have hdescent : baseEnd_5098 < baseStart_5098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105 : List Nat := [1, 2, 2, 2, 4, 1, 2, 4, 1, 2, 2]
def baseStart_5105 : Nat := 118140960795 + 5105 * 2 ^ 59
def prefixEnd_5105 : Nat := 4983230072969 + 3 ^ 40 * 5105 * 2
def baseEnd_5105 : Nat := 2621318741307760364029

theorem tailTrace_5105 : CollatzResearch.WordTrace tailWord_5105 prefixEnd_5105 2621318741307760364029 := by
  unfold tailWord_5105
  simp only [CollatzResearch.WordTrace]
  refine ⟨186194646512931709696769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124129764341954473131179 186194646512931709696769)
  ·
    refine ⟨139645984884698782272577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186194646512931709696769 139645984884698782272577)
    ·
      refine ⟨104734488663524086704433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139645984884698782272577 104734488663524086704433)
      ·
        refine ⟨78550866497643065028325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104734488663524086704433 78550866497643065028325)
        ·
          refine ⟨14728287468308074692811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78550866497643065028325 14728287468308074692811)
          ·
            refine ⟨22092431202462112039217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14728287468308074692811 22092431202462112039217)
            ·
              refine ⟨16569323401846584029413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22092431202462112039217 16569323401846584029413)
              ·
                refine ⟨3106748137846234505515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16569323401846584029413 3106748137846234505515)
                ·
                  refine ⟨4660122206769351758273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3106748137846234505515 4660122206769351758273)
                  ·
                    refine ⟨3495091655077013818705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4660122206769351758273 3495091655077013818705)
                    ·
                      refine ⟨2621318741307760364029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3495091655077013818705 2621318741307760364029)
                      ·
                        rfl

theorem cell23_5105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 1, 2, 2].length) (baseStart_5105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105 prefixEnd_5105 := by exact prefixLift 5105
  have htrace : WordTrace (prefixWord ++ tailWord_5105) baseStart_5105 baseEnd_5105 := by
    simpa [prefixWord, tailWord_5105, baseEnd_5105] using wordTrace_append hprefix tailTrace_5105
  have hstable : (prefixWord ++ tailWord_5105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105).length < 2 ^ (prefixWord ++ tailWord_5105).sum := by decide
  have hdescent : baseEnd_5105 < baseStart_5105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121 : List Nat := [1, 2, 4, 1, 2, 2, 3, 1, 1, 3, 3]
def baseStart_5121 : Nat := 118140960795 + 5121 * 2 ^ 59
def prefixEnd_5121 : Nat := 4983230072969 + 3 ^ 40 * 5121 * 2
def baseEnd_5121 : Nat := 2629534431779697763955

theorem tailTrace_5121 : CollatzResearch.WordTrace tailWord_5121 prefixEnd_5121 2629534431779697763955 := by
  unfold tailWord_5121
  simp only [CollatzResearch.WordTrace]
  refine ⟨186778214454966442279217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124518809636644294852811 186778214454966442279217)
  ·
    refine ⟨140083660841224831709413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186778214454966442279217 140083660841224831709413)
    ·
      refine ⟨26265686407729655945515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140083660841224831709413 26265686407729655945515)
      ·
        refine ⟨39398529611594483918273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26265686407729655945515 39398529611594483918273)
        ·
          refine ⟨29548897208695862938705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39398529611594483918273 29548897208695862938705)
          ·
            refine ⟨22161672906521897204029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29548897208695862938705 22161672906521897204029)
            ·
              refine ⟨8310627339945711451511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22161672906521897204029 8310627339945711451511)
              ·
                refine ⟨12465941009918567177267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8310627339945711451511 12465941009918567177267)
                ·
                  refine ⟨18698911514877850765901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12465941009918567177267 18698911514877850765901)
                  ·
                    refine ⟨7012091818079194037213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18698911514877850765901 7012091818079194037213)
                    ·
                      refine ⟨2629534431779697763955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7012091818079194037213 2629534431779697763955)
                      ·
                        rfl

theorem cell23_5121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_5121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121 prefixEnd_5121 := by exact prefixLift 5121
  have htrace : WordTrace (prefixWord ++ tailWord_5121) baseStart_5121 baseEnd_5121 := by
    simpa [prefixWord, tailWord_5121, baseEnd_5121] using wordTrace_append hprefix tailTrace_5121
  have hstable : (prefixWord ++ tailWord_5121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121).length < 2 ^ (prefixWord ++ tailWord_5121).sum := by decide
  have hdescent : baseEnd_5121 < baseStart_5121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5134 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5]
def baseStart_5134 : Nat := 118140960795 + 5134 * 2 ^ 59
def prefixEnd_5134 : Nat := 4983230072969 + 3 ^ 40 * 5134 * 2
def baseEnd_5134 : Nat := 2636209680288146901395

theorem tailTrace_5134 : CollatzResearch.WordTrace tailWord_5134 prefixEnd_5134 2636209680288146901395 := by
  unfold tailWord_5134
  simp only [CollatzResearch.WordTrace]
  refine ⟨23406545425983707812807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124834908938579775001637 23406545425983707812807)
  ·
    refine ⟨35109818138975561719211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23406545425983707812807 35109818138975561719211)
    ·
      refine ⟨52664727208463342578817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35109818138975561719211 52664727208463342578817)
      ·
        refine ⟨39498545406347506934113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52664727208463342578817 39498545406347506934113)
        ·
          refine ⟨29623909054760630200585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39498545406347506934113 29623909054760630200585)
          ·
            refine ⟨22217931791070472650439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29623909054760630200585 22217931791070472650439)
            ·
              refine ⟨33326897686605708975659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22217931791070472650439 33326897686605708975659)
              ·
                refine ⟨49990346529908563463489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33326897686605708975659 49990346529908563463489)
                ·
                  refine ⟨37492759897431422597617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49990346529908563463489 37492759897431422597617)
                  ·
                    refine ⟨28119569923073566948213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37492759897431422597617 28119569923073566948213)
                    ·
                      refine ⟨2636209680288146901395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28119569923073566948213 2636209680288146901395)
                      ·
                        rfl

theorem cell23_5134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_5134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5134 prefixEnd_5134 := by exact prefixLift 5134
  have htrace : WordTrace (prefixWord ++ tailWord_5134) baseStart_5134 baseEnd_5134 := by
    simpa [prefixWord, tailWord_5134, baseEnd_5134] using wordTrace_append hprefix tailTrace_5134
  have hstable : (prefixWord ++ tailWord_5134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5134).length < 2 ^ (prefixWord ++ tailWord_5134).sum := by decide
  have hdescent : baseEnd_5134 < baseStart_5134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 1, 8]
def baseStart_5137 : Nat := 118140960795 + 5137 * 2 ^ 59
def prefixEnd_5137 : Nat := 4983230072969 + 3 ^ 40 * 5137 * 2
def baseEnd_5137 : Nat := 879250040750545054627

theorem tailTrace_5137 : CollatzResearch.WordTrace tailWord_5137 prefixEnd_5137 879250040750545054627 := by
  unfold tailWord_5137
  simp only [CollatzResearch.WordTrace]
  refine ⟨187361782397001174861665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124907854931334116574443 187361782397001174861665)
  ·
    refine ⟨140521336797750881146249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187361782397001174861665 140521336797750881146249)
    ·
      refine ⟨105391002598313160859687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140521336797750881146249 105391002598313160859687)
      ·
        refine ⟨158086503897469741289531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105391002598313160859687 158086503897469741289531)
        ·
          refine ⟨237129755846204611934297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158086503897469741289531 237129755846204611934297)
          ·
            refine ⟨177847316884653458950723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237129755846204611934297 177847316884653458950723)
            ·
              refine ⟨266770975326980188426085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177847316884653458950723 266770975326980188426085)
              ·
                refine ⟨50019557873808785329891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 266770975326980188426085 50019557873808785329891)
                ·
                  refine ⟨75029336810713177994837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50019557873808785329891 75029336810713177994837)
                  ·
                    refine ⟨879250040750545054627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75029336810713177994837 879250040750545054627)
                    ·
                      rfl

theorem cell23_5137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_5137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137 prefixEnd_5137 := by exact prefixLift 5137
  have htrace : WordTrace (prefixWord ++ tailWord_5137) baseStart_5137 baseEnd_5137 := by
    simpa [prefixWord, tailWord_5137, baseEnd_5137] using wordTrace_append hprefix tailTrace_5137
  have hstable : (prefixWord ++ tailWord_5137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137).length < 2 ^ (prefixWord ++ tailWord_5137).sum := by decide
  have hdescent : baseEnd_5137 < baseStart_5137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 3]
def baseStart_5164 : Nat := 118140960795 + 5164 * 2 ^ 59
def prefixEnd_5164 : Nat := 4983230072969 + 3 ^ 40 * 5164 * 2
def baseEnd_5164 : Nat := 2651614099923029526257

theorem tailTrace_5164 : CollatzResearch.WordTrace tailWord_5164 prefixEnd_5164 2651614099923029526257 := by
  unfold tailWord_5164
  simp only [CollatzResearch.WordTrace]
  refine ⟨94173276649592393047273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125564368866123190729697 94173276649592393047273)
  ·
    refine ⟨70629957487194294785455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94173276649592393047273 70629957487194294785455)
    ·
      refine ⟨105944936230791442178183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70629957487194294785455 105944936230791442178183)
      ·
        refine ⟨158917404346187163267275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105944936230791442178183 158917404346187163267275)
        ·
          refine ⟨238376106519280744900913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158917404346187163267275 238376106519280744900913)
          ·
            refine ⟨178782079889460558675685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238376106519280744900913 178782079889460558675685)
            ·
              refine ⟨33521639979273854751691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 178782079889460558675685 33521639979273854751691)
              ·
                refine ⟨50282459968910782127537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33521639979273854751691 50282459968910782127537)
                ·
                  refine ⟨37711844976683086595653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50282459968910782127537 37711844976683086595653)
                  ·
                    refine ⟨7070970933128078736685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37711844976683086595653 7070970933128078736685)
                    ·
                      refine ⟨2651614099923029526257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7070970933128078736685 2651614099923029526257)
                      ·
                        rfl

theorem cell23_5164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 3].length) (baseStart_5164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164 prefixEnd_5164 := by exact prefixLift 5164
  have htrace : WordTrace (prefixWord ++ tailWord_5164) baseStart_5164 baseEnd_5164 := by
    simpa [prefixWord, tailWord_5164, baseEnd_5164] using wordTrace_append hprefix tailTrace_5164
  have hstable : (prefixWord ++ tailWord_5164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164).length < 2 ^ (prefixWord ++ tailWord_5164).sum := by decide
  have hdescent : baseEnd_5164 < baseStart_5164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172 : List Nat := [2, 5, 1, 2, 1, 1, 4, 1, 2, 1, 3]
def baseStart_5172 : Nat := 118140960795 + 5172 * 2 ^ 59
def prefixEnd_5172 : Nat := 4983230072969 + 3 ^ 40 * 5172 * 2
def baseEnd_5172 : Nat := 2655721945158998226221

theorem tailTrace_5172 : CollatzResearch.WordTrace tailWord_5172 prefixEnd_5172 2655721945158998226221 := by
  unfold tailWord_5172
  simp only [CollatzResearch.WordTrace]
  refine ⟨94319168635101076192885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125758891513468101590513 94319168635101076192885)
  ·
    refine ⟨8842422059540725893083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94319168635101076192885 8842422059540725893083)
    ·
      refine ⟨13263633089311088839625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8842422059540725893083 13263633089311088839625)
      ·
        refine ⟨9947724816983316629719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13263633089311088839625 9947724816983316629719)
        ·
          refine ⟨14921587225474974944579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9947724816983316629719 14921587225474974944579)
          ·
            refine ⟨22382380838212462416869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14921587225474974944579 22382380838212462416869)
            ·
              refine ⟨4196696407164836703163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22382380838212462416869 4196696407164836703163)
              ·
                refine ⟨6295044610747255054745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4196696407164836703163 6295044610747255054745)
                ·
                  refine ⟨4721283458060441291059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6295044610747255054745 4721283458060441291059)
                  ·
                    refine ⟨7081925187090661936589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4721283458060441291059 7081925187090661936589)
                    ·
                      refine ⟨2655721945158998226221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7081925187090661936589 2655721945158998226221)
                      ·
                        rfl

theorem cell23_5172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_5172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172 prefixEnd_5172 := by exact prefixLift 5172
  have htrace : WordTrace (prefixWord ++ tailWord_5172) baseStart_5172 baseEnd_5172 := by
    simpa [prefixWord, tailWord_5172, baseEnd_5172] using wordTrace_append hprefix tailTrace_5172
  have hstable : (prefixWord ++ tailWord_5172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172).length < 2 ^ (prefixWord ++ tailWord_5172).sum := by decide
  have hdescent : baseEnd_5172 < baseStart_5172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5182 : List Nat := [4, 2, 1, 3, 1, 3, 1, 2, 1, 3, 2]
def baseStart_5182 : Nat := 118140960795 + 5182 * 2 ^ 59
def prefixEnd_5182 : Nat := 4983230072969 + 3 ^ 40 * 5182 * 2
def baseEnd_5182 : Nat := 2660856751703959101175

theorem tailTrace_5182 : CollatzResearch.WordTrace tailWord_5182 prefixEnd_5182 2660856751703959101175 := by
  unfold tailWord_5182
  simp only [CollatzResearch.WordTrace]
  refine ⟨23625383404246732531225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126002044822649240166533 23625383404246732531225)
  ·
    refine ⟨17719037553185049398419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23625383404246732531225 17719037553185049398419)
    ·
      refine ⟨26578556329777574097629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17719037553185049398419 26578556329777574097629)
      ·
        refine ⟨9966958623666590286611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26578556329777574097629 9966958623666590286611)
        ·
          refine ⟨14950437935499885429917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9966958623666590286611 14950437935499885429917)
          ·
            refine ⟨5606414225812457036219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14950437935499885429917 5606414225812457036219)
            ·
              refine ⟨8409621338718685554329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5606414225812457036219 8409621338718685554329)
              ·
                refine ⟨6307216004039014165747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8409621338718685554329 6307216004039014165747)
                ·
                  refine ⟨9460824006058521248621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6307216004039014165747 9460824006058521248621)
                  ·
                    refine ⟨3547809002271945468233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9460824006058521248621 3547809002271945468233)
                    ·
                      refine ⟨2660856751703959101175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3547809002271945468233 2660856751703959101175)
                      ·
                        rfl

theorem cell23_5182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_5182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5182 prefixEnd_5182 := by exact prefixLift 5182
  have htrace : WordTrace (prefixWord ++ tailWord_5182) baseStart_5182 baseEnd_5182 := by
    simpa [prefixWord, tailWord_5182, baseEnd_5182] using wordTrace_append hprefix tailTrace_5182
  have hstable : (prefixWord ++ tailWord_5182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5182).length < 2 ^ (prefixWord ++ tailWord_5182).sum := by decide
  have hdescent : baseEnd_5182 < baseStart_5182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 1, 7, 2]
def baseStart_5221 : Nat := 118140960795 + 5221 * 2 ^ 59
def prefixEnd_5221 : Nat := 4983230072969 + 3 ^ 40 * 5221 * 2
def baseEnd_5221 : Nat := 2680882497229306513495

theorem tailTrace_5221 : CollatzResearch.WordTrace tailWord_5221 prefixEnd_5221 2680882497229306513495 := by
  unfold tailWord_5221
  simp only [CollatzResearch.WordTrace]
  refine ⟨190425514092683520919517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126950342728455680613011 190425514092683520919517)
  ·
    refine ⟨71409567784756320344819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190425514092683520919517 71409567784756320344819)
    ·
      refine ⟨107114351677134480517229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71409567784756320344819 107114351677134480517229)
      ·
        refine ⟨40167881878925430193961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107114351677134480517229 40167881878925430193961)
        ·
          refine ⟨30125911409194072645471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40167881878925430193961 30125911409194072645471)
          ·
            refine ⟨45188867113791108968207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30125911409194072645471 45188867113791108968207)
            ·
              refine ⟨67783300670686663452311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45188867113791108968207 67783300670686663452311)
              ·
                refine ⟨101674951006029995178467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67783300670686663452311 101674951006029995178467)
                ·
                  refine ⟨152512426509044992767701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101674951006029995178467 152512426509044992767701)
                  ·
                    refine ⟨3574509996305742017993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 152512426509044992767701 3574509996305742017993)
                    ·
                      refine ⟨2680882497229306513495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3574509996305742017993 2680882497229306513495)
                      ·
                        rfl

theorem cell23_5221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_5221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221 prefixEnd_5221 := by exact prefixLift 5221
  have htrace : WordTrace (prefixWord ++ tailWord_5221) baseStart_5221 baseEnd_5221 := by
    simpa [prefixWord, tailWord_5221, baseEnd_5221] using wordTrace_append hprefix tailTrace_5221
  have hstable : (prefixWord ++ tailWord_5221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221).length < 2 ^ (prefixWord ++ tailWord_5221).sum := by decide
  have hdescent : baseEnd_5221 < baseStart_5221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2]
def baseStart_5238 : Nat := 118140960795 + 5238 * 2 ^ 59
def prefixEnd_5238 : Nat := 4983230072969 + 3 ^ 40 * 5238 * 2
def baseEnd_5238 : Nat := 2689611668355740000917

theorem tailTrace_5238 : CollatzResearch.WordTrace tailWord_5238 prefixEnd_5238 2689611668355740000917 := by
  unfold tailWord_5238
  simp only [CollatzResearch.WordTrace]
  refine ⟨11940347189443464018023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127363703354063616192245 11940347189443464018023)
  ·
    refine ⟨17910520784165196027035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11940347189443464018023 17910520784165196027035)
    ·
      refine ⟨26865781176247794040553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17910520784165196027035 26865781176247794040553)
      ·
        refine ⟨20149335882185845530415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26865781176247794040553 20149335882185845530415)
        ·
          refine ⟨30224003823278768295623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20149335882185845530415 30224003823278768295623)
          ·
            refine ⟨45336005734918152443435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30224003823278768295623 45336005734918152443435)
            ·
              refine ⟨68004008602377228665153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45336005734918152443435 68004008602377228665153)
              ·
                refine ⟨51003006451782921498865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68004008602377228665153 51003006451782921498865)
                ·
                  refine ⟨38252254838837191124149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51003006451782921498865 38252254838837191124149)
                  ·
                    refine ⟨3586148891140986667889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38252254838837191124149 3586148891140986667889)
                    ·
                      refine ⟨2689611668355740000917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3586148891140986667889 2689611668355740000917)
                      ·
                        rfl

theorem cell23_5238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_5238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238 prefixEnd_5238 := by exact prefixLift 5238
  have htrace : WordTrace (prefixWord ++ tailWord_5238) baseStart_5238 baseEnd_5238 := by
    simpa [prefixWord, tailWord_5238, baseEnd_5238] using wordTrace_append hprefix tailTrace_5238
  have hstable : (prefixWord ++ tailWord_5238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238).length < 2 ^ (prefixWord ++ tailWord_5238).sum := by decide
  have hdescent : baseEnd_5238 < baseStart_5238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 1, 6, 2]
def baseStart_5251 : Nat := 118140960795 + 5251 * 2 ^ 59
def prefixEnd_5251 : Nat := 4983230072969 + 3 ^ 40 * 5251 * 2
def baseEnd_5251 : Nat := 2696286916864189138357

theorem tailTrace_5251 : CollatzResearch.WordTrace tailWord_5251 prefixEnd_5251 2696286916864189138357 := by
  unfold tailWord_5251
  simp only [CollatzResearch.WordTrace]
  refine ⟨191519703983998644511607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127679802655999096341071 191519703983998644511607)
  ·
    refine ⟨287279555975997966767411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191519703983998644511607 287279555975997966767411)
    ·
      refine ⟨430919333963996950151117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287279555975997966767411 430919333963996950151117)
      ·
        refine ⟨161594750236498856306669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 430919333963996950151117 161594750236498856306669)
        ·
          refine ⟨60598031338687071115001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161594750236498856306669 60598031338687071115001)
          ·
            refine ⟨45448523504015303336251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60598031338687071115001 45448523504015303336251)
            ·
              refine ⟨68172785256022955004377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45448523504015303336251 68172785256022955004377)
              ·
                refine ⟨51129588942017216253283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68172785256022955004377 51129588942017216253283)
                ·
                  refine ⟨76694383413025824379925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51129588942017216253283 76694383413025824379925)
                  ·
                    refine ⟨3595049222485585517809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76694383413025824379925 3595049222485585517809)
                    ·
                      refine ⟨2696286916864189138357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3595049222485585517809 2696286916864189138357)
                      ·
                        rfl

theorem cell23_5251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 6, 2].length) (baseStart_5251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251 prefixEnd_5251 := by exact prefixLift 5251
  have htrace : WordTrace (prefixWord ++ tailWord_5251) baseStart_5251 baseEnd_5251 := by
    simpa [prefixWord, tailWord_5251, baseEnd_5251] using wordTrace_append hprefix tailTrace_5251
  have hstable : (prefixWord ++ tailWord_5251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251).length < 2 ^ (prefixWord ++ tailWord_5251).sum := by decide
  have hdescent : baseEnd_5251 < baseStart_5251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312 : List Nat := [2, 1, 1, 2, 6, 2, 1, 3, 1, 4]
def baseStart_5312 : Nat := 118140960795 + 5312 * 2 ^ 59
def prefixEnd_5312 : Nat := 4983230072969 + 3 ^ 40 * 5312 * 2
def baseEnd_5312 : Nat := 909203078929483491859

theorem tailTrace_5312 : CollatzResearch.WordTrace tailWord_5312 prefixEnd_5312 909203078929483491859 := by
  unfold tailWord_5312
  simp only [CollatzResearch.WordTrace]
  refine ⟨96872278381503031241095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129163037842004041654793 96872278381503031241095)
  ·
    refine ⟨145308417572254546861643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96872278381503031241095 145308417572254546861643)
    ·
      refine ⟨217962626358381820292465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145308417572254546861643 217962626358381820292465)
      ·
        refine ⟨163471969768786365219349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217962626358381820292465 163471969768786365219349)
        ·
          refine ⟨7662748582911860869657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 163471969768786365219349 7662748582911860869657)
          ·
            refine ⟨5747061437183895652243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7662748582911860869657 5747061437183895652243)
            ·
              refine ⟨8620592155775843478365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5747061437183895652243 8620592155775843478365)
              ·
                refine ⟨3232722058415941304387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8620592155775843478365 3232722058415941304387)
                ·
                  refine ⟨4849083087623911956581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3232722058415941304387 4849083087623911956581)
                  ·
                    refine ⟨909203078929483491859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4849083087623911956581 909203078929483491859)
                    ·
                      rfl

theorem cell23_5312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 1, 4].length) (baseStart_5312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312 prefixEnd_5312 := by exact prefixLift 5312
  have htrace : WordTrace (prefixWord ++ tailWord_5312) baseStart_5312 baseEnd_5312 := by
    simpa [prefixWord, tailWord_5312, baseEnd_5312] using wordTrace_append hprefix tailTrace_5312
  have hstable : (prefixWord ++ tailWord_5312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312).length < 2 ^ (prefixWord ++ tailWord_5312).sum := by decide
  have hdescent : baseEnd_5312 < baseStart_5312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5335 : List Nat := [1, 1, 3, 2, 1, 2, 2, 6, 1, 1, 3]
def baseStart_5335 : Nat := 118140960795 + 5335 * 2 ^ 59
def prefixEnd_5335 : Nat := 4983230072969 + 3 ^ 40 * 5335 * 2
def baseEnd_5335 : Nat := 2739419291841860487971

theorem tailTrace_5335 : CollatzResearch.WordTrace tailWord_5335 prefixEnd_5335 2739419291841860487971 := by
  unfold tailWord_5335
  simp only [CollatzResearch.WordTrace]
  refine ⟨194583435679680990569459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129722290453120660379639 194583435679680990569459)
  ·
    refine ⟨291875153519521485854189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194583435679680990569459 291875153519521485854189)
    ·
      refine ⟨109453182569820557195321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291875153519521485854189 109453182569820557195321)
      ·
        refine ⟨82089886927365417896491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109453182569820557195321 82089886927365417896491)
        ·
          refine ⟨123134830391048126844737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82089886927365417896491 123134830391048126844737)
          ·
            refine ⟨92351122793286095133553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123134830391048126844737 92351122793286095133553)
            ·
              refine ⟨69263342094964571350165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92351122793286095133553 69263342094964571350165)
              ·
                refine ⟨3246719160701464282039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69263342094964571350165 3246719160701464282039)
                ·
                  refine ⟨4870078741052196423059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3246719160701464282039 4870078741052196423059)
                  ·
                    refine ⟨7305118111578294634589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4870078741052196423059 7305118111578294634589)
                    ·
                      refine ⟨2739419291841860487971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7305118111578294634589 2739419291841860487971)
                      ·
                        rfl

theorem cell23_5335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 1, 1, 3].length) (baseStart_5335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5335 prefixEnd_5335 := by exact prefixLift 5335
  have htrace : WordTrace (prefixWord ++ tailWord_5335) baseStart_5335 baseEnd_5335 := by
    simpa [prefixWord, tailWord_5335, baseEnd_5335] using wordTrace_append hprefix tailTrace_5335
  have hstable : (prefixWord ++ tailWord_5335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5335).length < 2 ^ (prefixWord ++ tailWord_5335).sum := by decide
  have hdescent : baseEnd_5335 < baseStart_5335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 2, 6, 2]
def baseStart_5358 : Nat := 118140960795 + 5358 * 2 ^ 59
def prefixEnd_5358 : Nat := 4983230072969 + 3 ^ 40 * 5358 * 2
def baseEnd_5358 : Nat := 2751229346895270500365

theorem tailTrace_5358 : CollatzResearch.WordTrace tailWord_5358 prefixEnd_5358 2751229346895270500365 := by
  unfold tailWord_5358
  simp only [CollatzResearch.WordTrace]
  refine ⟨24427789324544489832091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130281543064237279104485 24427789324544489832091)
  ·
    refine ⟨36641683986816734748137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24427789324544489832091 36641683986816734748137)
    ·
      refine ⟨27481262990112551061103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36641683986816734748137 27481262990112551061103)
      ·
        refine ⟨41221894485168826591655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27481262990112551061103 41221894485168826591655)
        ·
          refine ⟨61832841727753239887483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41221894485168826591655 61832841727753239887483)
          ·
            refine ⟨92749262591629859831225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61832841727753239887483 92749262591629859831225)
            ·
              refine ⟨69561946943722394873419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92749262591629859831225 69561946943722394873419)
              ·
                refine ⟨104342920415583592310129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69561946943722394873419 104342920415583592310129)
                ·
                  refine ⟨78257190311687694232597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104342920415583592310129 78257190311687694232597)
                  ·
                    refine ⟨3668305795860360667153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78257190311687694232597 3668305795860360667153)
                    ·
                      refine ⟨2751229346895270500365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3668305795860360667153 2751229346895270500365)
                      ·
                        rfl

theorem cell23_5358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_5358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358 prefixEnd_5358 := by exact prefixLift 5358
  have htrace : WordTrace (prefixWord ++ tailWord_5358) baseStart_5358 baseEnd_5358 := by
    simpa [prefixWord, tailWord_5358, baseEnd_5358] using wordTrace_append hprefix tailTrace_5358
  have hstable : (prefixWord ++ tailWord_5358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358).length < 2 ^ (prefixWord ++ tailWord_5358).sum := by decide
  have hdescent : baseEnd_5358 < baseStart_5358 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362 : List Nat := [3, 2, 1, 3, 3, 1, 2, 1, 2, 3, 2]
def baseStart_5362 : Nat := 118140960795 + 5362 * 2 ^ 59
def prefixEnd_5362 : Nat := 4983230072969 + 3 ^ 40 * 5362 * 2
def baseEnd_5362 : Nat := 2753283269513254850347

theorem tailTrace_5362 : CollatzResearch.WordTrace tailWord_5362 prefixEnd_5362 2753283269513254850347 := by
  unfold tailWord_5362
  simp only [CollatzResearch.WordTrace]
  refine ⟨48892051645466150450585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130378804387909734534893 48892051645466150450585)
  ·
    refine ⟨36669038734099612837939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48892051645466150450585 36669038734099612837939)
    ·
      refine ⟨55003558101149419256909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36669038734099612837939 55003558101149419256909)
      ·
        refine ⟨20626334287931032221341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55003558101149419256909 20626334287931032221341)
        ·
          refine ⟨7734875357974137083003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20626334287931032221341 7734875357974137083003)
          ·
            refine ⟨11602313036961205624505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7734875357974137083003 11602313036961205624505)
            ·
              refine ⟨8701734777720904218379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11602313036961205624505 8701734777720904218379)
              ·
                refine ⟨13052602166581356327569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8701734777720904218379 13052602166581356327569)
                ·
                  refine ⟨9789451624936017245677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13052602166581356327569 9789451624936017245677)
                  ·
                    refine ⟨3671044359351006467129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9789451624936017245677 3671044359351006467129)
                    ·
                      refine ⟨2753283269513254850347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3671044359351006467129 2753283269513254850347)
                      ·
                        rfl

theorem cell23_5362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_5362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362 prefixEnd_5362 := by exact prefixLift 5362
  have htrace : WordTrace (prefixWord ++ tailWord_5362) baseStart_5362 baseEnd_5362 := by
    simpa [prefixWord, tailWord_5362, baseEnd_5362] using wordTrace_append hprefix tailTrace_5362
  have hstable : (prefixWord ++ tailWord_5362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362).length < 2 ^ (prefixWord ++ tailWord_5362).sum := by decide
  have hdescent : baseEnd_5362 < baseStart_5362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375 : List Nat := [1, 1, 2, 2, 1, 6, 3, 1, 1, 1, 4]
def baseStart_5375 : Nat := 118140960795 + 5375 * 2 ^ 59
def prefixEnd_5375 : Nat := 4983230072969 + 3 ^ 40 * 5375 * 2
def baseEnd_5375 : Nat := 2759958518021703987787

theorem tailTrace_5375 : CollatzResearch.WordTrace tailWord_5375 prefixEnd_5375 2759958518021703987787 := by
  unfold tailWord_5375
  simp only [CollatzResearch.WordTrace]
  refine ⟨196042355534767822025579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130694903689845214683719 196042355534767822025579)
  ·
    refine ⟨294063533302151733038369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196042355534767822025579 294063533302151733038369)
    ·
      refine ⟨220547649976613799778777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294063533302151733038369 220547649976613799778777)
      ·
        refine ⟨165410737482460349834083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220547649976613799778777 165410737482460349834083)
        ·
          refine ⟨248116106223690524751125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165410737482460349834083 248116106223690524751125)
          ·
            refine ⟨11630442479235493347709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 248116106223690524751125 11630442479235493347709)
            ·
              refine ⟨4361415929713310005391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11630442479235493347709 4361415929713310005391)
              ·
                refine ⟨6542123894569965008087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4361415929713310005391 6542123894569965008087)
                ·
                  refine ⟨9813185841854947512131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6542123894569965008087 9813185841854947512131)
                  ·
                    refine ⟨14719778762782421268197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9813185841854947512131 14719778762782421268197)
                    ·
                      refine ⟨2759958518021703987787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14719778762782421268197 2759958518021703987787)
                      ·
                        rfl

theorem cell23_5375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 1, 1, 4].length) (baseStart_5375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375 prefixEnd_5375 := by exact prefixLift 5375
  have htrace : WordTrace (prefixWord ++ tailWord_5375) baseStart_5375 baseEnd_5375 := by
    simpa [prefixWord, tailWord_5375, baseEnd_5375] using wordTrace_append hprefix tailTrace_5375
  have hstable : (prefixWord ++ tailWord_5375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375).length < 2 ^ (prefixWord ++ tailWord_5375).sum := by decide
  have hdescent : baseEnd_5375 < baseStart_5375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405 : List Nat := [1, 4, 2, 3, 1, 2, 2, 1, 1, 2, 4]
def baseStart_5405 : Nat := 118140960795 + 5405 * 2 ^ 59
def prefixEnd_5405 : Nat := 4983230072969 + 3 ^ 40 * 5405 * 2
def baseEnd_5405 : Nat := 2775362937656586612649

theorem tailTrace_5405 : CollatzResearch.WordTrace tailWord_5405 prefixEnd_5405 2775362937656586612649 := by
  unfold tailWord_5405
  simp only [CollatzResearch.WordTrace]
  refine ⟨197136545426082945617669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131424363617388630411779 197136545426082945617669)
  ·
    refine ⟨36963102267390552303313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197136545426082945617669 36963102267390552303313)
    ·
      refine ⟨27722326700542914227485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36963102267390552303313 27722326700542914227485)
      ·
        refine ⟨10395872512703592835307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27722326700542914227485 10395872512703592835307)
        ·
          refine ⟨15593808769055389252961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10395872512703592835307 15593808769055389252961)
          ·
            refine ⟨11695356576791541939721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15593808769055389252961 11695356576791541939721)
            ·
              refine ⟨8771517432593656454791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11695356576791541939721 8771517432593656454791)
              ·
                refine ⟨13157276148890484682187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8771517432593656454791 13157276148890484682187)
                ·
                  refine ⟨19735914223335727023281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13157276148890484682187 19735914223335727023281)
                  ·
                    refine ⟨14801935667501795267461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19735914223335727023281 14801935667501795267461)
                    ·
                      refine ⟨2775362937656586612649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14801935667501795267461 2775362937656586612649)
                      ·
                        rfl

theorem cell23_5405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_5405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405 prefixEnd_5405 := by exact prefixLift 5405
  have htrace : WordTrace (prefixWord ++ tailWord_5405) baseStart_5405 baseEnd_5405 := by
    simpa [prefixWord, tailWord_5405, baseEnd_5405] using wordTrace_append hprefix tailTrace_5405
  have hstable : (prefixWord ++ tailWord_5405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405).length < 2 ^ (prefixWord ++ tailWord_5405).sum := by decide
  have hdescent : baseEnd_5405 < baseStart_5405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5465 : List Nat := [1, 2, 1, 2, 2, 2, 5, 1, 1, 4, 2]
def baseStart_5465 : Nat := 118140960795 + 5465 * 2 ^ 59
def prefixEnd_5465 : Nat := 4983230072969 + 3 ^ 40 * 5465 * 2
def baseEnd_5465 : Nat := 2806171776926351862373

theorem tailTrace_5465 : CollatzResearch.WordTrace tailWord_5465 prefixEnd_5465 2806171776926351862373 := by
  unfold tailWord_5465
  simp only [CollatzResearch.WordTrace]
  refine ⟨199324925208713192801849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132883283472475461867899 199324925208713192801849)
  ·
    refine ⟨149493693906534894601387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199324925208713192801849 149493693906534894601387)
    ·
      refine ⟨224240540859802341902081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149493693906534894601387 224240540859802341902081)
      ·
        refine ⟨168180405644851756426561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224240540859802341902081 168180405644851756426561)
        ·
          refine ⟨126135304233638817319921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168180405644851756426561 126135304233638817319921)
          ·
            refine ⟨94601478175229112989941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126135304233638817319921 94601478175229112989941)
            ·
              refine ⟨8868888578927729342807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94601478175229112989941 8868888578927729342807)
              ·
                refine ⟨13303332868391594014211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8868888578927729342807 13303332868391594014211)
                ·
                  refine ⟨19954999302587391021317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13303332868391594014211 19954999302587391021317)
                  ·
                    refine ⟨3741562369235135816497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19954999302587391021317 3741562369235135816497)
                    ·
                      refine ⟨2806171776926351862373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3741562369235135816497 2806171776926351862373)
                      ·
                        rfl

theorem cell23_5465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 4, 2].length) (baseStart_5465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5465 prefixEnd_5465 := by exact prefixLift 5465
  have htrace : WordTrace (prefixWord ++ tailWord_5465) baseStart_5465 baseEnd_5465 := by
    simpa [prefixWord, tailWord_5465, baseEnd_5465] using wordTrace_append hprefix tailTrace_5465
  have hstable : (prefixWord ++ tailWord_5465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5465).length < 2 ^ (prefixWord ++ tailWord_5465).sum := by decide
  have hdescent : baseEnd_5465 < baseStart_5465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535 : List Nat := [1, 1, 2, 5, 1, 3, 2, 1, 2, 5]
def baseStart_5535 : Nat := 118140960795 + 5535 * 2 ^ 59
def prefixEnd_5535 : Nat := 4983230072969 + 3 ^ 40 * 5535 * 2
def baseEnd_5535 : Nat := 947371807580359329017

theorem tailTrace_5535 : CollatzResearch.WordTrace tailWord_5535 prefixEnd_5535 947371807580359329017 := by
  unfold tailWord_5535
  simp only [CollatzResearch.WordTrace]
  refine ⟨201878034955115147850059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134585356636743431900039 201878034955115147850059)
  ·
    refine ⟨302817052432672721775089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201878034955115147850059 302817052432672721775089)
    ·
      refine ⟨227112789324504541331317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302817052432672721775089 227112789324504541331317)
      ·
        refine ⟨21291823999172300749811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 227112789324504541331317 21291823999172300749811)
        ·
          refine ⟨31937735998758451124717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21291823999172300749811 31937735998758451124717)
          ·
            refine ⟨11976650999534419171769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31937735998758451124717 11976650999534419171769)
            ·
              refine ⟨8982488249650814378827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11976650999534419171769 8982488249650814378827)
              ·
                refine ⟨13473732374476221568241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8982488249650814378827 13473732374476221568241)
                ·
                  refine ⟨10105299280857166176181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13473732374476221568241 10105299280857166176181)
                  ·
                    refine ⟨947371807580359329017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10105299280857166176181 947371807580359329017)
                    ·
                      rfl

theorem cell23_5535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 5].length) (baseStart_5535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535 prefixEnd_5535 := by exact prefixLift 5535
  have htrace : WordTrace (prefixWord ++ tailWord_5535) baseStart_5535 baseEnd_5535 := by
    simpa [prefixWord, tailWord_5535, baseEnd_5535] using wordTrace_append hprefix tailTrace_5535
  have hstable : (prefixWord ++ tailWord_5535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535).length < 2 ^ (prefixWord ++ tailWord_5535).sum := by decide
  have hdescent : baseEnd_5535 < baseStart_5535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565 : List Nat := [1, 4, 1, 2, 2, 1, 2, 3, 3, 4]
def baseStart_5565 : Nat := 118140960795 + 5565 * 2 ^ 59
def prefixEnd_5565 : Nat := 4983230072969 + 3 ^ 40 * 5565 * 2
def baseEnd_5565 : Nat := 952506614125320203971

theorem tailTrace_5565 : CollatzResearch.WordTrace tailWord_5565 prefixEnd_5565 952506614125320203971 := by
  unfold tailWord_5565
  simp only [CollatzResearch.WordTrace]
  refine ⟨202972224846430271442149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135314816564286847628099 202972224846430271442149)
  ·
    refine ⟨38057292158705675895403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202972224846430271442149 38057292158705675895403)
    ·
      refine ⟨57085938238058513843105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38057292158705675895403 57085938238058513843105)
      ·
        refine ⟨42814453678543885382329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57085938238058513843105 42814453678543885382329)
        ·
          refine ⟨32110840258907914036747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42814453678543885382329 32110840258907914036747)
          ·
            refine ⟨48166260388361871055121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32110840258907914036747 48166260388361871055121)
            ·
              refine ⟨36124695291271403291341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48166260388361871055121 36124695291271403291341)
              ·
                refine ⟨13546760734226776234253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36124695291271403291341 13546760734226776234253)
                ·
                  refine ⟨5080035275335041087845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13546760734226776234253 5080035275335041087845)
                  ·
                    refine ⟨952506614125320203971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5080035275335041087845 952506614125320203971)
                    ·
                      rfl

theorem cell23_5565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_5565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565 prefixEnd_5565 := by exact prefixLift 5565
  have htrace : WordTrace (prefixWord ++ tailWord_5565) baseStart_5565 baseEnd_5565 := by
    simpa [prefixWord, tailWord_5565, baseEnd_5565] using wordTrace_append hprefix tailTrace_5565
  have hstable : (prefixWord ++ tailWord_5565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565).length < 2 ^ (prefixWord ++ tailWord_5565).sum := by decide
  have hdescent : baseEnd_5565 < baseStart_5565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5572 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 1, 6, 2]
def baseStart_5572 : Nat := 118140960795 + 5572 * 2 ^ 59
def prefixEnd_5572 : Nat := 4983230072969 + 3 ^ 40 * 5572 * 2
def baseEnd_5572 : Nat := 2861114206957433224381

theorem tailTrace_5572 : CollatzResearch.WordTrace tailWord_5572 prefixEnd_5572 2861114206957433224381 := by
  unfold tailWord_5572
  simp only [CollatzResearch.WordTrace]
  refine ⟨101613767910535233473485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135485023880713644631313 101613767910535233473485)
  ·
    refine ⟨38105162966450712552557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101613767910535233473485 38105162966450712552557)
    ·
      refine ⟨14289436112419017207209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38105162966450712552557 14289436112419017207209)
      ·
        refine ⟨10717077084314262905407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14289436112419017207209 10717077084314262905407)
        ·
          refine ⟨16075615626471394358111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10717077084314262905407 16075615626471394358111)
          ·
            refine ⟨24113423439707091537167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16075615626471394358111 24113423439707091537167)
            ·
              refine ⟨36170135159560637305751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24113423439707091537167 36170135159560637305751)
              ·
                refine ⟨54255202739340955958627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36170135159560637305751 54255202739340955958627)
                ·
                  refine ⟨81382804109011433937941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54255202739340955958627 81382804109011433937941)
                  ·
                    refine ⟨3814818942609910965841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81382804109011433937941 3814818942609910965841)
                    ·
                      refine ⟨2861114206957433224381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3814818942609910965841 2861114206957433224381)
                      ·
                        rfl

theorem cell23_5572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_5572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5572 prefixEnd_5572 := by exact prefixLift 5572
  have htrace : WordTrace (prefixWord ++ tailWord_5572) baseStart_5572 baseEnd_5572 := by
    simpa [prefixWord, tailWord_5572, baseEnd_5572] using wordTrace_append hprefix tailTrace_5572
  have hstable : (prefixWord ++ tailWord_5572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5572).length < 2 ^ (prefixWord ++ tailWord_5572).sum := by decide
  have hdescent : baseEnd_5572 < baseStart_5572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642 : List Nat := [3, 1, 2, 2, 2, 3, 2, 2, 1, 5]
def baseStart_5642 : Nat := 118140960795 + 5642 * 2 ^ 59
def prefixEnd_5642 : Nat := 4983230072969 + 3 ^ 40 * 5642 * 2
def baseEnd_5642 : Nat := 965685950924053116353

theorem tailTrace_5642 : CollatzResearch.WordTrace tailWord_5642 prefixEnd_5642 965685950924053116353 := by
  unfold tailWord_5642
  simp only [CollatzResearch.WordTrace]
  refine ⟨51445161391868105498795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137187097044981614663453 51445161391868105498795)
  ·
    refine ⟨77167742087802158248193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51445161391868105498795 77167742087802158248193)
    ·
      refine ⟨57875806565851618686145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77167742087802158248193 57875806565851618686145)
      ·
        refine ⟨43406854924388714014609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57875806565851618686145 43406854924388714014609)
        ·
          refine ⟨32555141193291535510957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43406854924388714014609 32555141193291535510957)
          ·
            refine ⟨12208177947484325816609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32555141193291535510957 12208177947484325816609)
            ·
              refine ⟨9156133460613244362457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12208177947484325816609 9156133460613244362457)
              ·
                refine ⟨6867100095459933271843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9156133460613244362457 6867100095459933271843)
                ·
                  refine ⟨10300650143189899907765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6867100095459933271843 10300650143189899907765)
                  ·
                    refine ⟨965685950924053116353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10300650143189899907765 965685950924053116353)
                    ·
                      rfl

theorem cell23_5642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_5642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642 prefixEnd_5642 := by exact prefixLift 5642
  have htrace : WordTrace (prefixWord ++ tailWord_5642) baseStart_5642 baseEnd_5642 := by
    simpa [prefixWord, tailWord_5642, baseEnd_5642] using wordTrace_append hprefix tailTrace_5642
  have hstable : (prefixWord ++ tailWord_5642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642).length < 2 ^ (prefixWord ++ tailWord_5642).sum := by decide
  have hdescent : baseEnd_5642 < baseStart_5642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5665 : List Nat := [1, 2, 3, 2, 2, 2, 1, 3, 1, 1, 5]
def baseStart_5665 : Nat := 118140960795 + 5665 * 2 ^ 59
def prefixEnd_5665 : Nat := 4983230072969 + 3 ^ 40 * 5665 * 2
def baseEnd_5665 : Nat := 2908867907825569361453

theorem tailTrace_5665 : CollatzResearch.WordTrace tailWord_5665 prefixEnd_5665 2908867907825569361453 := by
  unfold tailWord_5665
  simp only [CollatzResearch.WordTrace]
  refine ⟨206619524484147350082449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137746349656098233388299 206619524484147350082449)
  ·
    refine ⟨154964643363110512561837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206619524484147350082449 154964643363110512561837)
    ·
      refine ⟨58111741261166442210689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154964643363110512561837 58111741261166442210689)
      ·
        refine ⟨43583805945874831658017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58111741261166442210689 43583805945874831658017)
        ·
          refine ⟨32687854459406123743513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43583805945874831658017 32687854459406123743513)
          ·
            refine ⟨24515890844554592807635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32687854459406123743513 24515890844554592807635)
            ·
              refine ⟨36773836266831889211453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24515890844554592807635 36773836266831889211453)
              ·
                refine ⟨13790188600061958454295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36773836266831889211453 13790188600061958454295)
                ·
                  refine ⟨20685282900092937681443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13790188600061958454295 20685282900092937681443)
                  ·
                    refine ⟨31027924350139406522165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20685282900092937681443 31027924350139406522165)
                    ·
                      refine ⟨2908867907825569361453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31027924350139406522165 2908867907825569361453)
                      ·
                        rfl

theorem cell23_5665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_5665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5665 prefixEnd_5665 := by exact prefixLift 5665
  have htrace : WordTrace (prefixWord ++ tailWord_5665) baseStart_5665 baseEnd_5665 := by
    simpa [prefixWord, tailWord_5665, baseEnd_5665] using wordTrace_append hprefix tailTrace_5665
  have hstable : (prefixWord ++ tailWord_5665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5665).length < 2 ^ (prefixWord ++ tailWord_5665).sum := by decide
  have hdescent : baseEnd_5665 < baseStart_5665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685 : List Nat := [1, 3, 3, 1, 1, 4, 2, 8]
def baseStart_5685 : Nat := 118140960795 + 5685 * 2 ^ 59
def prefixEnd_5685 : Nat := 4983230072969 + 3 ^ 40 * 5685 * 2
def baseEnd_5685 : Nat := 108116204478351522643

theorem tailTrace_5685 : CollatzResearch.WordTrace tailWord_5685 prefixEnd_5685 108116204478351522643 := by
  unfold tailWord_5685
  simp only [CollatzResearch.WordTrace]
  refine ⟨207348984411690765810509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138232656274460510540339 207348984411690765810509)
  ·
    refine ⟨77755869154384037178941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207348984411690765810509 77755869154384037178941)
    ·
      refine ⟨29158450932894013942103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77755869154384037178941 29158450932894013942103)
      ·
        refine ⟨43737676399341020913155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29158450932894013942103 43737676399341020913155)
        ·
          refine ⟨65606514599011531369733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43737676399341020913155 65606514599011531369733)
          ·
            refine ⟨12301221487314662131825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65606514599011531369733 12301221487314662131825)
            ·
              refine ⟨9225916115485996598869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12301221487314662131825 9225916115485996598869)
              ·
                refine ⟨108116204478351522643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9225916115485996598869 108116204478351522643)
                ·
                  rfl

theorem cell23_5685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 8].length) (baseStart_5685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685 prefixEnd_5685 := by exact prefixLift 5685
  have htrace : WordTrace (prefixWord ++ tailWord_5685) baseStart_5685 baseEnd_5685 := by
    simpa [prefixWord, tailWord_5685, baseEnd_5685] using wordTrace_append hprefix tailTrace_5685
  have hstable : (prefixWord ++ tailWord_5685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685).length < 2 ^ (prefixWord ++ tailWord_5685).sum := by decide
  have hdescent : baseEnd_5685 < baseStart_5685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689 : List Nat := [1, 2, 1, 5, 1, 2, 4, 1, 2, 4]
def baseStart_5689 : Nat := 118140960795 + 5689 * 2 ^ 59
def prefixEnd_5689 : Nat := 4983230072969 + 3 ^ 40 * 5689 * 2
def baseEnd_5689 : Nat := 973730481177825153781

theorem tailTrace_5689 : CollatzResearch.WordTrace tailWord_5689 prefixEnd_5689 973730481177825153781 := by
  unfold tailWord_5689
  simp only [CollatzResearch.WordTrace]
  refine ⟨207494876397199448956121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138329917598132965970747 207494876397199448956121)
  ·
    refine ⟨155621157297899586717091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207494876397199448956121 155621157297899586717091)
    ·
      refine ⟨233431735946849380075637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155621157297899586717091 233431735946849380075637)
      ·
        refine ⟨21884225245017129382091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 233431735946849380075637 21884225245017129382091)
        ·
          refine ⟨32826337867525694073137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21884225245017129382091 32826337867525694073137)
          ·
            refine ⟨24619753400644270554853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32826337867525694073137 24619753400644270554853)
            ·
              refine ⟨4616203762620800729035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24619753400644270554853 4616203762620800729035)
              ·
                refine ⟨6924305643931201093553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4616203762620800729035 6924305643931201093553)
                ·
                  refine ⟨5193229232948400820165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6924305643931201093553 5193229232948400820165)
                  ·
                    refine ⟨973730481177825153781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5193229232948400820165 973730481177825153781)
                    ·
                      rfl

theorem cell23_5689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 2, 4].length) (baseStart_5689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689 prefixEnd_5689 := by exact prefixLift 5689
  have htrace : WordTrace (prefixWord ++ tailWord_5689) baseStart_5689 baseEnd_5689 := by
    simpa [prefixWord, tailWord_5689, baseEnd_5689] using wordTrace_append hprefix tailTrace_5689
  have hstable : (prefixWord ++ tailWord_5689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689).length < 2 ^ (prefixWord ++ tailWord_5689).sum := by decide
  have hdescent : baseEnd_5689 < baseStart_5689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5709 : List Nat := [1, 6, 1, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_5709 : Nat := 118140960795 + 5709 * 2 ^ 59
def prefixEnd_5709 : Nat := 4983230072969 + 3 ^ 40 * 5709 * 2
def baseEnd_5709 : Nat := 2931461056623397211251

theorem tailTrace_5709 : CollatzResearch.WordTrace tailWord_5709 prefixEnd_5709 2931461056623397211251 := by
  unfold tailWord_5709
  simp only [CollatzResearch.WordTrace]
  refine ⟨208224336324742864684181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138816224216495243122787 208224336324742864684181)
  ·
    refine ⟨9760515765222321782071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 208224336324742864684181 9760515765222321782071)
    ·
      refine ⟨14640773647833482673107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9760515765222321782071 14640773647833482673107)
      ·
        refine ⟨21961160471750224009661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14640773647833482673107 21961160471750224009661)
        ·
          refine ⟨8235435176906334003623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21961160471750224009661 8235435176906334003623)
          ·
            refine ⟨12353152765359501005435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8235435176906334003623 12353152765359501005435)
            ·
              refine ⟨18529729148039251508153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12353152765359501005435 18529729148039251508153)
              ·
                refine ⟨13897296861029438631115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18529729148039251508153 13897296861029438631115)
                ·
                  refine ⟨20845945291544157946673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13897296861029438631115 20845945291544157946673)
                  ·
                    refine ⟨15634458968658118460005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20845945291544157946673 15634458968658118460005)
                    ·
                      refine ⟨2931461056623397211251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15634458968658118460005 2931461056623397211251)
                      ·
                        rfl

theorem cell23_5709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_5709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5709 prefixEnd_5709 := by exact prefixLift 5709
  have htrace : WordTrace (prefixWord ++ tailWord_5709) baseStart_5709 baseEnd_5709 := by
    simpa [prefixWord, tailWord_5709, baseEnd_5709] using wordTrace_append hprefix tailTrace_5709
  have hstable : (prefixWord ++ tailWord_5709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5709).length < 2 ^ (prefixWord ++ tailWord_5709).sum := by decide
  have hdescent : baseEnd_5709 < baseStart_5709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729 : List Nat := [1, 2, 3, 1, 1, 3, 4, 2, 2, 1, 3]
def baseStart_5729 : Nat := 118140960795 + 5729 * 2 ^ 59
def prefixEnd_5729 : Nat := 4983230072969 + 3 ^ 40 * 5729 * 2
def baseEnd_5729 : Nat := 2941730669713318961159

theorem tailTrace_5729 : CollatzResearch.WordTrace tailWord_5729 prefixEnd_5729 2941730669713318961159 := by
  unfold tailWord_5729
  simp only [CollatzResearch.WordTrace]
  refine ⟨208953796252286280412241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139302530834857520274827 208953796252286280412241)
  ·
    refine ⟨156715347189214710309181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208953796252286280412241 156715347189214710309181)
    ·
      refine ⟨58768255195955516365943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156715347189214710309181 58768255195955516365943)
      ·
        refine ⟨88152382793933274548915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58768255195955516365943 88152382793933274548915)
        ·
          refine ⟨132228574190899911823373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88152382793933274548915 132228574190899911823373)
          ·
            refine ⟨49585715321587466933765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132228574190899911823373 49585715321587466933765)
            ·
              refine ⟨9297321622797650050081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49585715321587466933765 9297321622797650050081)
              ·
                refine ⟨6972991217098237537561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9297321622797650050081 6972991217098237537561)
                ·
                  refine ⟨5229743412823678153171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6972991217098237537561 5229743412823678153171)
                  ·
                    refine ⟨7844615119235517229757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5229743412823678153171 7844615119235517229757)
                    ·
                      refine ⟨2941730669713318961159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7844615119235517229757 2941730669713318961159)
                      ·
                        rfl

theorem cell23_5729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_5729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729 prefixEnd_5729 := by exact prefixLift 5729
  have htrace : WordTrace (prefixWord ++ tailWord_5729) baseStart_5729 baseEnd_5729 := by
    simpa [prefixWord, tailWord_5729, baseEnd_5729] using wordTrace_append hprefix tailTrace_5729
  have hstable : (prefixWord ++ tailWord_5729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729).length < 2 ^ (prefixWord ++ tailWord_5729).sum := by decide
  have hdescent : baseEnd_5729 < baseStart_5729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_5735 : Nat := 118140960795 + 5735 * 2 ^ 59
def prefixEnd_5735 : Nat := 4983230072969 + 3 ^ 40 * 5735 * 2
def baseEnd_5735 : Nat := 2944811553640295486131

theorem tailTrace_5735 : CollatzResearch.WordTrace tailWord_5735 prefixEnd_5735 2944811553640295486131 := by
  unfold tailWord_5735
  simp only [CollatzResearch.WordTrace]
  refine ⟨209172634230549305130659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139448422820366203420439 209172634230549305130659)
  ·
    refine ⟨313758951345823957695989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209172634230549305130659 313758951345823957695989)
    ·
      refine ⟨29414901688670996033999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 313758951345823957695989 29414901688670996033999)
      ·
        refine ⟨44122352533006494050999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29414901688670996033999 44122352533006494050999)
        ·
          refine ⟨66183528799509741076499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44122352533006494050999 66183528799509741076499)
          ·
            refine ⟨99275293199264611614749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66183528799509741076499 99275293199264611614749)
            ·
              refine ⟨37228234949724229355531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99275293199264611614749 37228234949724229355531)
              ·
                refine ⟨55842352424586344033297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37228234949724229355531 55842352424586344033297)
                ·
                  refine ⟨41881764318439758024973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55842352424586344033297 41881764318439758024973)
                  ·
                    refine ⟨15705661619414909259365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41881764318439758024973 15705661619414909259365)
                    ·
                      refine ⟨2944811553640295486131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15705661619414909259365 2944811553640295486131)
                      ·
                        rfl

theorem cell23_5735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_5735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735 prefixEnd_5735 := by exact prefixLift 5735
  have htrace : WordTrace (prefixWord ++ tailWord_5735) baseStart_5735 baseEnd_5735 := by
    simpa [prefixWord, tailWord_5735, baseEnd_5735] using wordTrace_append hprefix tailTrace_5735
  have hstable : (prefixWord ++ tailWord_5735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735).length < 2 ^ (prefixWord ++ tailWord_5735).sum := by decide
  have hdescent : baseEnd_5735 < baseStart_5735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5755 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 3]
def baseStart_5755 : Nat := 118140960795 + 5755 * 2 ^ 59
def prefixEnd_5755 : Nat := 4983230072969 + 3 ^ 40 * 5755 * 2
def baseEnd_5755 : Nat := 2955081166730217236039

theorem tailTrace_5755 : CollatzResearch.WordTrace tailWord_5755 prefixEnd_5755 2955081166730217236039 := by
  unfold tailWord_5755
  simp only [CollatzResearch.WordTrace]
  refine ⟨209902094158092720858719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139934729438728480572479 209902094158092720858719)
  ·
    refine ⟨314853141237139081288079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209902094158092720858719 314853141237139081288079)
    ·
      refine ⟨472279711855708621932119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314853141237139081288079 472279711855708621932119)
      ·
        refine ⟨708419567783562932898179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472279711855708621932119 708419567783562932898179)
        ·
          refine ⟨1062629351675344399347269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 708419567783562932898179 1062629351675344399347269)
          ·
            refine ⟨199243003439127074877613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1062629351675344399347269 199243003439127074877613)
            ·
              refine ⟨74716126289672653079105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199243003439127074877613 74716126289672653079105)
              ·
                refine ⟨56037094717254489809329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74716126289672653079105 56037094717254489809329)
                ·
                  refine ⟨42027821037940867356997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56037094717254489809329 42027821037940867356997)
                  ·
                    refine ⟨7880216444613912629437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42027821037940867356997 7880216444613912629437)
                    ·
                      refine ⟨2955081166730217236039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7880216444613912629437 2955081166730217236039)
                      ·
                        rfl

theorem cell23_5755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 3].length) (baseStart_5755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5755 prefixEnd_5755 := by exact prefixLift 5755
  have htrace : WordTrace (prefixWord ++ tailWord_5755) baseStart_5755 baseEnd_5755 := by
    simpa [prefixWord, tailWord_5755, baseEnd_5755] using wordTrace_append hprefix tailTrace_5755
  have hstable : (prefixWord ++ tailWord_5755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5755).length < 2 ^ (prefixWord ++ tailWord_5755).sum := by decide
  have hdescent : baseEnd_5755 < baseStart_5755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5765 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 1, 4, 4]
def baseStart_5765 : Nat := 118140960795 + 5765 * 2 ^ 59
def prefixEnd_5765 : Nat := 4983230072969 + 3 ^ 40 * 5765 * 2
def baseEnd_5765 : Nat := 2960215973275178110993

theorem tailTrace_5765 : CollatzResearch.WordTrace tailWord_5765 prefixEnd_5765 2960215973275178110993 := by
  unfold tailWord_5765
  simp only [CollatzResearch.WordTrace]
  refine ⟨210266824121864428722749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140177882747909619148499 210266824121864428722749)
  ·
    refine ⟨78850059045699160771031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210266824121864428722749 78850059045699160771031)
    ·
      refine ⟨118275088568548741156547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78850059045699160771031 118275088568548741156547)
      ·
        refine ⟨177412632852823111734821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118275088568548741156547 177412632852823111734821)
        ·
          refine ⟨33264868659904333450279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177412632852823111734821 33264868659904333450279)
          ·
            refine ⟨49897302989856500175419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33264868659904333450279 49897302989856500175419)
            ·
              refine ⟨74845954484784750263129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49897302989856500175419 74845954484784750263129)
              ·
                refine ⟨56134465863588562697347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74845954484784750263129 56134465863588562697347)
                ·
                  refine ⟨84201698795382844046021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56134465863588562697347 84201698795382844046021)
                  ·
                    refine ⟨15787818524134283258629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84201698795382844046021 15787818524134283258629)
                    ·
                      refine ⟨2960215973275178110993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15787818524134283258629 2960215973275178110993)
                      ·
                        rfl

theorem cell23_5765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_5765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5765 prefixEnd_5765 := by exact prefixLift 5765
  have htrace : WordTrace (prefixWord ++ tailWord_5765) baseStart_5765 baseEnd_5765 := by
    simpa [prefixWord, tailWord_5765, baseEnd_5765] using wordTrace_append hprefix tailTrace_5765
  have hstable : (prefixWord ++ tailWord_5765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5765).length < 2 ^ (prefixWord ++ tailWord_5765).sum := by decide
  have hdescent : baseEnd_5765 < baseStart_5765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780 : List Nat := [2, 4, 2, 2, 3, 1, 1, 2, 2, 1, 3]
def baseStart_5780 : Nat := 118140960795 + 5780 * 2 ^ 59
def prefixEnd_5780 : Nat := 4983230072969 + 3 ^ 40 * 5780 * 2
def baseEnd_5780 : Nat := 2967918183092619423425

theorem tailTrace_5780 : CollatzResearch.WordTrace tailWord_5780 prefixEnd_5780 2967918183092619423425 := by
  unfold tailWord_5780
  simp only [CollatzResearch.WordTrace]
  refine ⟨105406959533760995259397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140542612711681327012529 105406959533760995259397)
  ·
    refine ⟨19763804912580186611137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105406959533760995259397 19763804912580186611137)
    ·
      refine ⟨14822853684435139958353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19763804912580186611137 14822853684435139958353)
      ·
        refine ⟨11117140263326354968765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14822853684435139958353 11117140263326354968765)
        ·
          refine ⟨4168927598747383113287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11117140263326354968765 4168927598747383113287)
          ·
            refine ⟨6253391398121074669931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4168927598747383113287 6253391398121074669931)
            ·
              refine ⟨9380087097181612004897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6253391398121074669931 9380087097181612004897)
              ·
                refine ⟨7035065322886209003673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9380087097181612004897 7035065322886209003673)
                ·
                  refine ⟨5276298992164656752755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7035065322886209003673 5276298992164656752755)
                  ·
                    refine ⟨7914448488246985129133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5276298992164656752755 7914448488246985129133)
                    ·
                      refine ⟨2967918183092619423425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7914448488246985129133 2967918183092619423425)
                      ·
                        rfl

theorem cell23_5780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_5780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780 prefixEnd_5780 := by exact prefixLift 5780
  have htrace : WordTrace (prefixWord ++ tailWord_5780) baseStart_5780 baseEnd_5780 := by
    simpa [prefixWord, tailWord_5780, baseEnd_5780] using wordTrace_append hprefix tailTrace_5780
  have hstable : (prefixWord ++ tailWord_5780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780).length < 2 ^ (prefixWord ++ tailWord_5780).sum := by decide
  have hdescent : baseEnd_5780 < baseStart_5780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792 : List Nat := [2, 1, 1, 4, 3, 2, 2, 1, 7]
def baseStart_5792 : Nat := 118140960795 + 5792 * 2 ^ 59
def prefixEnd_5792 : Nat := 4983230072969 + 3 ^ 40 * 5792 * 2
def baseEnd_5792 : Nat := 330453327882952497041

theorem tailTrace_5792 : CollatzResearch.WordTrace tailWord_5792 prefixEnd_5792 330453327882952497041 := by
  unfold tailWord_5792
  simp only [CollatzResearch.WordTrace]
  refine ⟨105625797512024019977815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140834396682698693303753 105625797512024019977815)
  ·
    refine ⟨158438696268036029966723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105625797512024019977815 158438696268036029966723)
    ·
      refine ⟨237658044402054044950085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158438696268036029966723 237658044402054044950085)
      ·
        refine ⟨44560883325385133428141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 237658044402054044950085 44560883325385133428141)
        ·
          refine ⟨16710331247019425035553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44560883325385133428141 16710331247019425035553)
          ·
            refine ⟨12532748435264568776665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16710331247019425035553 12532748435264568776665)
            ·
              refine ⟨9399561326448426582499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12532748435264568776665 9399561326448426582499)
              ·
                refine ⟨14099341989672639873749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9399561326448426582499 14099341989672639873749)
                ·
                  refine ⟨330453327882952497041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14099341989672639873749 330453327882952497041)
                  ·
                    rfl

theorem cell23_5792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 7].length) (baseStart_5792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792 prefixEnd_5792 := by exact prefixLift 5792
  have htrace : WordTrace (prefixWord ++ tailWord_5792) baseStart_5792 baseEnd_5792 := by
    simpa [prefixWord, tailWord_5792, baseEnd_5792] using wordTrace_append hprefix tailTrace_5792
  have hstable : (prefixWord ++ tailWord_5792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792).length < 2 ^ (prefixWord ++ tailWord_5792).sum := by decide
  have hdescent : baseEnd_5792 < baseStart_5792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 1, 7]
def baseStart_5822 : Nat := 118140960795 + 5822 * 2 ^ 59
def prefixEnd_5822 : Nat := 4983230072969 + 3 ^ 40 * 5822 * 2
def baseEnd_5822 : Nat := 996494790193818366077

theorem tailTrace_5822 : CollatzResearch.WordTrace tailWord_5822 prefixEnd_5822 996494790193818366077 := by
  unfold tailWord_5822
  simp only [CollatzResearch.WordTrace]
  refine ⟨26543223114420395443465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141563856610242109031813 26543223114420395443465)
  ·
    refine ⟨19907417335815296582599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26543223114420395443465 19907417335815296582599)
    ·
      refine ⟨29861126003722944873899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19907417335815296582599 29861126003722944873899)
      ·
        refine ⟨44791689005584417310849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29861126003722944873899 44791689005584417310849)
        ·
          refine ⟨33593766754188312983137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44791689005584417310849 33593766754188312983137)
          ·
            refine ⟨25195325065641234737353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33593766754188312983137 25195325065641234737353)
            ·
              refine ⟨18896493799230926053015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25195325065641234737353 18896493799230926053015)
              ·
                refine ⟨28344740698846389079523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18896493799230926053015 28344740698846389079523)
                ·
                  refine ⟨42517111048269583619285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28344740698846389079523 42517111048269583619285)
                  ·
                    refine ⟨996494790193818366077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42517111048269583619285 996494790193818366077)
                    ·
                      rfl

theorem cell23_5822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_5822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822 prefixEnd_5822 := by exact prefixLift 5822
  have htrace : WordTrace (prefixWord ++ tailWord_5822) baseStart_5822 baseEnd_5822 := by
    simpa [prefixWord, tailWord_5822, baseEnd_5822] using wordTrace_append hprefix tailTrace_5822
  have hstable : (prefixWord ++ tailWord_5822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822).length < 2 ^ (prefixWord ++ tailWord_5822).sum := by decide
  have hdescent : baseEnd_5822 < baseStart_5822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 3, 5]
def baseStart_5912 : Nat := 118140960795 + 5912 * 2 ^ 59
def prefixEnd_5912 : Nat := 4983230072969 + 3 ^ 40 * 5912 * 2
def baseEnd_5912 : Nat := 1011899209828700990939

theorem tailTrace_5912 : CollatzResearch.WordTrace tailWord_5912 prefixEnd_5912 1011899209828700990939 := by
  unfold tailWord_5912
  simp only [CollatzResearch.WordTrace]
  refine ⟨107814177294654267161995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143752236392872356215993 107814177294654267161995)
  ·
    refine ⟨161721265941981400742993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107814177294654267161995 161721265941981400742993)
    ·
      refine ⟨121290949456486050557245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161721265941981400742993 121290949456486050557245)
      ·
        refine ⟨45484106046182268958967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121290949456486050557245 45484106046182268958967)
        ·
          refine ⟨68226159069273403438451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45484106046182268958967 68226159069273403438451)
          ·
            refine ⟨102339238603910105157677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68226159069273403438451 102339238603910105157677)
            ·
              refine ⟨38377214476466289434129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102339238603910105157677 38377214476466289434129)
              ·
                refine ⟨28782910857349717075597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38377214476466289434129 28782910857349717075597)
                ·
                  refine ⟨10793591571506143903349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28782910857349717075597 10793591571506143903349)
                  ·
                    refine ⟨1011899209828700990939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10793591571506143903349 1011899209828700990939)
                    ·
                      rfl

theorem cell23_5912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_5912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912 prefixEnd_5912 := by exact prefixLift 5912
  have htrace : WordTrace (prefixWord ++ tailWord_5912) baseStart_5912 baseEnd_5912 := by
    simpa [prefixWord, tailWord_5912, baseEnd_5912] using wordTrace_append hprefix tailTrace_5912
  have hstable : (prefixWord ++ tailWord_5912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912).length < 2 ^ (prefixWord ++ tailWord_5912).sum := by decide
  have hdescent : baseEnd_5912 < baseStart_5912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 1, 5, 2]
def baseStart_5919 : Nat := 118140960795 + 5919 * 2 ^ 59
def prefixEnd_5919 : Nat := 4983230072969 + 3 ^ 40 * 5919 * 2
def baseEnd_5919 : Nat := 3039291994067575585285

theorem tailTrace_5919 : CollatzResearch.WordTrace tailWord_5919 prefixEnd_5919 3039291994067575585285 := by
  unfold tailWord_5919
  simp only [CollatzResearch.WordTrace]
  refine ⟨215883665563948729828811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143922443709299153219207 215883665563948729828811)
  ·
    refine ⟨323825498345923094743217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215883665563948729828811 323825498345923094743217)
    ·
      refine ⟨242869123759442321057413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323825498345923094743217 242869123759442321057413)
      ·
        refine ⟨45537960704895435198265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 242869123759442321057413 45537960704895435198265)
        ·
          refine ⟨34153470528671576398699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45537960704895435198265 34153470528671576398699)
          ·
            refine ⟨51230205793007364598049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34153470528671576398699 51230205793007364598049)
            ·
              refine ⟨38422654344755523448537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51230205793007364598049 38422654344755523448537)
              ·
                refine ⟨28816990758566642586403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38422654344755523448537 28816990758566642586403)
                ·
                  refine ⟨43225486137849963879605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28816990758566642586403 43225486137849963879605)
                  ·
                    refine ⟨4052389325423434113713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43225486137849963879605 4052389325423434113713)
                    ·
                      refine ⟨3039291994067575585285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4052389325423434113713 3039291994067575585285)
                      ·
                        rfl

theorem cell23_5919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_5919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919 prefixEnd_5919 := by exact prefixLift 5919
  have htrace : WordTrace (prefixWord ++ tailWord_5919) baseStart_5919 baseEnd_5919 := by
    simpa [prefixWord, tailWord_5919, baseEnd_5919] using wordTrace_append hprefix tailTrace_5919
  have hstable : (prefixWord ++ tailWord_5919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919).length < 2 ^ (prefixWord ++ tailWord_5919).sum := by decide
  have hdescent : baseEnd_5919 < baseStart_5919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
