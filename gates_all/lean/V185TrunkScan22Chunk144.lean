import V185TrunkScan22Chunk143

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1287631 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 3, 5]
def baseStart_1287631 : Nat := 118140960795 + 1287631 * 2 ^ 59
def prefixEnd_1287631 : Nat := 4983230072969 + 3 ^ 40 * 1287631 * 2
def baseEnd_1287631 : Nat := 440782405753037914327199

theorem tailTrace_1287631 : CollatzResearch.WordTrace tailWord_1287631 prefixEnd_1287631 440782405753037914327199 := by
  unfold tailWord_1287631
  simp only [CollatzResearch.WordTrace]
  refine ⟨46963760798140271711990747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31309173865426847807993831 46963760798140271711990747)
  ·
    refine ⟨70445641197210407567986121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46963760798140271711990747 70445641197210407567986121)
    ·
      refine ⟨52834230897907805675989591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70445641197210407567986121 52834230897907805675989591)
      ·
        refine ⟨79251346346861708513984387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52834230897907805675989591 79251346346861708513984387)
        ·
          refine ⟨118877019520292562770976581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79251346346861708513984387 118877019520292562770976581)
          ·
            refine ⟨22289441160054855519558109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118877019520292562770976581 22289441160054855519558109)
            ·
              refine ⟨8358540435020570819834291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22289441160054855519558109 8358540435020570819834291)
              ·
                refine ⟨12537810652530856229751437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8358540435020570819834291 12537810652530856229751437)
                ·
                  refine ⟨4701678994699071086156789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12537810652530856229751437 4701678994699071086156789)
                  ·
                    refine ⟨440782405753037914327199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4701678994699071086156789 440782405753037914327199)
                    ·
                      rfl

theorem cell22_1287631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_1287631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287631 prefixEnd_1287631 := by exact prefixLift 1287631
  have htrace : WordTrace (prefixWord ++ tailWord_1287631) baseStart_1287631 baseEnd_1287631 := by
    simpa [prefixWord, tailWord_1287631, baseEnd_1287631] using wordTrace_append hprefix tailTrace_1287631
  have hstable : (prefixWord ++ tailWord_1287631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287631).length < 2 ^ (prefixWord ++ tailWord_1287631).sum := by decide
  have hdescent : baseEnd_1287631 < baseStart_1287631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287665 : List Nat := [1, 2, 2, 2, 3, 2, 2, 3, 2, 3]
def baseStart_1287665 : Nat := 118140960795 + 1287665 * 2 ^ 59
def prefixEnd_1287665 : Nat := 4983230072969 + 3 ^ 40 * 1287665 * 2
def baseEnd_1287665 : Nat := 440794044647873158977095

theorem tailTrace_1287665 : CollatzResearch.WordTrace tailWord_1287665 prefixEnd_1287665 440794044647873158977095 := by
  unfold tailWord_1287665
  simp only [CollatzResearch.WordTrace]
  refine ⟨46965000880017095518728449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31310000586678063679152299 46965000880017095518728449)
  ·
    refine ⟨35223750660012821639046337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46965000880017095518728449 35223750660012821639046337)
    ·
      refine ⟨26417812995009616229284753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35223750660012821639046337 26417812995009616229284753)
      ·
        refine ⟨19813359746257212171963565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26417812995009616229284753 19813359746257212171963565)
        ·
          refine ⟨7430009904846454564486337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19813359746257212171963565 7430009904846454564486337)
          ·
            refine ⟨5572507428634840923364753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7430009904846454564486337 5572507428634840923364753)
            ·
              refine ⟨4179380571476130692523565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5572507428634840923364753 4179380571476130692523565)
              ·
                refine ⟨1567267714303549009696337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4179380571476130692523565 1567267714303549009696337)
                ·
                  refine ⟨1175450785727661757272253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1567267714303549009696337 1175450785727661757272253)
                  ·
                    refine ⟨440794044647873158977095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1175450785727661757272253 440794044647873158977095)
                    ·
                      rfl

theorem cell22_1287665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 3].length) (baseStart_1287665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287665 prefixEnd_1287665 := by exact prefixLift 1287665
  have htrace : WordTrace (prefixWord ++ tailWord_1287665) baseStart_1287665 baseEnd_1287665 := by
    simpa [prefixWord, tailWord_1287665, baseEnd_1287665] using wordTrace_append hprefix tailTrace_1287665
  have hstable : (prefixWord ++ tailWord_1287665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287665).length < 2 ^ (prefixWord ++ tailWord_1287665).sum := by decide
  have hdescent : baseEnd_1287665 < baseStart_1287665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287686 : List Nat := [6, 2, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_1287686 : Nat := 118140960795 + 1287686 * 2 ^ 59
def prefixEnd_1287686 : Nat := 4983230072969 + 3 ^ 40 * 1287686 * 2
def baseEnd_1287686 : Nat := 440801233377036104202031

theorem tailTrace_1287686 : CollatzResearch.WordTrace tailWord_1287686 prefixEnd_1287686 440801233377036104202031 := by
  unfold tailWord_1287686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1467680212904406753288841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31310511208627344070161941 1467680212904406753288841)
  ·
    refine ⟨1100760159678305064966631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1467680212904406753288841 1100760159678305064966631)
    ·
      refine ⟨1651140239517457597449947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1100760159678305064966631 1651140239517457597449947)
      ·
        refine ⟨2476710359276186396174921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1651140239517457597449947 2476710359276186396174921)
        ·
          refine ⟨1857532769457139797131191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2476710359276186396174921 1857532769457139797131191)
          ·
            refine ⟨2786299154185709695696787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1857532769457139797131191 2786299154185709695696787)
            ·
              refine ⟨4179448731278564543545181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2786299154185709695696787 4179448731278564543545181)
              ·
                refine ⟨1567293274229461703829443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4179448731278564543545181 1567293274229461703829443)
                ·
                  refine ⟨2350939911344192555744165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1567293274229461703829443 2350939911344192555744165)
                  ·
                    refine ⟨440801233377036104202031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2350939911344192555744165 440801233377036104202031)
                    ·
                      rfl

theorem cell22_1287686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_1287686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287686 prefixEnd_1287686 := by exact prefixLift 1287686
  have htrace : WordTrace (prefixWord ++ tailWord_1287686) baseStart_1287686 baseEnd_1287686 := by
    simpa [prefixWord, tailWord_1287686, baseEnd_1287686] using wordTrace_append hprefix tailTrace_1287686
  have hstable : (prefixWord ++ tailWord_1287686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287686).length < 2 ^ (prefixWord ++ tailWord_1287686).sum := by decide
  have hdescent : baseEnd_1287686 < baseStart_1287686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287815 : List Nat := [1, 1, 4, 2, 1, 3, 2, 2, 2, 4]
def baseStart_1287815 : Nat := 118140960795 + 1287815 * 2 ^ 59
def prefixEnd_1287815 : Nat := 4983230072969 + 3 ^ 40 * 1287815 * 2
def baseEnd_1287815 : Nat := 440845392713322767726635

theorem tailTrace_1287815 : CollatzResearch.WordTrace tailWord_1287815 prefixEnd_1287815 440845392713322767726635 := by
  unfold tailWord_1287815
  simp only [CollatzResearch.WordTrace]
  refine ⟨46970471829473671136688899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31313647886315780757792599 46970471829473671136688899)
  ·
    refine ⟨70455707744210506705033349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46970471829473671136688899 70455707744210506705033349)
    ·
      refine ⟨13210445202039470007193753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70455707744210506705033349 13210445202039470007193753)
      ·
        refine ⟨9907833901529602505395315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13210445202039470007193753 9907833901529602505395315)
        ·
          refine ⟨14861750852294403758092973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9907833901529602505395315 14861750852294403758092973)
          ·
            refine ⟨5573156569610401409284865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14861750852294403758092973 5573156569610401409284865)
            ·
              refine ⟨4179867427207801056963649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5573156569610401409284865 4179867427207801056963649)
              ·
                refine ⟨3134900570405850792722737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4179867427207801056963649 3134900570405850792722737)
                ·
                  refine ⟨2351175427804388094542053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3134900570405850792722737 2351175427804388094542053)
                  ·
                    refine ⟨440845392713322767726635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2351175427804388094542053 440845392713322767726635)
                    ·
                      rfl

theorem cell22_1287815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_1287815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287815 prefixEnd_1287815 := by exact prefixLift 1287815
  have htrace : WordTrace (prefixWord ++ tailWord_1287815) baseStart_1287815 baseEnd_1287815 := by
    simpa [prefixWord, tailWord_1287815, baseEnd_1287815] using wordTrace_append hprefix tailTrace_1287815
  have hstable : (prefixWord ++ tailWord_1287815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287815).length < 2 ^ (prefixWord ++ tailWord_1287815).sum := by decide
  have hdescent : baseEnd_1287815 < baseStart_1287815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287843 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 2, 6]
def baseStart_1287843 : Nat := 118140960795 + 1287843 * 2 ^ 59
def prefixEnd_1287843 : Nat := 4983230072969 + 3 ^ 40 * 1287843 * 2
def baseEnd_1287843 : Nat := 440854977685540028026549

theorem tailTrace_1287843 : CollatzResearch.WordTrace tailWord_1287843 prefixEnd_1287843 440854977685540028026549 := by
  unfold tailWord_1287843
  simp only [CollatzResearch.WordTrace]
  refine ⟨46971493073372231918708183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31314328715581487945805455 46971493073372231918708183)
  ·
    refine ⟨70457239610058347878062275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46971493073372231918708183 70457239610058347878062275)
    ·
      refine ⟨105685859415087521817093413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70457239610058347878062275 105685859415087521817093413)
      ·
        refine ⟨19816098640328910340705015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105685859415087521817093413 19816098640328910340705015)
        ·
          refine ⟨29724147960493365511057523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19816098640328910340705015 29724147960493365511057523)
          ·
            refine ⟨44586221940740048266586285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29724147960493365511057523 44586221940740048266586285)
            ·
              refine ⟨16719833227777518099969857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44586221940740048266586285 16719833227777518099969857)
              ·
                refine ⟨12539874920833138574977393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16719833227777518099969857 12539874920833138574977393)
                ·
                  refine ⟨9404906190624853931233045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12539874920833138574977393 9404906190624853931233045)
                  ·
                    refine ⟨440854977685540028026549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9404906190624853931233045 440854977685540028026549)
                    ·
                      rfl

theorem cell22_1287843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 6].length) (baseStart_1287843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287843 prefixEnd_1287843 := by exact prefixLift 1287843
  have htrace : WordTrace (prefixWord ++ tailWord_1287843) baseStart_1287843 baseEnd_1287843 := by
    simpa [prefixWord, tailWord_1287843, baseEnd_1287843] using wordTrace_append hprefix tailTrace_1287843
  have hstable : (prefixWord ++ tailWord_1287843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287843).length < 2 ^ (prefixWord ++ tailWord_1287843).sum := by decide
  have hdescent : baseEnd_1287843 < baseStart_1287843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287845 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 5, 3]
def baseStart_1287845 : Nat := 118140960795 + 1287845 * 2 ^ 59
def prefixEnd_1287845 : Nat := 4983230072969 + 3 ^ 40 * 1287845 * 2
def baseEnd_1287845 : Nat := 440855662326412689476543

theorem tailTrace_1287845 : CollatzResearch.WordTrace tailWord_1287845 prefixEnd_1287845 440855662326412689476543 := by
  unfold tailWord_1287845
  simp only [CollatzResearch.WordTrace]
  refine ⟨46971566019364986260280989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31314377346243324173520659 46971566019364986260280989)
  ·
    refine ⟨17614337257261869847605371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46971566019364986260280989 17614337257261869847605371)
    ·
      refine ⟨26421505885892804771408057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17614337257261869847605371 26421505885892804771408057)
      ·
        refine ⟨19816129414419603578556043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26421505885892804771408057 19816129414419603578556043)
        ·
          refine ⟨29724194121629405367834065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19816129414419603578556043 29724194121629405367834065)
          ·
            refine ⟨22293145591222054025875549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29724194121629405367834065 22293145591222054025875549)
            ·
              refine ⟨8359929596708270259703331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22293145591222054025875549 8359929596708270259703331)
              ·
                refine ⟨12539894395062405389554997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8359929596708270259703331 12539894395062405389554997)
                ·
                  refine ⟨1175615099537100505270781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12539894395062405389554997 1175615099537100505270781)
                  ·
                    refine ⟨440855662326412689476543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1175615099537100505270781 440855662326412689476543)
                    ·
                      rfl

theorem cell22_1287845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 3].length) (baseStart_1287845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287845 prefixEnd_1287845 := by exact prefixLift 1287845
  have htrace : WordTrace (prefixWord ++ tailWord_1287845) baseStart_1287845 baseEnd_1287845 := by
    simpa [prefixWord, tailWord_1287845, baseEnd_1287845] using wordTrace_append hprefix tailTrace_1287845
  have hstable : (prefixWord ++ tailWord_1287845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287845).length < 2 ^ (prefixWord ++ tailWord_1287845).sum := by decide
  have hdescent : baseEnd_1287845 < baseStart_1287845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287888 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 2, 8]
def baseStart_1287888 : Nat := 118140960795 + 1287888 * 2 ^ 59
def prefixEnd_1287888 : Nat := 4983230072969 + 3 ^ 40 * 1287888 * 2
def baseEnd_1287888 : Nat := 440870382105174910651411

theorem tailTrace_1287888 : CollatzResearch.WordTrace tailWord_1287888 prefixEnd_1287888 440870382105174910651411 := by
  unfold tailWord_1287888
  simp only [CollatzResearch.WordTrace]
  refine ⟨23486567179104602302048159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31315422905472803069397545 23486567179104602302048159)
  ·
    refine ⟨35229850768656903453072239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23486567179104602302048159 35229850768656903453072239)
    ·
      refine ⟨52844776152985355179608359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35229850768656903453072239 52844776152985355179608359)
      ·
        refine ⟨79267164229478032769412539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52844776152985355179608359 79267164229478032769412539)
        ·
          refine ⟨118900746344217049154118809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79267164229478032769412539 118900746344217049154118809)
          ·
            refine ⟨89175559758162786865589107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118900746344217049154118809 89175559758162786865589107)
            ·
              refine ⟨133763339637244180298383661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89175559758162786865589107 133763339637244180298383661)
              ·
                refine ⟨50161252363966567611893873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133763339637244180298383661 50161252363966567611893873)
                ·
                  refine ⟨37620939272974925708920405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50161252363966567611893873 37620939272974925708920405)
                  ·
                    refine ⟨440870382105174910651411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37620939272974925708920405 440870382105174910651411)
                    ·
                      rfl

theorem cell22_1287888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_1287888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287888 prefixEnd_1287888 := by exact prefixLift 1287888
  have htrace : WordTrace (prefixWord ++ tailWord_1287888) baseStart_1287888 baseEnd_1287888 := by
    simpa [prefixWord, tailWord_1287888, baseEnd_1287888] using wordTrace_append hprefix tailTrace_1287888
  have hstable : (prefixWord ++ tailWord_1287888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287888).length < 2 ^ (prefixWord ++ tailWord_1287888).sum := by decide
  have hdescent : baseEnd_1287888 < baseStart_1287888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287922 : List Nat := [3, 2, 1, 3, 1, 1, 1, 5, 1, 4]
def baseStart_1287922 : Nat := 118140960795 + 1287922 * 2 ^ 59
def prefixEnd_1287922 : Nat := 4983230072969 + 3 ^ 40 * 1287922 * 2
def baseEnd_1287922 : Nat := 440882021000010155301307

theorem tailTrace_1287922 : CollatzResearch.WordTrace tailWord_1287922 prefixEnd_1287922 440882021000010155301307 := by
  unfold tailWord_1287922
  simp only [CollatzResearch.WordTrace]
  refine ⟨11743593610021507102708505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31316249626724018940556013 11743593610021507102708505)
  ·
    refine ⟨8807695207516130327031379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11743593610021507102708505 8807695207516130327031379)
    ·
      refine ⟨13211542811274195490547069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8807695207516130327031379 13211542811274195490547069)
      ·
        refine ⟨4954328554227823308955151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13211542811274195490547069 4954328554227823308955151)
        ·
          refine ⟨7431492831341734963432727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4954328554227823308955151 7431492831341734963432727)
          ·
            refine ⟨11147239247012602445149091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7431492831341734963432727 11147239247012602445149091)
            ·
              refine ⟨16720858870518903667723637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11147239247012602445149091 16720858870518903667723637)
              ·
                refine ⟨1567580519111147218849091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16720858870518903667723637 1567580519111147218849091)
                ·
                  refine ⟨2351370778666720828273637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1567580519111147218849091 2351370778666720828273637)
                  ·
                    refine ⟨440882021000010155301307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2351370778666720828273637 440882021000010155301307)
                    ·
                      rfl

theorem cell22_1287922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_1287922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287922 prefixEnd_1287922 := by exact prefixLift 1287922
  have htrace : WordTrace (prefixWord ++ tailWord_1287922) baseStart_1287922 baseEnd_1287922 := by
    simpa [prefixWord, tailWord_1287922, baseEnd_1287922] using wordTrace_append hprefix tailTrace_1287922
  have hstable : (prefixWord ++ tailWord_1287922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287922).length < 2 ^ (prefixWord ++ tailWord_1287922).sum := by decide
  have hdescent : baseEnd_1287922 < baseStart_1287922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287937 : List Nat := [1, 2, 4, 1, 1, 1, 2, 6, 4]
def baseStart_1287937 : Nat := 118140960795 + 1287937 * 2 ^ 59
def prefixEnd_1287937 : Nat := 4983230072969 + 3 ^ 40 * 1287937 * 2
def baseEnd_1287937 : Nat := 146962385268851705392087

theorem tailTrace_1287937 : CollatzResearch.WordTrace tailWord_1287937 prefixEnd_1287937 146962385268851705392087 := by
  unfold tailWord_1287937
  simp only [CollatzResearch.WordTrace]
  refine ⟨46974921535031685972630065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31316614356687790648420043 46974921535031685972630065)
  ·
    refine ⟨35231191151273764479472549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46974921535031685972630065 35231191151273764479472549)
    ·
      refine ⟨6605848340863830839901103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35231191151273764479472549 6605848340863830839901103)
      ·
        refine ⟨9908772511295746259851655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6605848340863830839901103 9908772511295746259851655)
        ·
          refine ⟨14863158766943619389777483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9908772511295746259851655 14863158766943619389777483)
          ·
            refine ⟨22294738150415429084666225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14863158766943619389777483 22294738150415429084666225)
            ·
              refine ⟨16721053612811571813499669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22294738150415429084666225 16721053612811571813499669)
              ·
                refine ⟨783799388100542428757797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16721053612811571813499669 783799388100542428757797)
                ·
                  refine ⟨146962385268851705392087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 783799388100542428757797 146962385268851705392087)
                  ·
                    rfl

theorem cell22_1287937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 4].length) (baseStart_1287937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287937 prefixEnd_1287937 := by exact prefixLift 1287937
  have htrace : WordTrace (prefixWord ++ tailWord_1287937) baseStart_1287937 baseEnd_1287937 := by
    simpa [prefixWord, tailWord_1287937, baseEnd_1287937] using wordTrace_append hprefix tailTrace_1287937
  have hstable : (prefixWord ++ tailWord_1287937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287937).length < 2 ^ (prefixWord ++ tailWord_1287937).sum := by decide
  have hdescent : baseEnd_1287937 < baseStart_1287937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287950 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 3, 6]
def baseStart_1287950 : Nat := 118140960795 + 1287950 * 2 ^ 59
def prefixEnd_1287950 : Nat := 4983230072969 + 3 ^ 40 * 1287950 * 2
def baseEnd_1287950 : Nat := 440891605972227415601221

theorem tailTrace_1287950 : CollatzResearch.WordTrace tailWord_1287950 prefixEnd_1287950 440891605972227415601221 := by
  unfold tailWord_1287950
  simp only [CollatzResearch.WordTrace]
  refine ⟨5871924460498073649106663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31316930455989726128568869 5871924460498073649106663)
  ·
    refine ⟨8807886690747110473659995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5871924460498073649106663 8807886690747110473659995)
    ·
      refine ⟨13211830036120665710489993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8807886690747110473659995 13211830036120665710489993)
      ·
        refine ⟨9908872527090499282867495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13211830036120665710489993 9908872527090499282867495)
        ·
          refine ⟨14863308790635748924301243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9908872527090499282867495 14863308790635748924301243)
          ·
            refine ⟨22294963185953623386451865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14863308790635748924301243 22294963185953623386451865)
            ·
              refine ⟨16721222389465217539838899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22294963185953623386451865 16721222389465217539838899)
              ·
                refine ⟨25081833584197826309758349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16721222389465217539838899 25081833584197826309758349)
                ·
                  refine ⟨9405687594074184866159381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25081833584197826309758349 9405687594074184866159381)
                  ·
                    refine ⟨440891605972227415601221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9405687594074184866159381 440891605972227415601221)
                    ·
                      rfl

theorem cell22_1287950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_1287950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287950 prefixEnd_1287950 := by exact prefixLift 1287950
  have htrace : WordTrace (prefixWord ++ tailWord_1287950) baseStart_1287950 baseEnd_1287950 := by
    simpa [prefixWord, tailWord_1287950, baseEnd_1287950] using wordTrace_append hprefix tailTrace_1287950
  have hstable : (prefixWord ++ tailWord_1287950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287950).length < 2 ^ (prefixWord ++ tailWord_1287950).sum := by decide
  have hdescent : baseEnd_1287950 < baseStart_1287950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287967 : List Nat := [1, 1, 2, 4, 2, 1, 4, 1, 2, 4]
def baseStart_1287967 : Nat := 118140960795 + 1287967 * 2 ^ 59
def prefixEnd_1287967 : Nat := 4983230072969 + 3 ^ 40 * 1287967 * 2
def baseEnd_1287967 : Nat := 440897425419645037926169

theorem tailTrace_1287967 : CollatzResearch.WordTrace tailWord_1287967 prefixEnd_1287967 440897425419645037926169 := by
  unfold tailWord_1287967
  simp only [CollatzResearch.WordTrace]
  refine ⟨46976015724923001096222155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31317343816615334064148103 46976015724923001096222155)
  ·
    refine ⟨70464023587384501644333233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46976015724923001096222155 70464023587384501644333233)
    ·
      refine ⟨52848017690538376233249925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70464023587384501644333233 52848017690538376233249925)
      ·
        refine ⟨9909003316975945543734361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52848017690538376233249925 9909003316975945543734361)
        ·
          refine ⟨7431752487731959157800771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9909003316975945543734361 7431752487731959157800771)
          ·
            refine ⟨11147628731597938736701157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7431752487731959157800771 11147628731597938736701157)
            ·
              refine ⟨2090180387174613513131467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11147628731597938736701157 2090180387174613513131467)
              ·
                refine ⟨3135270580761920269697201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2090180387174613513131467 3135270580761920269697201)
                ·
                  refine ⟨2351452935571440202272901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3135270580761920269697201 2351452935571440202272901)
                  ·
                    refine ⟨440897425419645037926169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2351452935571440202272901 440897425419645037926169)
                    ·
                      rfl

theorem cell22_1287967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 4].length) (baseStart_1287967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287967 prefixEnd_1287967 := by exact prefixLift 1287967
  have htrace : WordTrace (prefixWord ++ tailWord_1287967) baseStart_1287967 baseEnd_1287967 := by
    simpa [prefixWord, tailWord_1287967, baseEnd_1287967] using wordTrace_append hprefix tailTrace_1287967
  have hstable : (prefixWord ++ tailWord_1287967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287967).length < 2 ^ (prefixWord ++ tailWord_1287967).sum := by decide
  have hdescent : baseEnd_1287967 < baseStart_1287967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287982 : List Nat := [4, 1, 3, 2, 2, 10]
def baseStart_1287982 : Nat := 118140960795 + 1287982 * 2 ^ 59
def prefixEnd_1287982 : Nat := 4983230072969 + 3 ^ 40 * 1287982 * 2
def baseEnd_1287982 : Nat := 5443241484273950602483

theorem tailTrace_1287982 : CollatzResearch.WordTrace tailWord_1287982 prefixEnd_1287982 5443241484273950602483 := by
  unfold tailWord_1287982
  simp only [CollatzResearch.WordTrace]
  refine ⟨5872070352483582332252275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31317708546579105772012133 5872070352483582332252275)
  ·
    refine ⟨8808105528725373498378413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5872070352483582332252275 8808105528725373498378413)
    ·
      refine ⟨3303039573272015061891905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8808105528725373498378413 3303039573272015061891905)
      ·
        refine ⟨2477279679954011296418929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3303039573272015061891905 2477279679954011296418929)
        ·
          refine ⟨1857959759965508472314197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2477279679954011296418929 1857959759965508472314197)
          ·
            refine ⟨5443241484273950602483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1857959759965508472314197 5443241484273950602483)
            ·
              rfl

theorem cell22_1287982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 10].length) (baseStart_1287982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287982 prefixEnd_1287982 := by exact prefixLift 1287982
  have htrace : WordTrace (prefixWord ++ tailWord_1287982) baseStart_1287982 baseEnd_1287982 := by
    simpa [prefixWord, tailWord_1287982, baseEnd_1287982] using wordTrace_append hprefix tailTrace_1287982
  have hstable : (prefixWord ++ tailWord_1287982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287982).length < 2 ^ (prefixWord ++ tailWord_1287982).sum := by decide
  have hdescent : baseEnd_1287982 < baseStart_1287982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287988 : List Nat := [2, 5, 1, 1, 2, 3, 2, 2, 4]
def baseStart_1287988 : Nat := 118140960795 + 1287988 * 2 ^ 59
def prefixEnd_1287988 : Nat := 4983230072969 + 3 ^ 40 * 1287988 * 2
def baseEnd_1287988 : Nat := 146968204716269327717035

theorem tailTrace_1287988 : CollatzResearch.WordTrace tailWord_1287988 prefixEnd_1287988 146968204716269327717035 := by
  unfold tailWord_1287988
  simp only [CollatzResearch.WordTrace]
  refine ⟨23488390828923460841368309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31317854438564614455157745 23488390828923460841368309)
  ·
    refine ⟨2202036640211574453878279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23488390828923460841368309 2202036640211574453878279)
    ·
      refine ⟨3303054960317361680817419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2202036640211574453878279 3303054960317361680817419)
      ·
        refine ⟨4954582440476042521226129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3303054960317361680817419 4954582440476042521226129)
        ·
          refine ⟨3715936830357031890919597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4954582440476042521226129 3715936830357031890919597)
          ·
            refine ⟨1393476311383886959094849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3715936830357031890919597 1393476311383886959094849)
            ·
              refine ⟨1045107233537915219321137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1393476311383886959094849 1045107233537915219321137)
              ·
                refine ⟨783830425153436414490853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1045107233537915219321137 783830425153436414490853)
                ·
                  refine ⟨146968204716269327717035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 783830425153436414490853 146968204716269327717035)
                  ·
                    rfl

theorem cell22_1287988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_1287988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287988 prefixEnd_1287988 := by exact prefixLift 1287988
  have htrace : WordTrace (prefixWord ++ tailWord_1287988) baseStart_1287988 baseEnd_1287988 := by
    simpa [prefixWord, tailWord_1287988, baseEnd_1287988] using wordTrace_append hprefix tailTrace_1287988
  have hstable : (prefixWord ++ tailWord_1287988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287988).length < 2 ^ (prefixWord ++ tailWord_1287988).sum := by decide
  have hdescent : baseEnd_1287988 < baseStart_1287988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287999 : List Nat := [1, 1, 2, 2, 7, 1, 1, 7]
def baseStart_1287999 : Nat := 118140960795 + 1287999 * 2 ^ 59
def prefixEnd_1287999 : Nat := 4983230072969 + 3 ^ 40 * 1287999 * 2
def baseEnd_1287999 : Nat := 48989819963734180125119

theorem tailTrace_1287999 : CollatzResearch.WordTrace tailWord_1287999 prefixEnd_1287999 48989819963734180125119 := by
  unfold tailWord_1287999
  simp only [CollatzResearch.WordTrace]
  refine ⟨46977182860807070561387051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31318121907204713707591367 46977182860807070561387051)
  ·
    refine ⟨70465774291210605842080577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46977182860807070561387051 70465774291210605842080577)
    ·
      refine ⟨52849330718407954381560433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70465774291210605842080577 52849330718407954381560433)
      ·
        refine ⟨39636998038805965786170325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52849330718407954381560433 39636998038805965786170325)
        ·
          refine ⟨928992141534514823113367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 39636998038805965786170325 928992141534514823113367)
          ·
            refine ⟨1393488212301772234670051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 928992141534514823113367 1393488212301772234670051)
            ·
              refine ⟨2090232318452658352005077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1393488212301772234670051 2090232318452658352005077)
              ·
                refine ⟨48989819963734180125119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2090232318452658352005077 48989819963734180125119)
                ·
                  rfl

theorem cell22_1287999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 7].length) (baseStart_1287999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287999 prefixEnd_1287999 := by exact prefixLift 1287999
  have htrace : WordTrace (prefixWord ++ tailWord_1287999) baseStart_1287999 baseEnd_1287999 := by
    simpa [prefixWord, tailWord_1287999, baseEnd_1287999] using wordTrace_append hprefix tailTrace_1287999
  have hstable : (prefixWord ++ tailWord_1287999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287999).length < 2 ^ (prefixWord ++ tailWord_1287999).sum := by decide
  have hdescent : baseEnd_1287999 < baseStart_1287999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288025 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 1, 7]
def baseStart_1288025 : Nat := 118140960795 + 1288025 * 2 ^ 59
def prefixEnd_1288025 : Nat := 4983230072969 + 3 ^ 40 * 1288025 * 2
def baseEnd_1288025 : Nat := 440917280004952219975991

theorem tailTrace_1288025 : CollatzResearch.WordTrace tailWord_1288025 prefixEnd_1288025 440917280004952219975991 := by
  unfold tailWord_1288025
  simp only [CollatzResearch.WordTrace]
  refine ⟨46978131158712877001833529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31318754105808584667889019 46978131158712877001833529)
  ·
    refine ⟨35233598369034657751375147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46978131158712877001833529 35233598369034657751375147)
    ·
      refine ⟨52850397553551986627062721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35233598369034657751375147 52850397553551986627062721)
      ·
        refine ⟨39637798165163989970297041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52850397553551986627062721 39637798165163989970297041)
        ·
          refine ⟨29728348623872992477722781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39637798165163989970297041 29728348623872992477722781)
          ·
            refine ⟨11148130733952372179146043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29728348623872992477722781 11148130733952372179146043)
            ·
              refine ⟨16722196100928558268719065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11148130733952372179146043 16722196100928558268719065)
              ·
                refine ⟨12541647075696418701539299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16722196100928558268719065 12541647075696418701539299)
                ·
                  refine ⟨18812470613544628052308949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12541647075696418701539299 18812470613544628052308949)
                  ·
                    refine ⟨440917280004952219975991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18812470613544628052308949 440917280004952219975991)
                    ·
                      rfl

theorem cell22_1288025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_1288025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1288025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1288025 prefixEnd_1288025 := by exact prefixLift 1288025
  have htrace : WordTrace (prefixWord ++ tailWord_1288025) baseStart_1288025 baseEnd_1288025 := by
    simpa [prefixWord, tailWord_1288025, baseEnd_1288025] using wordTrace_append hprefix tailTrace_1288025
  have hstable : (prefixWord ++ tailWord_1288025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288025).length < 2 ^ (prefixWord ++ tailWord_1288025).sum := by decide
  have hdescent : baseEnd_1288025 < baseStart_1288025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288031 : List Nat := [1, 1, 2, 3, 1, 5, 2, 3, 1, 3]
def baseStart_1288031 : Nat := 118140960795 + 1288031 * 2 ^ 59
def prefixEnd_1288031 : Nat := 4983230072969 + 3 ^ 40 * 1288031 * 2
def baseEnd_1288031 : Nat := 440919333927570204325973

theorem tailTrace_1288031 : CollatzResearch.WordTrace tailWord_1288031 prefixEnd_1288031 440919333927570204325973 := by
  unfold tailWord_1288031
  simp only [CollatzResearch.WordTrace]
  refine ⟨46978349996691140026551947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31318899997794093351034631 46978349996691140026551947)
  ·
    refine ⟨70467524995036710039827921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46978349996691140026551947 70467524995036710039827921)
    ·
      refine ⟨52850643746277532529870941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70467524995036710039827921 52850643746277532529870941)
      ·
        refine ⟨19818991404854074698701603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52850643746277532529870941 19818991404854074698701603)
        ·
          refine ⟨29728487107281112048052405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19818991404854074698701603 29728487107281112048052405)
          ·
            refine ⟨2787045666307604254504913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29728487107281112048052405 2787045666307604254504913)
            ·
              refine ⟨2090284249730703190878685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2787045666307604254504913 2090284249730703190878685)
              ·
                refine ⟨783856593649013696579507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2090284249730703190878685 783856593649013696579507)
                ·
                  refine ⟨1175784890473520544869261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 783856593649013696579507 1175784890473520544869261)
                  ·
                    refine ⟨440919333927570204325973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1175784890473520544869261 440919333927570204325973)
                    ·
                      rfl

theorem cell22_1288031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 1, 3].length) (baseStart_1288031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1288031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1288031 prefixEnd_1288031 := by exact prefixLift 1288031
  have htrace : WordTrace (prefixWord ++ tailWord_1288031) baseStart_1288031 baseEnd_1288031 := by
    simpa [prefixWord, tailWord_1288031, baseEnd_1288031] using wordTrace_append hprefix tailTrace_1288031
  have hstable : (prefixWord ++ tailWord_1288031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288031).length < 2 ^ (prefixWord ++ tailWord_1288031).sum := by decide
  have hdescent : baseEnd_1288031 < baseStart_1288031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288044 : List Nat := [2, 2, 1, 1, 4, 4, 1, 2, 5]
def baseStart_1288044 : Nat := 118140960795 + 1288044 * 2 ^ 59
def prefixEnd_1288044 : Nat := 4983230072969 + 3 ^ 40 * 1288044 * 2
def baseEnd_1288044 : Nat := 146974594697747501250311

theorem tailTrace_1288044 : CollatzResearch.WordTrace tailWord_1288044 prefixEnd_1288044 146974594697747501250311 := by
  unfold tailWord_1288044
  simp only [CollatzResearch.WordTrace]
  refine ⟨23489412072822021623387593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31319216097096028831183457 23489412072822021623387593)
  ·
    refine ⟨17617059054616516217540695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23489412072822021623387593 17617059054616516217540695)
    ·
      refine ⟨26425588581924774326311043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17617059054616516217540695 26425588581924774326311043)
      ·
        refine ⟨39638382872887161489466565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26425588581924774326311043 39638382872887161489466565)
        ·
          refine ⟨7432196788666342779274981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39638382872887161489466565 7432196788666342779274981)
          ·
            refine ⟨1393536897874939271114059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7432196788666342779274981 1393536897874939271114059)
            ·
              refine ⟨2090305346812408906671089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1393536897874939271114059 2090305346812408906671089)
              ·
                refine ⟨1567729010109306680003317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2090305346812408906671089 1567729010109306680003317)
                ·
                  refine ⟨146974594697747501250311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1567729010109306680003317 146974594697747501250311)
                  ·
                    rfl

theorem cell22_1288044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 5].length) (baseStart_1288044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1288044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1288044 prefixEnd_1288044 := by exact prefixLift 1288044
  have htrace : WordTrace (prefixWord ++ tailWord_1288044) baseStart_1288044 baseEnd_1288044 := by
    simpa [prefixWord, tailWord_1288044, baseEnd_1288044] using wordTrace_append hprefix tailTrace_1288044
  have hstable : (prefixWord ++ tailWord_1288044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288044).length < 2 ^ (prefixWord ++ tailWord_1288044).sum := by decide
  have hdescent : baseEnd_1288044 < baseStart_1288044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288089 : List Nat := [1, 2, 1, 2, 1, 3, 5, 3, 4]
def baseStart_1288089 : Nat := 118140960795 + 1288089 * 2 ^ 59
def prefixEnd_1288089 : Nat := 4983230072969 + 3 ^ 40 * 1288089 * 2
def baseEnd_1288089 : Nat := 146979729504292462125265

theorem tailTrace_1288089 : CollatzResearch.WordTrace tailWord_1288089 prefixEnd_1288089 146979729504292462125265 := by
  unfold tailWord_1288089
  simp only [CollatzResearch.WordTrace]
  refine ⟨46980465430481015932163321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31320310286987343954775547 46980465430481015932163321)
  ·
    refine ⟨35235349072860761949122491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46980465430481015932163321 35235349072860761949122491)
    ·
      refine ⟨52853023609291142923683737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35235349072860761949122491 52853023609291142923683737)
      ·
        refine ⟨39639767706968357192762803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52853023609291142923683737 39639767706968357192762803)
        ·
          refine ⟨59459651560452535789144205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39639767706968357192762803 59459651560452535789144205)
          ·
            refine ⟨22297369335169700920929077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59459651560452535789144205 22297369335169700920929077)
            ·
              refine ⟨2090378375172159461337101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22297369335169700920929077 2090378375172159461337101)
              ·
                refine ⟨783891890689559798001413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2090378375172159461337101 783891890689559798001413)
                ·
                  refine ⟨146979729504292462125265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 783891890689559798001413 146979729504292462125265)
                  ·
                    rfl

theorem cell22_1288089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 4].length) (baseStart_1288089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1288089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1288089 prefixEnd_1288089 := by exact prefixLift 1288089
  have htrace : WordTrace (prefixWord ++ tailWord_1288089) baseStart_1288089 baseEnd_1288089 := by
    simpa [prefixWord, tailWord_1288089, baseEnd_1288089] using wordTrace_append hprefix tailTrace_1288089
  have hstable : (prefixWord ++ tailWord_1288089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288089).length < 2 ^ (prefixWord ++ tailWord_1288089).sum := by decide
  have hdescent : baseEnd_1288089 < baseStart_1288089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288117 : List Nat := [1, 3, 3, 2, 1, 2, 1, 9]
def baseStart_1288117 : Nat := 118140960795 + 1288117 * 2 ^ 59
def prefixEnd_1288117 : Nat := 4983230072969 + 3 ^ 40 * 1288117 * 2
def baseEnd_1288117 : Nat := 48994308165010516297301

theorem tailTrace_1288117 : CollatzResearch.WordTrace tailWord_1288117 prefixEnd_1288117 48994308165010516297301 := by
  unfold tailWord_1288117
  simp only [CollatzResearch.WordTrace]
  refine ⟨46981486674379576714182605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31320991116253051142788403 46981486674379576714182605)
  ·
    refine ⟨17618057502892341267818477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46981486674379576714182605 17618057502892341267818477)
    ·
      refine ⟨6606771563584627975431929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17618057502892341267818477 6606771563584627975431929)
      ·
        refine ⟨4955078672688470981573947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6606771563584627975431929 4955078672688470981573947)
        ·
          refine ⟨7432618009032706472360921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4955078672688470981573947 7432618009032706472360921)
          ·
            refine ⟨5574463506774529854270691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7432618009032706472360921 5574463506774529854270691)
            ·
              refine ⟨8361695260161794781406037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5574463506774529854270691 8361695260161794781406037)
              ·
                refine ⟨48994308165010516297301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8361695260161794781406037 48994308165010516297301)
                ·
                  rfl

theorem cell22_1288117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 9].length) (baseStart_1288117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1288117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1288117 prefixEnd_1288117 := by exact prefixLift 1288117
  have htrace : WordTrace (prefixWord ++ tailWord_1288117) baseStart_1288117 baseEnd_1288117 := by
    simpa [prefixWord, tailWord_1288117, baseEnd_1288117] using wordTrace_append hprefix tailTrace_1288117
  have hstable : (prefixWord ++ tailWord_1288117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288117).length < 2 ^ (prefixWord ++ tailWord_1288117).sum := by decide
  have hdescent : baseEnd_1288117 < baseStart_1288117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288213 : List Nat := [1, 3, 2, 1, 6, 1, 1, 2, 5]
def baseStart_1288213 : Nat := 118140960795 + 1288213 * 2 ^ 59
def prefixEnd_1288213 : Nat := 4983230072969 + 3 ^ 40 * 1288213 * 2
def baseEnd_1288213 : Nat := 146993878748994132091805

theorem tailTrace_1288213 : CollatzResearch.WordTrace tailWord_1288213 prefixEnd_1288213 146993878748994132091805 := by
  unfold tailWord_1288213
  simp only [CollatzResearch.WordTrace]
  refine ⟨46984988082031785109677293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31323325388021190073118195 46984988082031785109677293)
  ·
    refine ⟨17619370530761919416128985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46984988082031785109677293 17619370530761919416128985)
    ·
      refine ⟨13214527898071439562096739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17619370530761919416128985 13214527898071439562096739)
      ·
        refine ⟨19821791847107159343145109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13214527898071439562096739 19821791847107159343145109)
        ·
          refine ⟨929146492833148094209927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19821791847107159343145109 929146492833148094209927)
          ·
            refine ⟨1393719739249722141314891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929146492833148094209927 1393719739249722141314891)
            ·
              refine ⟨2090579608874583211972337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1393719739249722141314891 2090579608874583211972337)
              ·
                refine ⟨1567934706655937408979253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2090579608874583211972337 1567934706655937408979253)
                ·
                  refine ⟨146993878748994132091805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1567934706655937408979253 146993878748994132091805)
                  ·
                    rfl

theorem cell22_1288213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 5].length) (baseStart_1288213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1288213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1288213 prefixEnd_1288213 := by exact prefixLift 1288213
  have htrace : WordTrace (prefixWord ++ tailWord_1288213) baseStart_1288213 baseEnd_1288213 := by
    simpa [prefixWord, tailWord_1288213, baseEnd_1288213] using wordTrace_append hprefix tailTrace_1288213
  have hstable : (prefixWord ++ tailWord_1288213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288213).length < 2 ^ (prefixWord ++ tailWord_1288213).sum := by decide
  have hdescent : baseEnd_1288213 < baseStart_1288213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288267 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 1, 9]
def baseStart_1288267 : Nat := 118140960795 + 1288267 * 2 ^ 59
def prefixEnd_1288267 : Nat := 4983230072969 + 3 ^ 40 * 1288267 * 2
def baseEnd_1288267 : Nat := 441000121550544255425249

theorem tailTrace_1288267 : CollatzResearch.WordTrace tailWord_1288267 prefixEnd_1288267 441000121550544255425249 := by
  unfold tailWord_1288267
  simp only [CollatzResearch.WordTrace]
  refine ⟨46986957623836152332143055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31324638415890768221428703 46986957623836152332143055)
  ·
    refine ⟨70480436435754228498214583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46986957623836152332143055 70480436435754228498214583)
    ·
      refine ⟨105720654653631342747321875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70480436435754228498214583 105720654653631342747321875)
      ·
        refine ⟨158580981980447014120982813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105720654653631342747321875 158580981980447014120982813)
        ·
          refine ⟨59467868242667630295368555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158580981980447014120982813 59467868242667630295368555)
          ·
            refine ⟨89201802364001445443052833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59467868242667630295368555 89201802364001445443052833)
            ·
              refine ⟨66901351773001084082289625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89201802364001445443052833 66901351773001084082289625)
              ·
                refine ⟨50176013829750813061717219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66901351773001084082289625 50176013829750813061717219)
                ·
                  refine ⟨75264020744626219592575829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50176013829750813061717219 75264020744626219592575829)
                  ·
                    refine ⟨441000121550544255425249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 75264020744626219592575829 441000121550544255425249)
                    ·
                      rfl

theorem cell22_1288267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 9].length) (baseStart_1288267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1288267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1288267 prefixEnd_1288267 := by exact prefixLift 1288267
  have htrace : WordTrace (prefixWord ++ tailWord_1288267) baseStart_1288267 baseEnd_1288267 := by
    simpa [prefixWord, tailWord_1288267, baseEnd_1288267] using wordTrace_append hprefix tailTrace_1288267
  have hstable : (prefixWord ++ tailWord_1288267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288267).length < 2 ^ (prefixWord ++ tailWord_1288267).sum := by decide
  have hdescent : baseEnd_1288267 < baseStart_1288267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288290 : List Nat := [3, 3, 2, 2, 2, 1, 1, 3, 2, 3]
def baseStart_1288290 : Nat := 118140960795 + 1288290 * 2 ^ 59
def prefixEnd_1288290 : Nat := 4983230072969 + 3 ^ 40 * 1288290 * 2
def baseEnd_1288290 : Nat := 441007994920579862100179

theorem tailTrace_1288290 : CollatzResearch.WordTrace tailWord_1288290 prefixEnd_1288290 441007994920579862100179 := by
  unfold tailWord_1288290
  simp only [CollatzResearch.WordTrace]
  refine ⟨11746949125688206815057581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31325197668501884840153549 11746949125688206815057581)
  ·
    refine ⟨4405105922133077555646593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11746949125688206815057581 4405105922133077555646593)
    ·
      refine ⟨3303829441599808166734945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4405105922133077555646593 3303829441599808166734945)
      ·
        refine ⟨2477872081199856125051209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3303829441599808166734945 2477872081199856125051209)
        ·
          refine ⟨1858404060899892093788407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2477872081199856125051209 1858404060899892093788407)
          ·
            refine ⟨2787606091349838140682611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1858404060899892093788407 2787606091349838140682611)
            ·
              refine ⟨4181409137024757211023917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2787606091349838140682611 4181409137024757211023917)
              ·
                refine ⟨1568028426384283954133969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4181409137024757211023917 1568028426384283954133969)
                ·
                  refine ⟨1176021319788212965600477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1568028426384283954133969 1176021319788212965600477)
                  ·
                    refine ⟨441007994920579862100179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1176021319788212965600477 441007994920579862100179)
                    ·
                      rfl

theorem cell22_1288290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_1288290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1288290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1288290 prefixEnd_1288290 := by exact prefixLift 1288290
  have htrace : WordTrace (prefixWord ++ tailWord_1288290) baseStart_1288290 baseEnd_1288290 := by
    simpa [prefixWord, tailWord_1288290, baseEnd_1288290] using wordTrace_append hprefix tailTrace_1288290
  have hstable : (prefixWord ++ tailWord_1288290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288290).length < 2 ^ (prefixWord ++ tailWord_1288290).sum := by decide
  have hdescent : baseEnd_1288290 < baseStart_1288290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288301 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 5, 3]
def baseStart_1288301 : Nat := 118140960795 + 1288301 * 2 ^ 59
def prefixEnd_1288301 : Nat := 4983230072969 + 3 ^ 40 * 1288301 * 2
def baseEnd_1288301 : Nat := 441011760445379500075145

theorem tailTrace_1288301 : CollatzResearch.WordTrace tailWord_1288301 prefixEnd_1288301 441011760445379500075145 := by
  unfold tailWord_1288301
  simp only [CollatzResearch.WordTrace]
  refine ⟨46988197705712976138880757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31325465137141984092587171 46988197705712976138880757)
  ·
    refine ⟨4405143534910591513020071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46988197705712976138880757 4405143534910591513020071)
    ·
      refine ⟨6607715302365887269530107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4405143534910591513020071 6607715302365887269530107)
      ·
        refine ⟨9911572953548830904295161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6607715302365887269530107 9911572953548830904295161)
        ·
          refine ⟨7433679715161623178221371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9911572953548830904295161 7433679715161623178221371)
          ·
            refine ⟨11150519572742434767332057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7433679715161623178221371 11150519572742434767332057)
            ·
              refine ⟨8362889679556826075499043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11150519572742434767332057 8362889679556826075499043)
              ·
                refine ⟨12544334519335239113248565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8362889679556826075499043 12544334519335239113248565)
                ·
                  refine ⟨1176031361187678666867053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12544334519335239113248565 1176031361187678666867053)
                  ·
                    refine ⟨441011760445379500075145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1176031361187678666867053 441011760445379500075145)
                    ·
                      rfl

theorem cell22_1288301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_1288301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1288301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1288301 prefixEnd_1288301 := by exact prefixLift 1288301
  have htrace : WordTrace (prefixWord ++ tailWord_1288301) baseStart_1288301 baseEnd_1288301 := by
    simpa [prefixWord, tailWord_1288301, baseEnd_1288301] using wordTrace_append hprefix tailTrace_1288301
  have hstable : (prefixWord ++ tailWord_1288301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288301).length < 2 ^ (prefixWord ++ tailWord_1288301).sum := by decide
  have hdescent : baseEnd_1288301 < baseStart_1288301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288329 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 2, 5]
def baseStart_1288329 : Nat := 118140960795 + 1288329 * 2 ^ 59
def prefixEnd_1288329 : Nat := 4983230072969 + 3 ^ 40 * 1288329 * 2
def baseEnd_1288329 : Nat := 441021345417596760375059

theorem tailTrace_1288329 : CollatzResearch.WordTrace tailWord_1288329 prefixEnd_1288329 441021345417596760375059 := by
  unfold tailWord_1288329
  simp only [CollatzResearch.WordTrace]
  refine ⟨46989218949611536920900041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31326145966407691280600027 46989218949611536920900041)
  ·
    refine ⟨35241914212208652690675031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46989218949611536920900041 35241914212208652690675031)
    ·
      refine ⟨52862871318312979036012547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35241914212208652690675031 52862871318312979036012547)
      ·
        refine ⟨79294306977469468554018821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52862871318312979036012547 79294306977469468554018821)
        ·
          refine ⟨14867682558275525353878529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79294306977469468554018821 14867682558275525353878529)
          ·
            refine ⟨11150761918706644015408897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14867682558275525353878529 11150761918706644015408897)
            ·
              refine ⟨8363071439029983011556673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11150761918706644015408897 8363071439029983011556673)
              ·
                refine ⟨6272303579272487258667505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8363071439029983011556673 6272303579272487258667505)
                ·
                  refine ⟨4704227684454365444000629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6272303579272487258667505 4704227684454365444000629)
                  ·
                    refine ⟨441021345417596760375059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4704227684454365444000629 441021345417596760375059)
                    ·
                      rfl

theorem cell22_1288329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_1288329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1288329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1288329 prefixEnd_1288329 := by exact prefixLift 1288329
  have htrace : WordTrace (prefixWord ++ tailWord_1288329) baseStart_1288329 baseEnd_1288329 := by
    simpa [prefixWord, tailWord_1288329, baseEnd_1288329] using wordTrace_append hprefix tailTrace_1288329
  have hstable : (prefixWord ++ tailWord_1288329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288329).length < 2 ^ (prefixWord ++ tailWord_1288329).sum := by decide
  have hdescent : baseEnd_1288329 < baseStart_1288329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288378 : List Nat := [3, 1, 1, 1, 2, 2, 6, 1, 1, 4]
def baseStart_1288378 : Nat := 118140960795 + 1288378 * 2 ^ 59
def prefixEnd_1288378 : Nat := 4983230072969 + 3 ^ 40 * 1288378 * 2
def baseEnd_1288378 : Nat := 441038119118976965899909

theorem tailTrace_1288378 : CollatzResearch.WordTrace tailWord_1288378 prefixEnd_1288378 441038119118976965899909 := by
  unfold tailWord_1288378
  simp only [CollatzResearch.WordTrace]
  refine ⟨11747751531608504572358447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31327337417622678859622525 11747751531608504572358447)
  ·
    refine ⟨17621627297412756858537671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11747751531608504572358447 17621627297412756858537671)
    ·
      refine ⟨26432440946119135287806507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17621627297412756858537671 26432440946119135287806507)
      ·
        refine ⟨39648661419178702931709761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26432440946119135287806507 39648661419178702931709761)
        ·
          refine ⟨29736496064384027198782321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39648661419178702931709761 29736496064384027198782321)
          ·
            refine ⟨22302372048288020399086741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29736496064384027198782321 22302372048288020399086741)
            ·
              refine ⟨1045423689763500956207191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22302372048288020399086741 1045423689763500956207191)
              ·
                refine ⟨1568135534645251434310787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1045423689763500956207191 1568135534645251434310787)
                ·
                  refine ⟨2352203301967877151466181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1568135534645251434310787 2352203301967877151466181)
                  ·
                    refine ⟨441038119118976965899909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2352203301967877151466181 441038119118976965899909)
                    ·
                      rfl

theorem cell22_1288378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 1, 4].length) (baseStart_1288378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1288378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1288378 prefixEnd_1288378 := by exact prefixLift 1288378
  have htrace : WordTrace (prefixWord ++ tailWord_1288378) baseStart_1288378 baseEnd_1288378 := by
    simpa [prefixWord, tailWord_1288378, baseEnd_1288378] using wordTrace_append hprefix tailTrace_1288378
  have hstable : (prefixWord ++ tailWord_1288378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288378).length < 2 ^ (prefixWord ++ tailWord_1288378).sum := by decide
  have hdescent : baseEnd_1288378 < baseStart_1288378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288408 : List Nat := [2, 1, 2, 2, 4, 3, 1, 1, 1, 5]
def baseStart_1288408 : Nat := 118140960795 + 1288408 * 2 ^ 59
def prefixEnd_1288408 : Nat := 4983230072969 + 3 ^ 40 * 1288408 * 2
def baseEnd_1288408 : Nat := 441048388732066887649817

theorem tailTrace_1288408 : CollatzResearch.WordTrace tailWord_1288408 prefixEnd_1288408 441048388732066887649817 := by
  unfold tailWord_1288408
  simp only [CollatzResearch.WordTrace]
  refine ⟨23496050158162666706512939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31328066877550222275350585 23496050158162666706512939)
  ·
    refine ⟨35244075237244000059769409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23496050158162666706512939 35244075237244000059769409)
    ·
      refine ⟨26433056427933000044827057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35244075237244000059769409 26433056427933000044827057)
      ·
        refine ⟨19824792320949750033620293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26433056427933000044827057 19824792320949750033620293)
        ·
          refine ⟨3717148560178078131303805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19824792320949750033620293 3717148560178078131303805)
          ·
            refine ⟨1393930710066779299238927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3717148560178078131303805 1393930710066779299238927)
            ·
              refine ⟨2090896065100168948858391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1393930710066779299238927 2090896065100168948858391)
              ·
                refine ⟨3136344097650253423287587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2090896065100168948858391 3136344097650253423287587)
                ·
                  refine ⟨4704516146475380134931381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3136344097650253423287587 4704516146475380134931381)
                  ·
                    refine ⟨441048388732066887649817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4704516146475380134931381 441048388732066887649817)
                    ·
                      rfl

theorem cell22_1288408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 1, 5].length) (baseStart_1288408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1288408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1288408 prefixEnd_1288408 := by exact prefixLift 1288408
  have htrace : WordTrace (prefixWord ++ tailWord_1288408) baseStart_1288408 baseEnd_1288408 := by
    simpa [prefixWord, tailWord_1288408, baseEnd_1288408] using wordTrace_append hprefix tailTrace_1288408
  have hstable : (prefixWord ++ tailWord_1288408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288408).length < 2 ^ (prefixWord ++ tailWord_1288408).sum := by decide
  have hdescent : baseEnd_1288408 < baseStart_1288408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288412 : List Nat := [2, 2, 5, 2, 1, 1, 2, 2, 1, 4]
def baseStart_1288412 : Nat := 118140960795 + 1288412 * 2 ^ 59
def prefixEnd_1288412 : Nat := 4983230072969 + 3 ^ 40 * 1288412 * 2
def baseEnd_1288412 : Nat := 441049758013812210549805

theorem tailTrace_1288412 : CollatzResearch.WordTrace tailWord_1288412 prefixEnd_1288412 441049758013812210549805 := by
  unfold tailWord_1288412
  simp only [CollatzResearch.WordTrace]
  refine ⟨23496123104155421048085745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31328164138873894730780993 23496123104155421048085745)
  ·
    refine ⟨17622092328116565786064309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23496123104155421048085745 17622092328116565786064309)
    ·
      refine ⟨1652071155760928042443529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17622092328116565786064309 1652071155760928042443529)
      ·
        refine ⟨1239053366820696031832647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1652071155760928042443529 1239053366820696031832647)
        ·
          refine ⟨1858580050231044047748971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1239053366820696031832647 1858580050231044047748971)
          ·
            refine ⟨2787870075346566071623457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1858580050231044047748971 2787870075346566071623457)
            ·
              refine ⟨2090902556509924553717593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2787870075346566071623457 2090902556509924553717593)
              ·
                refine ⟨1568176917382443415288195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2090902556509924553717593 1568176917382443415288195)
                ·
                  refine ⟨2352265376073665122932293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1568176917382443415288195 2352265376073665122932293)
                  ·
                    refine ⟨441049758013812210549805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2352265376073665122932293 441049758013812210549805)
                    ·
                      rfl

theorem cell22_1288412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_1288412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1288412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1288412 prefixEnd_1288412 := by exact prefixLift 1288412
  have htrace : WordTrace (prefixWord ++ tailWord_1288412) baseStart_1288412 baseEnd_1288412 := by
    simpa [prefixWord, tailWord_1288412, baseEnd_1288412] using wordTrace_append hprefix tailTrace_1288412
  have hstable : (prefixWord ++ tailWord_1288412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288412).length < 2 ^ (prefixWord ++ tailWord_1288412).sum := by decide
  have hdescent : baseEnd_1288412 < baseStart_1288412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288421 : List Nat := [1, 3, 1, 4, 2, 2, 1, 8]
def baseStart_1288421 : Nat := 118140960795 + 1288421 * 2 ^ 59
def prefixEnd_1288421 : Nat := 4983230072969 + 3 ^ 40 * 1288421 * 2
def baseEnd_1288421 : Nat := 49005870988637687452753

theorem tailTrace_1288421 : CollatzResearch.WordTrace tailWord_1288421 prefixEnd_1288421 49005870988637687452753 := by
  unfold tailWord_1288421
  simp only [CollatzResearch.WordTrace]
  refine ⟨46992574465278236633249117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31328382976852157755499411 46992574465278236633249117)
  ·
    refine ⟨17622215424479338737468419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46992574465278236633249117 17622215424479338737468419)
    ·
      refine ⟨26433323136719008106202629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17622215424479338737468419 26433323136719008106202629)
      ·
        refine ⟨4956248088134814019912993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26433323136719008106202629 4956248088134814019912993)
        ·
          refine ⟨3717186066101110514934745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4956248088134814019912993 3717186066101110514934745)
          ·
            refine ⟨2787889549575832886201059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3717186066101110514934745 2787889549575832886201059)
            ·
              refine ⟨4181834324363749329301589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2787889549575832886201059 4181834324363749329301589)
              ·
                refine ⟨49005870988637687452753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4181834324363749329301589 49005870988637687452753)
                ·
                  rfl

theorem cell22_1288421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 8].length) (baseStart_1288421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1288421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1288421 prefixEnd_1288421 := by exact prefixLift 1288421
  have htrace : WordTrace (prefixWord ++ tailWord_1288421) baseStart_1288421 baseEnd_1288421 := by
    simpa [prefixWord, tailWord_1288421, baseEnd_1288421] using wordTrace_append hprefix tailTrace_1288421
  have hstable : (prefixWord ++ tailWord_1288421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288421).length < 2 ^ (prefixWord ++ tailWord_1288421).sum := by decide
  have hdescent : baseEnd_1288421 < baseStart_1288421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288500 : List Nat := [2, 5, 1, 1, 1, 3, 2, 2, 5]
def baseStart_1288500 : Nat := 118140960795 + 1288500 * 2 ^ 59
def prefixEnd_1288500 : Nat := 4983230072969 + 3 ^ 40 * 1288500 * 2
def baseEnd_1288500 : Nat := 147026627404069771449845

theorem tailTrace_1288500 : CollatzResearch.WordTrace tailWord_1288500 prefixEnd_1288500 147026627404069771449845 := by
  unfold tailWord_1288500
  simp only [CollatzResearch.WordTrace]
  refine ⟨23497727915996016562687477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31330303887994688750249969 23497727915996016562687477)
  ·
    refine ⟨2202911992124626552751951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23497727915996016562687477 2202911992124626552751951)
    ·
      refine ⟨3304367988186939829127927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2202911992124626552751951 3304367988186939829127927)
      ·
        refine ⟨4956551982280409743691891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3304367988186939829127927 4956551982280409743691891)
        ·
          refine ⟨7434827973420614615537837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4956551982280409743691891 7434827973420614615537837)
          ·
            refine ⟨2788060490032730480826689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7434827973420614615537837 2788060490032730480826689)
            ·
              refine ⟨2091045367524547860620017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2788060490032730480826689 2091045367524547860620017)
              ·
                refine ⟨1568284025643410895465013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2091045367524547860620017 1568284025643410895465013)
                ·
                  refine ⟨147026627404069771449845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1568284025643410895465013 147026627404069771449845)
                  ·
                    rfl

theorem cell22_1288500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_1288500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1288500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1288500 prefixEnd_1288500 := by exact prefixLift 1288500
  have htrace : WordTrace (prefixWord ++ tailWord_1288500) baseStart_1288500 baseEnd_1288500 := by
    simpa [prefixWord, tailWord_1288500, baseEnd_1288500] using wordTrace_append hprefix tailTrace_1288500
  have hstable : (prefixWord ++ tailWord_1288500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288500).length < 2 ^ (prefixWord ++ tailWord_1288500).sum := by decide
  have hdescent : baseEnd_1288500 < baseStart_1288500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288511 : List Nat := [1, 1, 2, 2, 4, 1, 2, 3, 6]
def baseStart_1288511 : Nat := 118140960795 + 1288511 * 2 ^ 59
def prefixEnd_1288511 : Nat := 4983230072969 + 3 ^ 40 * 1288511 * 2
def baseEnd_1288511 : Nat := 147027882579002984108167

theorem tailTrace_1288511 : CollatzResearch.WordTrace tailWord_1288511 prefixEnd_1288511 147027882579002984108167 := by
  unfold tailWord_1288511
  simp only [CollatzResearch.WordTrace]
  refine ⟨46995857034952182004025387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31330571356634788002683591 46995857034952182004025387)
  ·
    refine ⟨70493785552428273006038081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46995857034952182004025387 70493785552428273006038081)
    ·
      refine ⟨52870339164321204754528561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70493785552428273006038081 52870339164321204754528561)
      ·
        refine ⟨39652754373240903565896421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52870339164321204754528561 39652754373240903565896421)
        ·
          refine ⟨7434891444982669418605579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39652754373240903565896421 7434891444982669418605579)
          ·
            refine ⟨11152337167474004127908369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7434891444982669418605579 11152337167474004127908369)
            ·
              refine ⟨8364252875605503095931277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11152337167474004127908369 8364252875605503095931277)
              ·
                refine ⟨3136594828352063660974229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8364252875605503095931277 3136594828352063660974229)
                ·
                  refine ⟨147027882579002984108167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3136594828352063660974229 147027882579002984108167)
                  ·
                    rfl

theorem cell22_1288511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 6].length) (baseStart_1288511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1288511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1288511 prefixEnd_1288511 := by exact prefixLift 1288511
  have htrace : WordTrace (prefixWord ++ tailWord_1288511) baseStart_1288511 baseEnd_1288511 := by
    simpa [prefixWord, tailWord_1288511, baseEnd_1288511] using wordTrace_append hprefix tailTrace_1288511
  have hstable : (prefixWord ++ tailWord_1288511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288511).length < 2 ^ (prefixWord ++ tailWord_1288511).sum := by decide
  have hdescent : baseEnd_1288511 < baseStart_1288511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288560 : List Nat := [2, 1, 1, 1, 4, 3, 3, 2, 2, 3]
def baseStart_1288560 : Nat := 118140960795 + 1288560 * 2 ^ 59
def prefixEnd_1288560 : Nat := 4983230072969 + 3 ^ 40 * 1288560 * 2
def baseEnd_1288560 : Nat := 441100421438389157849351

theorem tailTrace_1288560 : CollatzResearch.WordTrace tailWord_1288560 prefixEnd_1288560 441100421438389157849351 := by
  unfold tailWord_1288560
  simp only [CollatzResearch.WordTrace]
  refine ⟨23498822105887331686279567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31331762807849775581706089 23498822105887331686279567)
  ·
    refine ⟨35248233158830997529419351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23498822105887331686279567 35248233158830997529419351)
    ·
      refine ⟨52872349738246496294129027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35248233158830997529419351 52872349738246496294129027)
      ·
        refine ⟨79308524607369744441193541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52872349738246496294129027 79308524607369744441193541)
        ·
          refine ⟨14870348363881827082723789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79308524607369744441193541 14870348363881827082723789)
          ·
            refine ⟨5576380636455685156021421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14870348363881827082723789 5576380636455685156021421)
            ·
              refine ⟨2091142738670881933508033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5576380636455685156021421 2091142738670881933508033)
              ·
                refine ⟨1568357054003161450131025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2091142738670881933508033 1568357054003161450131025)
                ·
                  refine ⟨1176267790502371087598269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1568357054003161450131025 1176267790502371087598269)
                  ·
                    refine ⟨441100421438389157849351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1176267790502371087598269 441100421438389157849351)
                    ·
                      rfl

theorem cell22_1288560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 2, 3].length) (baseStart_1288560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1288560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1288560 prefixEnd_1288560 := by exact prefixLift 1288560
  have htrace : WordTrace (prefixWord ++ tailWord_1288560) baseStart_1288560 baseEnd_1288560 := by
    simpa [prefixWord, tailWord_1288560, baseEnd_1288560] using wordTrace_append hprefix tailTrace_1288560
  have hstable : (prefixWord ++ tailWord_1288560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288560).length < 2 ^ (prefixWord ++ tailWord_1288560).sum := by decide
  have hdescent : baseEnd_1288560 < baseStart_1288560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288590 : List Nat := [4, 1, 1, 4, 1, 1, 4, 6]
def baseStart_1288590 : Nat := 118140960795 + 1288590 * 2 ^ 59
def prefixEnd_1288590 : Nat := 4983230072969 + 3 ^ 40 * 1288590 * 2
def baseEnd_1288590 : Nat := 49012299005719897733251

theorem tailTrace_1288590 : CollatzResearch.WordTrace tailWord_1288590 prefixEnd_1288590 49012299005719897733251 := by
  unfold tailWord_1288590
  simp only [CollatzResearch.WordTrace]
  refine ⟨5874842300208247312018903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31332492267777318997434149 5874842300208247312018903)
  ·
    refine ⟨8812263450312370968028355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5874842300208247312018903 8812263450312370968028355)
    ·
      refine ⟨13218395175468556452042533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8812263450312370968028355 13218395175468556452042533)
      ·
        refine ⟨2478449095400354334757975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13218395175468556452042533 2478449095400354334757975)
        ·
          refine ⟨3717673643100531502136963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2478449095400354334757975 3717673643100531502136963)
          ·
            refine ⟨5576510464650797253205445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3717673643100531502136963 5576510464650797253205445)
            ·
              refine ⟨1045595712122024484976021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5576510464650797253205445 1045595712122024484976021)
              ·
                refine ⟨49012299005719897733251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1045595712122024484976021 49012299005719897733251)
                ·
                  rfl

theorem cell22_1288590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_1288590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1288590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1288590 prefixEnd_1288590 := by exact prefixLift 1288590
  have htrace : WordTrace (prefixWord ++ tailWord_1288590) baseStart_1288590 baseEnd_1288590 := by
    simpa [prefixWord, tailWord_1288590, baseEnd_1288590] using wordTrace_append hprefix tailTrace_1288590
  have hstable : (prefixWord ++ tailWord_1288590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288590).length < 2 ^ (prefixWord ++ tailWord_1288590).sum := by decide
  have hdescent : baseEnd_1288590 < baseStart_1288590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288601 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 9]
def baseStart_1288601 : Nat := 118140960795 + 1288601 * 2 ^ 59
def prefixEnd_1288601 : Nat := 4983230072969 + 3 ^ 40 * 1288601 * 2
def baseEnd_1288601 : Nat := 147038152192092905858075

theorem tailTrace_1288601 : CollatzResearch.WordTrace tailWord_1288601 prefixEnd_1288601 147038152192092905858075 := by
  unfold tailWord_1288601
  simp only [CollatzResearch.WordTrace]
  refine ⟨46999139604626127374801657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31332759736417418249867771 46999139604626127374801657)
  ·
    refine ⟨35249354703469595531101243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46999139604626127374801657 35249354703469595531101243)
    ·
      refine ⟨52874032055204393296651865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35249354703469595531101243 52874032055204393296651865)
      ·
        refine ⟨39655524041403294972488899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52874032055204393296651865 39655524041403294972488899)
        ·
          refine ⟨59483286062104942458733349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39655524041403294972488899 59483286062104942458733349)
          ·
            refine ⟨11153116136644676711012503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59483286062104942458733349 11153116136644676711012503)
            ·
              refine ⟨16729674204967015066518755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11153116136644676711012503 16729674204967015066518755)
              ·
                refine ⟨25094511307450522599778133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16729674204967015066518755 25094511307450522599778133)
                ·
                  refine ⟨147038152192092905858075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25094511307450522599778133 147038152192092905858075)
                  ·
                    rfl

theorem cell22_1288601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 9].length) (baseStart_1288601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1288601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1288601 prefixEnd_1288601 := by exact prefixLift 1288601
  have htrace : WordTrace (prefixWord ++ tailWord_1288601) baseStart_1288601 baseEnd_1288601 := by
    simpa [prefixWord, tailWord_1288601, baseEnd_1288601] using wordTrace_append hprefix tailTrace_1288601
  have hstable : (prefixWord ++ tailWord_1288601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288601).length < 2 ^ (prefixWord ++ tailWord_1288601).sum := by decide
  have hdescent : baseEnd_1288601 < baseStart_1288601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288628 : List Nat := [2, 5, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_1288628 : Nat := 118140960795 + 1288628 * 2 ^ 59
def prefixEnd_1288628 : Nat := 4983230072969 + 3 ^ 40 * 1288628 * 2
def baseEnd_1288628 : Nat := 441123699228059647149143

theorem tailTrace_1288628 : CollatzResearch.WordTrace tailWord_1288628 prefixEnd_1288628 441123699228059647149143 := by
  unfold tailWord_1288628
  simp only [CollatzResearch.WordTrace]
  refine ⟨23500062187764155493017269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31333416250352207324023025 23500062187764155493017269)
  ·
    refine ⟨2203130830102889577470369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23500062187764155493017269 2203130830102889577470369)
    ·
      refine ⟨1652348122577167183102777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2203130830102889577470369 1652348122577167183102777)
      ·
        refine ⟨1239261091932875387327083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1652348122577167183102777 1239261091932875387327083)
        ·
          refine ⟨1858891637899313080990625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1239261091932875387327083 1858891637899313080990625)
          ·
            refine ⟨1394168728424484810742969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1858891637899313080990625 1394168728424484810742969)
            ·
              refine ⟨1045626546318363608057227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1394168728424484810742969 1045626546318363608057227)
              ·
                refine ⟨1568439819477545412085841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1045626546318363608057227 1568439819477545412085841)
                ·
                  refine ⟨1176329864608159059064381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1568439819477545412085841 1176329864608159059064381)
                  ·
                    refine ⟨441123699228059647149143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1176329864608159059064381 441123699228059647149143)
                    ·
                      rfl

theorem cell22_1288628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_1288628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1288628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1288628 prefixEnd_1288628 := by exact prefixLift 1288628
  have htrace : WordTrace (prefixWord ++ tailWord_1288628) baseStart_1288628 baseEnd_1288628 := by
    simpa [prefixWord, tailWord_1288628, baseEnd_1288628] using wordTrace_append hprefix tailTrace_1288628
  have hstable : (prefixWord ++ tailWord_1288628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288628).length < 2 ^ (prefixWord ++ tailWord_1288628).sum := by decide
  have hdescent : baseEnd_1288628 < baseStart_1288628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288768 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 1, 7]
def baseStart_1288768 : Nat := 118140960795 + 1288768 * 2 ^ 59
def prefixEnd_1288768 : Nat := 4983230072969 + 3 ^ 40 * 1288768 * 2
def baseEnd_1288768 : Nat := 441171624089145948648713

theorem tailTrace_1288768 : CollatzResearch.WordTrace tailWord_1288768 prefixEnd_1288768 441171624089145948648713 := by
  unfold tailWord_1288768
  simp only [CollatzResearch.WordTrace]
  refine ⟨23502615297510557448065479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31336820396680743264087305 23502615297510557448065479)
  ·
    refine ⟨35253922946265836172098219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23502615297510557448065479 35253922946265836172098219)
    ·
      refine ⟨52880884419398754258147329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35253922946265836172098219 52880884419398754258147329)
      ·
        refine ⟨39660663314549065693610497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52880884419398754258147329 39660663314549065693610497)
        ·
          refine ⟨29745497485911799270207873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39660663314549065693610497 29745497485911799270207873)
          ·
            refine ⟨22309123114433849452655905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29745497485911799270207873 22309123114433849452655905)
            ·
              refine ⟨16731842335825387089491929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22309123114433849452655905 16731842335825387089491929)
              ·
                refine ⟨12548881751869040317118947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16731842335825387089491929 12548881751869040317118947)
                ·
                  refine ⟨18823322627803560475678421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12548881751869040317118947 18823322627803560475678421)
                  ·
                    refine ⟨441171624089145948648713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18823322627803560475678421 441171624089145948648713)
                    ·
                      rfl

theorem cell22_1288768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_1288768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1288768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1288768 prefixEnd_1288768 := by exact prefixLift 1288768
  have htrace : WordTrace (prefixWord ++ tailWord_1288768) baseStart_1288768 baseEnd_1288768 := by
    simpa [prefixWord, tailWord_1288768, baseEnd_1288768] using wordTrace_append hprefix tailTrace_1288768
  have hstable : (prefixWord ++ tailWord_1288768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288768).length < 2 ^ (prefixWord ++ tailWord_1288768).sum := by decide
  have hdescent : baseEnd_1288768 < baseStart_1288768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288862 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_1288862 : Nat := 118140960795 + 1288862 * 2 ^ 59
def prefixEnd_1288862 : Nat := 4983230072969 + 3 ^ 40 * 1288862 * 2
def baseEnd_1288862 : Nat := 441203802210161036798425

theorem tailTrace_1288862 : CollatzResearch.WordTrace tailWord_1288862 prefixEnd_1288862 441203802210161036798425 := by
  unfold tailWord_1288862
  simp only [CollatzResearch.WordTrace]
  refine ⟨5876082382085071118756605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31339106037787045966701893 5876082382085071118756605)
  ·
    refine ⟨2203530893281901669533727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5876082382085071118756605 2203530893281901669533727)
    ·
      refine ⟨3305296339922852504300591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2203530893281901669533727 3305296339922852504300591)
      ·
        refine ⟨4957944509884278756450887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3305296339922852504300591 4957944509884278756450887)
        ·
          refine ⟨7436916764826418134676331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4957944509884278756450887 7436916764826418134676331)
          ·
            refine ⟨11155375147239627202014497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7436916764826418134676331 11155375147239627202014497)
            ·
              refine ⟨8366531360429720401510873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11155375147239627202014497 8366531360429720401510873)
              ·
                refine ⟨6274898520322290301133155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8366531360429720401510873 6274898520322290301133155)
                ·
                  refine ⟨9412347780483435451699733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6274898520322290301133155 9412347780483435451699733)
                  ·
                    refine ⟨441203802210161036798425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9412347780483435451699733 441203802210161036798425)
                    ·
                      rfl

theorem cell22_1288862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_1288862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1288862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1288862 prefixEnd_1288862 := by exact prefixLift 1288862
  have htrace : WordTrace (prefixWord ++ tailWord_1288862) baseStart_1288862 baseEnd_1288862 := by
    simpa [prefixWord, tailWord_1288862, baseEnd_1288862] using wordTrace_append hprefix tailTrace_1288862
  have hstable : (prefixWord ++ tailWord_1288862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288862).length < 2 ^ (prefixWord ++ tailWord_1288862).sum := by decide
  have hdescent : baseEnd_1288862 < baseStart_1288862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288892 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 5, 3]
def baseStart_1288892 : Nat := 118140960795 + 1288892 * 2 ^ 59
def prefixEnd_1288892 : Nat := 4983230072969 + 3 ^ 40 * 1288892 * 2
def baseEnd_1288892 : Nat := 441214071823250958548333

theorem tailTrace_1288892 : CollatzResearch.WordTrace tailWord_1288892 prefixEnd_1288892 441214071823250958548333 := by
  unfold tailWord_1288892
  simp only [CollatzResearch.WordTrace]
  refine ⟨23504876623285942036822465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31339835497714589382429953 23504876623285942036822465)
  ·
    refine ⟨17628657467464456527616849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23504876623285942036822465 17628657467464456527616849)
    ·
      refine ⟨13221493100598342395712637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17628657467464456527616849 13221493100598342395712637)
      ·
        refine ⟨4958059912724378398392239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13221493100598342395712637 4958059912724378398392239)
        ·
          refine ⟨7437089869086567597588359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4958059912724378398392239 7437089869086567597588359)
          ·
            refine ⟨11155634803629851396382539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7437089869086567597588359 11155634803629851396382539)
            ·
              refine ⟨16733452205444777094573809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11155634803629851396382539 16733452205444777094573809)
              ·
                refine ⟨12550089154083582820930357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16733452205444777094573809 12550089154083582820930357)
                ·
                  refine ⟨1176570858195335889462221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12550089154083582820930357 1176570858195335889462221)
                  ·
                    refine ⟨441214071823250958548333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1176570858195335889462221 441214071823250958548333)
                    ·
                      rfl

theorem cell22_1288892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_1288892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1288892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1288892 prefixEnd_1288892 := by exact prefixLift 1288892
  have htrace : WordTrace (prefixWord ++ tailWord_1288892) baseStart_1288892 baseEnd_1288892 := by
    simpa [prefixWord, tailWord_1288892, baseEnd_1288892] using wordTrace_append hprefix tailTrace_1288892
  have hstable : (prefixWord ++ tailWord_1288892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288892).length < 2 ^ (prefixWord ++ tailWord_1288892).sum := by decide
  have hdescent : baseEnd_1288892 < baseStart_1288892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288952 : List Nat := [2, 1, 2, 1, 1, 2, 3, 5, 1, 4]
def baseStart_1288952 : Nat := 118140960795 + 1288952 * 2 ^ 59
def prefixEnd_1288952 : Nat := 4983230072969 + 3 ^ 40 * 1288952 * 2
def baseEnd_1288952 : Nat := 441234611049430802048149

theorem tailTrace_1288952 : CollatzResearch.WordTrace tailWord_1288952 prefixEnd_1288952 441234611049430802048149 := by
  unfold tailWord_1288952
  simp only [CollatzResearch.WordTrace]
  refine ⟨23505970813177257160414555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31341294417569676213886073 23505970813177257160414555)
  ·
    refine ⟨35258956219765885740621833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23505970813177257160414555 35258956219765885740621833)
    ·
      refine ⟨26444217164824414305466375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35258956219765885740621833 26444217164824414305466375)
      ·
        refine ⟨39666325747236621458199563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26444217164824414305466375 39666325747236621458199563)
        ·
          refine ⟨59499488620854932187299345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39666325747236621458199563 59499488620854932187299345)
          ·
            refine ⟨44624616465641199140474509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59499488620854932187299345 44624616465641199140474509)
            ·
              refine ⟨16734231174615449677677941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44624616465641199140474509 16734231174615449677677941)
              ·
                refine ⟨1568834172620198407282307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16734231174615449677677941 1568834172620198407282307)
                ·
                  refine ⟨2353251258930297610923461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1568834172620198407282307 2353251258930297610923461)
                  ·
                    refine ⟨441234611049430802048149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2353251258930297610923461 441234611049430802048149)
                    ·
                      rfl

theorem cell22_1288952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_1288952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1288952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1288952 prefixEnd_1288952 := by exact prefixLift 1288952
  have htrace : WordTrace (prefixWord ++ tailWord_1288952) baseStart_1288952 baseEnd_1288952 := by
    simpa [prefixWord, tailWord_1288952, baseEnd_1288952] using wordTrace_append hprefix tailTrace_1288952
  have hstable : (prefixWord ++ tailWord_1288952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288952).length < 2 ^ (prefixWord ++ tailWord_1288952).sum := by decide
  have hdescent : baseEnd_1288952 < baseStart_1288952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289012 : List Nat := [2, 5, 1, 1, 13]
def baseStart_1289012 : Nat := 118140960795 + 1289012 * 2 ^ 59
def prefixEnd_1289012 : Nat := 4983230072969 + 3 ^ 40 * 1289012 * 2
def baseEnd_1289012 : Nat := 1815864815949015002255

theorem tailTrace_1289012 : CollatzResearch.WordTrace tailWord_1289012 prefixEnd_1289012 1815864815949015002255 := by
  unfold tailWord_1289012
  simp only [CollatzResearch.WordTrace]
  refine ⟨23507065003068572284006645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31342753337424763045342193 23507065003068572284006645)
  ·
    refine ⟨2203787344037678651625623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23507065003068572284006645 2203787344037678651625623)
    ·
      refine ⟨3305681016056517977438435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2203787344037678651625623 3305681016056517977438435)
      ·
        refine ⟨4958521524084776966157653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3305681016056517977438435 4958521524084776966157653)
        ·
          refine ⟨1815864815949015002255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 4958521524084776966157653 1815864815949015002255)
          ·
            rfl

theorem cell22_1289012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 13].length) (baseStart_1289012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289012 prefixEnd_1289012 := by exact prefixLift 1289012
  have htrace : WordTrace (prefixWord ++ tailWord_1289012) baseStart_1289012 baseEnd_1289012 := by
    simpa [prefixWord, tailWord_1289012, baseEnd_1289012] using wordTrace_append hprefix tailTrace_1289012
  have hstable : (prefixWord ++ tailWord_1289012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289012).length < 2 ^ (prefixWord ++ tailWord_1289012).sum := by decide
  have hdescent : baseEnd_1289012 < baseStart_1289012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289018 : List Nat := [3, 1, 1, 1, 6, 2, 2, 2, 4]
def baseStart_1289018 : Nat := 118140960795 + 1289018 * 2 ^ 59
def prefixEnd_1289018 : Nat := 4983230072969 + 3 ^ 40 * 1289018 * 2
def baseEnd_1289018 : Nat := 147085734732742876632649

theorem tailTrace_1289018 : CollatzResearch.WordTrace tailWord_1289018 prefixEnd_1289018 147085734732742876632649 := by
  unfold tailWord_1289018
  simp only [CollatzResearch.WordTrace]
  refine ⟨11753587211028851898182927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31342899229410271728487805 11753587211028851898182927)
  ·
    refine ⟨17630380816543277847274391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11753587211028851898182927 17630380816543277847274391)
    ·
      refine ⟨26445571224814916770911587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17630380816543277847274391 26445571224814916770911587)
      ·
        refine ⟨39668356837222375156367381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26445571224814916770911587 39668356837222375156367381)
        ·
          refine ⟨1859454226744798835454721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39668356837222375156367381 1859454226744798835454721)
          ·
            refine ⟨1394590670058599126591041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1859454226744798835454721 1394590670058599126591041)
            ·
              refine ⟨1045943002543949344943281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1394590670058599126591041 1045943002543949344943281)
              ·
                refine ⟨784457251907962008707461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1045943002543949344943281 784457251907962008707461)
                ·
                  refine ⟨147085734732742876632649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 784457251907962008707461 147085734732742876632649)
                  ·
                    rfl

theorem cell22_1289018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 4].length) (baseStart_1289018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289018 prefixEnd_1289018 := by exact prefixLift 1289018
  have htrace : WordTrace (prefixWord ++ tailWord_1289018) baseStart_1289018 baseEnd_1289018 := by
    simpa [prefixWord, tailWord_1289018, baseEnd_1289018] using wordTrace_append hprefix tailTrace_1289018
  have hstable : (prefixWord ++ tailWord_1289018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289018).length < 2 ^ (prefixWord ++ tailWord_1289018).sum := by decide
  have hdescent : baseEnd_1289018 < baseStart_1289018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289042 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 2, 6]
def baseStart_1289042 : Nat := 118140960795 + 1289042 * 2 ^ 59
def prefixEnd_1289042 : Nat := 4983230072969 + 3 ^ 40 * 1289042 * 2
def baseEnd_1289042 : Nat := 441265419888700567297873

theorem tailTrace_1289042 : CollatzResearch.WordTrace tailWord_1289042 prefixEnd_1289042 441265419888700567297873 := by
  unfold tailWord_1289042
  simp only [CollatzResearch.WordTrace]
  refine ⟨11753806049007114922901345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31343482797352306461070253 11753806049007114922901345)
  ·
    refine ⟨8815354536755336192176009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11753806049007114922901345 8815354536755336192176009)
    ·
      refine ⟨6611515902566502144132007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8815354536755336192176009 6611515902566502144132007)
      ·
        refine ⟨9917273853849753216198011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6611515902566502144132007 9917273853849753216198011)
        ·
          refine ⟨14875910780774629824297017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9917273853849753216198011 14875910780774629824297017)
          ·
            refine ⟨11156933085580972368222763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14875910780774629824297017 11156933085580972368222763)
            ·
              refine ⟨16735399628371458552334145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11156933085580972368222763 16735399628371458552334145)
              ·
                refine ⟨12551549721278593914250609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16735399628371458552334145 12551549721278593914250609)
                ·
                  refine ⟨9413662290958945435687957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12551549721278593914250609 9413662290958945435687957)
                  ·
                    refine ⟨441265419888700567297873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9413662290958945435687957 441265419888700567297873)
                    ·
                      rfl

theorem cell22_1289042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_1289042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289042 prefixEnd_1289042 := by exact prefixLift 1289042
  have htrace : WordTrace (prefixWord ++ tailWord_1289042) baseStart_1289042 baseEnd_1289042 := by
    simpa [prefixWord, tailWord_1289042, baseEnd_1289042] using wordTrace_append hprefix tailTrace_1289042
  have hstable : (prefixWord ++ tailWord_1289042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289042).length < 2 ^ (prefixWord ++ tailWord_1289042).sum := by decide
  have hdescent : baseEnd_1289042 < baseStart_1289042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289061 : List Nat := [1, 3, 1, 3, 1, 1, 3, 5, 1, 3]
def baseStart_1289061 : Nat := 118140960795 + 1289061 * 2 ^ 59
def prefixEnd_1289061 : Nat := 4983230072969 + 3 ^ 40 * 1289061 * 2
def baseEnd_1289061 : Nat := 441271923976990851072815

theorem tailTrace_1289061 : CollatzResearch.WordTrace tailWord_1289061 prefixEnd_1289061 441271923976990851072815 := by
  unfold tailWord_1289061
  simp only [CollatzResearch.WordTrace]
  refine ⟨47015917182959625936547037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31343944788639750624364691 47015917182959625936547037)
  ·
    refine ⟨17630968943609859726205139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47015917182959625936547037 17630968943609859726205139)
    ·
      refine ⟨26446453415414789589307709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17630968943609859726205139 26446453415414789589307709)
      ·
        refine ⟨9917420030780546095990391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26446453415414789589307709 9917420030780546095990391)
        ·
          refine ⟨14876130046170819143985587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9917420030780546095990391 14876130046170819143985587)
          ·
            refine ⟨22314195069256228715978381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14876130046170819143985587 22314195069256228715978381)
            ·
              refine ⟨8367823150971085768491893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22314195069256228715978381 8367823150971085768491893)
              ·
                refine ⟨784483420403539290796115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8367823150971085768491893 784483420403539290796115)
                ·
                  refine ⟨1176725130605308936194173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 784483420403539290796115 1176725130605308936194173)
                  ·
                    refine ⟨441271923976990851072815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1176725130605308936194173 441271923976990851072815)
                    ·
                      rfl

theorem cell22_1289061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 1, 3].length) (baseStart_1289061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289061 prefixEnd_1289061 := by exact prefixLift 1289061
  have htrace : WordTrace (prefixWord ++ tailWord_1289061) baseStart_1289061 baseEnd_1289061 := by
    simpa [prefixWord, tailWord_1289061, baseEnd_1289061] using wordTrace_append hprefix tailTrace_1289061
  have hstable : (prefixWord ++ tailWord_1289061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289061).length < 2 ^ (prefixWord ++ tailWord_1289061).sum := by decide
  have hdescent : baseEnd_1289061 < baseStart_1289061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289072 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 2, 5]
def baseStart_1289072 : Nat := 118140960795 + 1289072 * 2 ^ 59
def prefixEnd_1289072 : Nat := 4983230072969 + 3 ^ 40 * 1289072 * 2
def baseEnd_1289072 : Nat := 441275689501790489047781

theorem tailTrace_1289072 : CollatzResearch.WordTrace tailWord_1289072 prefixEnd_1289072 441275689501790489047781 := by
  unfold tailWord_1289072
  simp only [CollatzResearch.WordTrace]
  refine ⟨23508159192959887407598735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31344212257279849876798313 23508159192959887407598735)
  ·
    refine ⟨35262238789439831111398103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23508159192959887407598735 35262238789439831111398103)
    ·
      refine ⟨52893358184159746667097155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35262238789439831111398103 52893358184159746667097155)
      ·
        refine ⟨79340037276239620000645733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52893358184159746667097155 79340037276239620000645733)
        ·
          refine ⟨14876256989294928750121075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79340037276239620000645733 14876256989294928750121075)
          ·
            refine ⟨22314385483942393125181613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14876256989294928750121075 22314385483942393125181613)
            ·
              refine ⟨8367894556478397421943105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22314385483942393125181613 8367894556478397421943105)
              ·
                refine ⟨6275920917358798066457329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8367894556478397421943105 6275920917358798066457329)
                ·
                  refine ⟨4706940688019098549842997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6275920917358798066457329 4706940688019098549842997)
                  ·
                    refine ⟨441275689501790489047781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4706940688019098549842997 441275689501790489047781)
                    ·
                      rfl

theorem cell22_1289072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_1289072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289072 prefixEnd_1289072 := by exact prefixLift 1289072
  have htrace : WordTrace (prefixWord ++ tailWord_1289072) baseStart_1289072 baseEnd_1289072 := by
    simpa [prefixWord, tailWord_1289072, baseEnd_1289072] using wordTrace_append hprefix tailTrace_1289072
  have hstable : (prefixWord ++ tailWord_1289072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289072).length < 2 ^ (prefixWord ++ tailWord_1289072).sum := by decide
  have hdescent : baseEnd_1289072 < baseStart_1289072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289074 : List Nat := [3, 2, 1, 2, 1, 1, 5, 2, 5]
def baseStart_1289074 : Nat := 118140960795 + 1289074 * 2 ^ 59
def prefixEnd_1289074 : Nat := 4983230072969 + 3 ^ 40 * 1289074 * 2
def baseEnd_1289074 : Nat := 147092124714221050165925

theorem tailTrace_1289074 : CollatzResearch.WordTrace tailWord_1289074 prefixEnd_1289074 147092124714221050165925 := by
  unfold tailWord_1289074
  simp only [CollatzResearch.WordTrace]
  refine ⟨11754097832978132289192569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31344260887941686104513517 11754097832978132289192569)
  ·
    refine ⟨8815573374733599216894427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11754097832978132289192569 8815573374733599216894427)
    ·
      refine ⟨13223360062100398825341641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8815573374733599216894427 13223360062100398825341641)
      ·
        refine ⟨9917520046575299119006231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13223360062100398825341641 9917520046575299119006231)
        ·
          refine ⟨14876280069862948678509347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9917520046575299119006231 14876280069862948678509347)
          ·
            refine ⟨22314420104794423017764021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14876280069862948678509347 22314420104794423017764021)
            ·
              refine ⟨2091976884824477157915377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22314420104794423017764021 2091976884824477157915377)
              ·
                refine ⟨1568982663618357868436533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2091976884824477157915377 1568982663618357868436533)
                ·
                  refine ⟨147092124714221050165925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1568982663618357868436533 147092124714221050165925)
                  ·
                    rfl

theorem cell22_1289074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_1289074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289074 prefixEnd_1289074 := by exact prefixLift 1289074
  have htrace : WordTrace (prefixWord ++ tailWord_1289074) baseStart_1289074 baseEnd_1289074 := by
    simpa [prefixWord, tailWord_1289074, baseEnd_1289074] using wordTrace_append hprefix tailTrace_1289074
  have hstable : (prefixWord ++ tailWord_1289074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289074).length < 2 ^ (prefixWord ++ tailWord_1289074).sum := by decide
  have hdescent : baseEnd_1289074 < baseStart_1289074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289078 : List Nat := [5, 1, 1, 3, 1, 2, 2, 1, 3, 3]
def baseStart_1289078 : Nat := 118140960795 + 1289078 * 2 ^ 59
def prefixEnd_1289078 : Nat := 4983230072969 + 3 ^ 40 * 1289078 * 2
def baseEnd_1289078 : Nat := 441277743424408473397763

theorem tailTrace_1289078 : CollatzResearch.WordTrace tailWord_1289078 prefixEnd_1289078 441277743424408473397763 := by
  unfold tailWord_1289078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2938533576493627364994743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31344358149265358559943925 2938533576493627364994743)
  ·
    refine ⟨4407800364740441047492115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2938533576493627364994743 4407800364740441047492115)
    ·
      refine ⟨6611700547110661571238173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4407800364740441047492115 6611700547110661571238173)
      ·
        refine ⟨2479387705166498089214315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6611700547110661571238173 2479387705166498089214315)
        ·
          refine ⟨3719081557749747133821473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2479387705166498089214315 3719081557749747133821473)
          ·
            refine ⟨2789311168312310350366105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3719081557749747133821473 2789311168312310350366105)
            ·
              refine ⟨2091983376234232762774579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2789311168312310350366105 2091983376234232762774579)
              ·
                refine ⟨3137975064351349144161869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2091983376234232762774579 3137975064351349144161869)
                ·
                  refine ⟨1176740649131755929060701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3137975064351349144161869 1176740649131755929060701)
                  ·
                    refine ⟨441277743424408473397763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1176740649131755929060701 441277743424408473397763)
                    ·
                      rfl

theorem cell22_1289078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_1289078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289078 prefixEnd_1289078 := by exact prefixLift 1289078
  have htrace : WordTrace (prefixWord ++ tailWord_1289078) baseStart_1289078 baseEnd_1289078 := by
    simpa [prefixWord, tailWord_1289078, baseEnd_1289078] using wordTrace_append hprefix tailTrace_1289078
  have hstable : (prefixWord ++ tailWord_1289078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289078).length < 2 ^ (prefixWord ++ tailWord_1289078).sum := by decide
  have hdescent : baseEnd_1289078 < baseStart_1289078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289087 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 5, 4]
def baseStart_1289087 : Nat := 118140960795 + 1289087 * 2 ^ 59
def prefixEnd_1289087 : Nat := 4983230072969 + 3 ^ 40 * 1289087 * 2
def baseEnd_1289087 : Nat := 441280824308335449922735

theorem tailTrace_1289087 : CollatzResearch.WordTrace tailWord_1289087 prefixEnd_1289087 441280824308335449922735 := by
  unfold tailWord_1289087
  simp only [CollatzResearch.WordTrace]
  refine ⟨47016865480865432376993515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31344576987243621584662343 47016865480865432376993515)
  ·
    refine ⟨70525298221298148565490273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47016865480865432376993515 70525298221298148565490273)
    ·
      refine ⟨52893973665973611424117705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70525298221298148565490273 52893973665973611424117705)
      ·
        refine ⟨39670480249480208568088279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52893973665973611424117705 39670480249480208568088279)
        ·
          refine ⟨59505720374220312852132419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39670480249480208568088279 59505720374220312852132419)
          ·
            refine ⟨89258580561330469278198629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59505720374220312852132419 89258580561330469278198629)
            ·
              refine ⟨16735983855249462989662243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89258580561330469278198629 16735983855249462989662243)
              ·
                refine ⟨25103975782874194484493365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16735983855249462989662243 25103975782874194484493365)
                ·
                  refine ⟨2353497729644455732921253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25103975782874194484493365 2353497729644455732921253)
                  ·
                    refine ⟨441280824308335449922735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2353497729644455732921253 441280824308335449922735)
                    ·
                      rfl

theorem cell22_1289087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 4].length) (baseStart_1289087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289087 prefixEnd_1289087 := by exact prefixLift 1289087
  have htrace : WordTrace (prefixWord ++ tailWord_1289087) baseStart_1289087 baseEnd_1289087 := by
    simpa [prefixWord, tailWord_1289087, baseEnd_1289087] using wordTrace_append hprefix tailTrace_1289087
  have hstable : (prefixWord ++ tailWord_1289087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289087).length < 2 ^ (prefixWord ++ tailWord_1289087).sum := by decide
  have hdescent : baseEnd_1289087 < baseStart_1289087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289121 : List Nat := [1, 2, 3, 4, 1, 1, 2, 3, 1, 4]
def baseStart_1289121 : Nat := 118140960795 + 1289121 * 2 ^ 59
def prefixEnd_1289121 : Nat := 4983230072969 + 3 ^ 40 * 1289121 * 2
def baseEnd_1289121 : Nat := 441292463203170694572631

theorem tailTrace_1289121 : CollatzResearch.WordTrace tailWord_1289121 prefixEnd_1289121 441292463203170694572631 := by
  unfold tailWord_1289121
  simp only [CollatzResearch.WordTrace]
  refine ⟨47018105562742256183731217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31345403708494837455820811 47018105562742256183731217)
  ·
    refine ⟨35263579172056692137798413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47018105562742256183731217 35263579172056692137798413)
    ·
      refine ⟨13223842189521259551674405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35263579172056692137798413 13223842189521259551674405)
      ·
        refine ⟨2479470410535236165938951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13223842189521259551674405 2479470410535236165938951)
        ·
          refine ⟨3719205615802854248908427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2479470410535236165938951 3719205615802854248908427)
          ·
            refine ⟨5578808423704281373362641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3719205615802854248908427 5578808423704281373362641)
            ·
              refine ⟨4184106317778211030021981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5578808423704281373362641 4184106317778211030021981)
              ·
                refine ⟨1569039869166829136258243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4184106317778211030021981 1569039869166829136258243)
                ·
                  refine ⟨2353559803750243704387365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1569039869166829136258243 2353559803750243704387365)
                  ·
                    refine ⟨441292463203170694572631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2353559803750243704387365 441292463203170694572631)
                    ·
                      rfl

theorem cell22_1289121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_1289121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289121 prefixEnd_1289121 := by exact prefixLift 1289121
  have htrace : WordTrace (prefixWord ++ tailWord_1289121) baseStart_1289121 baseEnd_1289121 := by
    simpa [prefixWord, tailWord_1289121, baseEnd_1289121] using wordTrace_append hprefix tailTrace_1289121
  have hstable : (prefixWord ++ tailWord_1289121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289121).length < 2 ^ (prefixWord ++ tailWord_1289121).sum := by decide
  have hdescent : baseEnd_1289121 < baseStart_1289121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289166 : List Nat := [4, 1, 1, 1, 2, 4, 2, 1, 2, 4]
def baseStart_1289166 : Nat := 118140960795 + 1289166 * 2 ^ 59
def prefixEnd_1289166 : Nat := 4983230072969 + 3 ^ 40 * 1289166 * 2
def baseEnd_1289166 : Nat := 441307867622805577197493

theorem tailTrace_1289166 : CollatzResearch.WordTrace tailWord_1289166 prefixEnd_1289166 441307867622805577197493 := by
  unfold tailWord_1289166
  simp only [CollatzResearch.WordTrace]
  refine ⟨5877468355947403608639919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31346497898386152579412901 5877468355947403608639919)
  ·
    refine ⟨8816202533921105412959879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5877468355947403608639919 8816202533921105412959879)
    ·
      refine ⟨13224303800881658119439819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8816202533921105412959879 13224303800881658119439819)
      ·
        refine ⟨19836455701322487179159729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13224303800881658119439819 19836455701322487179159729)
        ·
          refine ⟨14877341775991865384369797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19836455701322487179159729 14877341775991865384369797)
          ·
            refine ⟨2789501582998474759569337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14877341775991865384369797 2789501582998474759569337)
            ·
              refine ⟨2092126187248856069677003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2789501582998474759569337 2092126187248856069677003)
              ·
                refine ⟨3138189280873284104515505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2092126187248856069677003 3138189280873284104515505)
                ·
                  refine ⟨2353641960654963078386629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3138189280873284104515505 2353641960654963078386629)
                  ·
                    refine ⟨441307867622805577197493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2353641960654963078386629 441307867622805577197493)
                    ·
                      rfl

theorem cell22_1289166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_1289166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289166 prefixEnd_1289166 := by exact prefixLift 1289166
  have htrace : WordTrace (prefixWord ++ tailWord_1289166) baseStart_1289166 baseEnd_1289166 := by
    simpa [prefixWord, tailWord_1289166, baseEnd_1289166] using wordTrace_append hprefix tailTrace_1289166
  have hstable : (prefixWord ++ tailWord_1289166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289166).length < 2 ^ (prefixWord ++ tailWord_1289166).sum := by decide
  have hdescent : baseEnd_1289166 < baseStart_1289166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289194 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 2, 6]
def baseStart_1289194 : Nat := 118140960795 + 1289194 * 2 ^ 59
def prefixEnd_1289194 : Nat := 4983230072969 + 3 ^ 40 * 1289194 * 2
def baseEnd_1289194 : Nat := 441317452595022837497407

theorem tailTrace_1289194 : CollatzResearch.WordTrace tailWord_1289194 prefixEnd_1289194 441317452595022837497407 := by
  unfold tailWord_1289194
  simp only [CollatzResearch.WordTrace]
  refine ⟨11755192022869447412784659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31347178727651859767425757 11755192022869447412784659)
  ·
    refine ⟨17632788034304171119176989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11755192022869447412784659 17632788034304171119176989)
    ·
      refine ⟨6612295512864064169691371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17632788034304171119176989 6612295512864064169691371)
      ·
        refine ⟨9918443269296096254537057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6612295512864064169691371 9918443269296096254537057)
        ·
          refine ⟨7438832451972072190902793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9918443269296096254537057 7438832451972072190902793)
          ·
            refine ⟨5579124338979054143177095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7438832451972072190902793 5579124338979054143177095)
            ·
              refine ⟨8368686508468581214765643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5579124338979054143177095 8368686508468581214765643)
              ·
                refine ⟨12553029762702871822148465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8368686508468581214765643 12553029762702871822148465)
                ·
                  refine ⟨9414772322027153866611349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12553029762702871822148465 9414772322027153866611349)
                  ·
                    refine ⟨441317452595022837497407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9414772322027153866611349 441317452595022837497407)
                    ·
                      rfl

theorem cell22_1289194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_1289194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289194 prefixEnd_1289194 := by exact prefixLift 1289194
  have htrace : WordTrace (prefixWord ++ tailWord_1289194) baseStart_1289194 baseEnd_1289194 := by
    simpa [prefixWord, tailWord_1289194, baseEnd_1289194] using wordTrace_append hprefix tailTrace_1289194
  have hstable : (prefixWord ++ tailWord_1289194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289194).length < 2 ^ (prefixWord ++ tailWord_1289194).sum := by decide
  have hdescent : baseEnd_1289194 < baseStart_1289194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289198 : List Nat := [4, 1, 2, 1, 5, 1, 1, 7]
def baseStart_1289198 : Nat := 118140960795 + 1289198 * 2 ^ 59
def prefixEnd_1289198 : Nat := 4983230072969 + 3 ^ 40 * 1289198 * 2
def baseEnd_1289198 : Nat := 49035424652974240044155

theorem tailTrace_1289198 : CollatzResearch.WordTrace tailWord_1289198 prefixEnd_1289198 49035424652974240044155 := by
  unfold tailWord_1289198
  simp only [CollatzResearch.WordTrace]
  refine ⟨5877614247932912291785531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31347275988975532222856165 5877614247932912291785531)
  ·
    refine ⟨8816421371899368437678297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5877614247932912291785531 8816421371899368437678297)
    ·
      refine ⟨6612316028924526328258723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8816421371899368437678297 6612316028924526328258723)
      ·
        refine ⟨9918474043386789492388085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6612316028924526328258723 9918474043386789492388085)
        ·
          refine ⟨929856941567511514911383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9918474043386789492388085 929856941567511514911383)
          ·
            refine ⟨1394785412351267272367075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929856941567511514911383 1394785412351267272367075)
            ·
              refine ⟨2092178118526900908550613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1394785412351267272367075 2092178118526900908550613)
              ·
                refine ⟨49035424652974240044155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2092178118526900908550613 49035424652974240044155)
                ·
                  rfl

theorem cell22_1289198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_1289198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289198 prefixEnd_1289198 := by exact prefixLift 1289198
  have htrace : WordTrace (prefixWord ++ tailWord_1289198) baseStart_1289198 baseEnd_1289198 := by
    simpa [prefixWord, tailWord_1289198, baseEnd_1289198] using wordTrace_append hprefix tailTrace_1289198
  have hstable : (prefixWord ++ tailWord_1289198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289198).length < 2 ^ (prefixWord ++ tailWord_1289198).sum := by decide
  have hdescent : baseEnd_1289198 < baseStart_1289198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289209 : List Nat := [1, 2, 1, 3, 1, 3, 1, 5, 5]
def baseStart_1289209 : Nat := 118140960795 + 1289209 * 2 ^ 59
def prefixEnd_1289209 : Nat := 4983230072969 + 3 ^ 40 * 1289209 * 2
def baseEnd_1289209 : Nat := 147107529133855932790787

theorem tailTrace_1289209 : CollatzResearch.WordTrace tailWord_1289209 prefixEnd_1289209 147107529133855932790787 := by
  unfold tailWord_1289209
  simp only [CollatzResearch.WordTrace]
  refine ⟨47021315186423447212934681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31347543457615631475289787 47021315186423447212934681)
  ·
    refine ⟨35265986389817585409701011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47021315186423447212934681 35265986389817585409701011)
    ·
      refine ⟨52898979584726378114551517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35265986389817585409701011 52898979584726378114551517)
      ·
        refine ⟨19837117344272391792956819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52898979584726378114551517 19837117344272391792956819)
        ·
          refine ⟨29755676016408587689435229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19837117344272391792956819 29755676016408587689435229)
          ·
            refine ⟨11158378506153220383538211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29755676016408587689435229 11158378506153220383538211)
            ·
              refine ⟨16737567759229830575307317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11158378506153220383538211 16737567759229830575307317)
              ·
                refine ⟨1569146977427796616435061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16737567759229830575307317 1569146977427796616435061)
                ·
                  refine ⟨147107529133855932790787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1569146977427796616435061 147107529133855932790787)
                  ·
                    rfl

theorem cell22_1289209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 5].length) (baseStart_1289209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289209 prefixEnd_1289209 := by exact prefixLift 1289209
  have htrace : WordTrace (prefixWord ++ tailWord_1289209) baseStart_1289209 baseEnd_1289209 := by
    simpa [prefixWord, tailWord_1289209, baseEnd_1289209] using wordTrace_append hprefix tailTrace_1289209
  have hstable : (prefixWord ++ tailWord_1289209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289209).length < 2 ^ (prefixWord ++ tailWord_1289209).sum := by decide
  have hdescent : baseEnd_1289209 < baseStart_1289209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289230 : List Nat := [4, 1, 1, 2, 2, 3, 2, 3, 1, 3]
def baseStart_1289230 : Nat := 118140960795 + 1289230 * 2 ^ 59
def prefixEnd_1289230 : Nat := 4983230072969 + 3 ^ 40 * 1289230 * 2
def baseEnd_1289230 : Nat := 441329776130730743597297

theorem tailTrace_1289230 : CollatzResearch.WordTrace tailWord_1289230 prefixEnd_1289230 441329776130730743597297 := by
  unfold tailWord_1289230
  simp only [CollatzResearch.WordTrace]
  refine ⟨5877760139918420974931143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31348054079564911866299429 5877760139918420974931143)
  ·
    refine ⟨8816640209877631462396715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5877760139918420974931143 8816640209877631462396715)
    ·
      refine ⟨13224960314816447193595073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8816640209877631462396715 13224960314816447193595073)
      ·
        refine ⟨9918720236112335395196305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13224960314816447193595073 9918720236112335395196305)
        ·
          refine ⟨7439040177084251546397229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9918720236112335395196305 7439040177084251546397229)
          ·
            refine ⟨2789640066406594329898961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7439040177084251546397229 2789640066406594329898961)
            ·
              refine ⟨2092230049804945747424221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2789640066406594329898961 2092230049804945747424221)
              ·
                refine ⟨784586268676854655284083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2092230049804945747424221 784586268676854655284083)
                ·
                  refine ⟨1176879403015281982926125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 784586268676854655284083 1176879403015281982926125)
                  ·
                    refine ⟨441329776130730743597297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1176879403015281982926125 441329776130730743597297)
                    ·
                      rfl

theorem cell22_1289230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_1289230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289230 prefixEnd_1289230 := by exact prefixLift 1289230
  have htrace : WordTrace (prefixWord ++ tailWord_1289230) baseStart_1289230 baseEnd_1289230 := by
    simpa [prefixWord, tailWord_1289230, baseEnd_1289230] using wordTrace_append hprefix tailTrace_1289230
  have hstable : (prefixWord ++ tailWord_1289230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289230).length < 2 ^ (prefixWord ++ tailWord_1289230).sum := by decide
  have hdescent : baseEnd_1289230 < baseStart_1289230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289273 : List Nat := [1, 2, 1, 5, 2, 2, 2, 2, 1, 4]
def baseStart_1289273 : Nat := 118140960795 + 1289273 * 2 ^ 59
def prefixEnd_1289273 : Nat := 4983230072969 + 3 ^ 40 * 1289273 * 2
def baseEnd_1289273 : Nat := 441344495909492964772165

theorem tailTrace_1289273 : CollatzResearch.WordTrace tailWord_1289273 prefixEnd_1289273 441344495909492964772165 := by
  unfold tailWord_1289273
  simp only [CollatzResearch.WordTrace]
  refine ⟨47023649458191586143264473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31349099638794390762176315 47023649458191586143264473)
  ·
    refine ⟨35267737093643689607448355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47023649458191586143264473 35267737093643689607448355)
    ·
      refine ⟨52901605640465534411172533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35267737093643689607448355 52901605640465534411172533)
      ·
        refine ⟨4959525528793643851047425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52901605640465534411172533 4959525528793643851047425)
        ·
          refine ⟨3719644146595232888285569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4959525528793643851047425 3719644146595232888285569)
          ·
            refine ⟨2789733109946424666214177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3719644146595232888285569 2789733109946424666214177)
            ·
              refine ⟨2092299832459818499660633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2789733109946424666214177 2092299832459818499660633)
              ·
                refine ⟨1569224874344863874745475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2092299832459818499660633 1569224874344863874745475)
                ·
                  refine ⟨2353837311517295812118213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1569224874344863874745475 2353837311517295812118213)
                  ·
                    refine ⟨441344495909492964772165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2353837311517295812118213 441344495909492964772165)
                    ·
                      rfl

theorem cell22_1289273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 4].length) (baseStart_1289273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289273 prefixEnd_1289273 := by exact prefixLift 1289273
  have htrace : WordTrace (prefixWord ++ tailWord_1289273) baseStart_1289273 baseEnd_1289273 := by
    simpa [prefixWord, tailWord_1289273, baseEnd_1289273] using wordTrace_append hprefix tailTrace_1289273
  have hstable : (prefixWord ++ tailWord_1289273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289273).length < 2 ^ (prefixWord ++ tailWord_1289273).sum := by decide
  have hdescent : baseEnd_1289273 < baseStart_1289273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289301 : List Nat := [1, 3, 2, 2, 1, 2, 3, 2, 2, 4]
def baseStart_1289301 : Nat := 118140960795 + 1289301 * 2 ^ 59
def prefixEnd_1289301 : Nat := 4983230072969 + 3 ^ 40 * 1289301 * 2
def baseEnd_1289301 : Nat := 441354080881710225072079

theorem tailTrace_1289301 : CollatzResearch.WordTrace tailWord_1289301 prefixEnd_1289301 441354080881710225072079 := by
  unfold tailWord_1289301
  simp only [CollatzResearch.WordTrace]
  refine ⟨47024670702090146925283757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31349780468060097950189171 47024670702090146925283757)
  ·
    refine ⟨17634251513283805096981409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47024670702090146925283757 17634251513283805096981409)
    ·
      refine ⟨13225688634962853822736057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17634251513283805096981409 13225688634962853822736057)
      ·
        refine ⟨9919266476222140367052043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13225688634962853822736057 9919266476222140367052043)
        ·
          refine ⟨14878899714333210550578065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9919266476222140367052043 14878899714333210550578065)
          ·
            refine ⟨11159174785749907912933549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14878899714333210550578065 11159174785749907912933549)
            ·
              refine ⟨4184690544656215467350081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11159174785749907912933549 4184690544656215467350081)
              ·
                refine ⟨3138517908492161600512561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4184690544656215467350081 3138517908492161600512561)
                ·
                  refine ⟨2353888431369121200384421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3138517908492161600512561 2353888431369121200384421)
                  ·
                    refine ⟨441354080881710225072079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2353888431369121200384421 441354080881710225072079)
                    ·
                      rfl

theorem cell22_1289301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_1289301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289301 prefixEnd_1289301 := by exact prefixLift 1289301
  have htrace : WordTrace (prefixWord ++ tailWord_1289301) baseStart_1289301 baseEnd_1289301 := by
    simpa [prefixWord, tailWord_1289301, baseEnd_1289301] using wordTrace_append hprefix tailTrace_1289301
  have hstable : (prefixWord ++ tailWord_1289301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289301).length < 2 ^ (prefixWord ++ tailWord_1289301).sum := by decide
  have hdescent : baseEnd_1289301 < baseStart_1289301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289329 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 4, 6]
def baseStart_1289329 : Nat := 118140960795 + 1289329 * 2 ^ 59
def prefixEnd_1289329 : Nat := 4983230072969 + 3 ^ 40 * 1289329 * 2
def baseEnd_1289329 : Nat := 441363665853927485371993

theorem tailTrace_1289329 : CollatzResearch.WordTrace tailWord_1289329 prefixEnd_1289329 441363665853927485371993 := by
  unfold tailWord_1289329
  simp only [CollatzResearch.WordTrace]
  refine ⟨47025691945988707707303041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31350461297325805138202027 47025691945988707707303041)
  ·
    refine ⟨35269268959491530780477281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47025691945988707707303041 35269268959491530780477281)
    ·
      refine ⟨26451951719618648085357961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35269268959491530780477281 26451951719618648085357961)
      ·
        refine ⟨19838963789713986064018471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26451951719618648085357961 19838963789713986064018471)
        ·
          refine ⟨29758445684570979096027707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19838963789713986064018471 29758445684570979096027707)
          ·
            refine ⟨44637668526856468644041561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29758445684570979096027707 44637668526856468644041561)
            ·
              refine ⟨33478251395142351483031171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44637668526856468644041561 33478251395142351483031171)
              ·
                refine ⟨50217377092713527224546757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33478251395142351483031171 50217377092713527224546757)
                ·
                  refine ⟨9415758204883786354602517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50217377092713527224546757 9415758204883786354602517)
                  ·
                    refine ⟨441363665853927485371993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9415758204883786354602517 441363665853927485371993)
                    ·
                      rfl

theorem cell22_1289329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_1289329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289329 prefixEnd_1289329 := by exact prefixLift 1289329
  have htrace : WordTrace (prefixWord ++ tailWord_1289329) baseStart_1289329 baseEnd_1289329 := by
    simpa [prefixWord, tailWord_1289329, baseEnd_1289329] using wordTrace_append hprefix tailTrace_1289329
  have hstable : (prefixWord ++ tailWord_1289329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289329).length < 2 ^ (prefixWord ++ tailWord_1289329).sum := by decide
  have hdescent : baseEnd_1289329 < baseStart_1289329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289344 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 9]
def baseStart_1289344 : Nat := 118140960795 + 1289344 * 2 ^ 59
def prefixEnd_1289344 : Nat := 4983230072969 + 3 ^ 40 * 1289344 * 2
def baseEnd_1289344 : Nat := 147122933553490815415649

theorem tailTrace_1289344 : CollatzResearch.WordTrace tailWord_1289344 prefixEnd_1289344 147122933553490815415649 := by
  unfold tailWord_1289344
  simp only [CollatzResearch.WordTrace]
  refine ⟨23513119520467182634549543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31350826027289576846066057 23513119520467182634549543)
  ·
    refine ⟨35269679280700773951824315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23513119520467182634549543 35269679280700773951824315)
    ·
      refine ⟨52904518921051160927736473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35269679280700773951824315 52904518921051160927736473)
      ·
        refine ⟨39678389190788370695802355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52904518921051160927736473 39678389190788370695802355)
        ·
          refine ⟨59517583786182556043703533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39678389190788370695802355 59517583786182556043703533)
          ·
            refine ⟨22319093919818458516388825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59517583786182556043703533 22319093919818458516388825)
            ·
              refine ⟨16739320439863843887291619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22319093919818458516388825 16739320439863843887291619)
              ·
                refine ⟨25108980659795765830937429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16739320439863843887291619 25108980659795765830937429)
                ·
                  refine ⟨147122933553490815415649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25108980659795765830937429 147122933553490815415649)
                  ·
                    rfl

theorem cell22_1289344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 9].length) (baseStart_1289344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289344 prefixEnd_1289344 := by exact prefixLift 1289344
  have htrace : WordTrace (prefixWord ++ tailWord_1289344) baseStart_1289344 baseEnd_1289344 := by
    simpa [prefixWord, tailWord_1289344, baseEnd_1289344] using wordTrace_append hprefix tailTrace_1289344
  have hstable : (prefixWord ++ tailWord_1289344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289344).length < 2 ^ (prefixWord ++ tailWord_1289344).sum := by decide
  have hdescent : baseEnd_1289344 < baseStart_1289344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289376 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 2, 5]
def baseStart_1289376 : Nat := 118140960795 + 1289376 * 2 ^ 59
def prefixEnd_1289376 : Nat := 4983230072969 + 3 ^ 40 * 1289376 * 2
def baseEnd_1289376 : Nat := 441379754914435029446849

theorem tailTrace_1289376 : CollatzResearch.WordTrace tailWord_1289376 prefixEnd_1289376 441379754914435029446849 := by
  unfold tailWord_1289376
  simp only [CollatzResearch.WordTrace]
  refine ⟨23513703088409217367131991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31351604117878956489509321 23513703088409217367131991)
  ·
    refine ⟨35270554632613826050697987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23513703088409217367131991 35270554632613826050697987)
    ·
      refine ⟨52905831948920739076046981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35270554632613826050697987 52905831948920739076046981)
      ·
        refine ⟨9919843490422638576758809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52905831948920739076046981 9919843490422638576758809)
        ·
          refine ⟨7439882617816978932569107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9919843490422638576758809 7439882617816978932569107)
          ·
            refine ⟨11159823926725468398853661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7439882617816978932569107 11159823926725468398853661)
            ·
              refine ⟨4184933972522050649570123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11159823926725468398853661 4184933972522050649570123)
              ·
                refine ⟨6277400958783075974355185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4184933972522050649570123 6277400958783075974355185)
                ·
                  refine ⟨4708050719087306980766389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6277400958783075974355185 4708050719087306980766389)
                  ·
                    refine ⟨441379754914435029446849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4708050719087306980766389 441379754914435029446849)
                    ·
                      rfl

theorem cell22_1289376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 2, 5].length) (baseStart_1289376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289376 prefixEnd_1289376 := by exact prefixLift 1289376
  have htrace : WordTrace (prefixWord ++ tailWord_1289376) baseStart_1289376 baseEnd_1289376 := by
    simpa [prefixWord, tailWord_1289376, baseEnd_1289376] using wordTrace_append hprefix tailTrace_1289376
  have hstable : (prefixWord ++ tailWord_1289376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289376).length < 2 ^ (prefixWord ++ tailWord_1289376).sum := by decide
  have hdescent : baseEnd_1289376 < baseStart_1289376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289391 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 3, 4]
def baseStart_1289391 : Nat := 118140960795 + 1289391 * 2 ^ 59
def prefixEnd_1289391 : Nat := 4983230072969 + 3 ^ 40 * 1289391 * 2
def baseEnd_1289391 : Nat := 441384889720979990321803

theorem tailTrace_1289391 : CollatzResearch.WordTrace tailWord_1289391 prefixEnd_1289391 441384889720979990321803 := by
  unfold tailWord_1289391
  simp only [CollatzResearch.WordTrace]
  refine ⟨47027953271764092296060027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31351968847842728197373351 47027953271764092296060027)
  ·
    refine ⟨70541929907646138444090041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47027953271764092296060027 70541929907646138444090041)
    ·
      refine ⟨52906447430734603833067531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70541929907646138444090041 52906447430734603833067531)
      ·
        refine ⟨79359671146101905749601297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52906447430734603833067531 79359671146101905749601297)
        ·
          refine ⟨59519753359576429312200973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79359671146101905749601297 59519753359576429312200973)
          ·
            refine ⟨22319907509841160992075365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59519753359576429312200973 22319907509841160992075365)
            ·
              refine ⟨4184982658095217686014131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22319907509841160992075365 4184982658095217686014131)
              ·
                refine ⟨6277473987142826529021197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4184982658095217686014131 6277473987142826529021197)
                ·
                  refine ⟨2354052745178559948382949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6277473987142826529021197 2354052745178559948382949)
                  ·
                    refine ⟨441384889720979990321803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2354052745178559948382949 441384889720979990321803)
                    ·
                      rfl

theorem cell22_1289391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 4].length) (baseStart_1289391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289391 prefixEnd_1289391 := by exact prefixLift 1289391
  have htrace : WordTrace (prefixWord ++ tailWord_1289391) baseStart_1289391 baseEnd_1289391 := by
    simpa [prefixWord, tailWord_1289391, baseEnd_1289391] using wordTrace_append hprefix tailTrace_1289391
  have hstable : (prefixWord ++ tailWord_1289391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289391).length < 2 ^ (prefixWord ++ tailWord_1289391).sum := by decide
  have hdescent : baseEnd_1289391 < baseStart_1289391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289412 : List Nat := [2, 3, 3, 1, 4, 1, 1, 2, 5]
def baseStart_1289412 : Nat := 118140960795 + 1289412 * 2 ^ 59
def prefixEnd_1289412 : Nat := 4983230072969 + 3 ^ 40 * 1289412 * 2
def baseEnd_1289412 : Nat := 147130692816714311848913

theorem tailTrace_1289412 : CollatzResearch.WordTrace tailWord_1289412 prefixEnd_1289412 147130692816714311848913 := by
  unfold tailWord_1289412
  simp only [CollatzResearch.WordTrace]
  refine ⟨23514359602344006441287245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31352479469792008588382993 23514359602344006441287245)
  ·
    refine ⟨8817884850879002415482717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23514359602344006441287245 8817884850879002415482717)
    ·
      refine ⟨3306706819079625905806019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8817884850879002415482717 3306706819079625905806019)
      ·
        refine ⟨4960060228619438858709029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3306706819079625905806019 4960060228619438858709029)
        ·
          refine ⟨930011292866144786007943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4960060228619438858709029 930011292866144786007943)
          ·
            refine ⟨1395016939299217179011915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930011292866144786007943 1395016939299217179011915)
            ·
              refine ⟨2092525408948825768517873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1395016939299217179011915 2092525408948825768517873)
              ·
                refine ⟨1569394056711619326388405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2092525408948825768517873 1569394056711619326388405)
                ·
                  refine ⟨147130692816714311848913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1569394056711619326388405 147130692816714311848913)
                  ·
                    rfl

theorem cell22_1289412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_1289412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289412 prefixEnd_1289412 := by exact prefixLift 1289412
  have htrace : WordTrace (prefixWord ++ tailWord_1289412) baseStart_1289412 baseEnd_1289412 := by
    simpa [prefixWord, tailWord_1289412, baseEnd_1289412] using wordTrace_append hprefix tailTrace_1289412
  have hstable : (prefixWord ++ tailWord_1289412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289412).length < 2 ^ (prefixWord ++ tailWord_1289412).sum := by decide
  have hdescent : baseEnd_1289412 < baseStart_1289412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289451 : List Nat := [1, 1, 1, 1, 2, 7, 1, 8]
def baseStart_1289451 : Nat := 118140960795 + 1289451 * 2 ^ 59
def prefixEnd_1289451 : Nat := 4983230072969 + 3 ^ 40 * 1289451 * 2
def baseEnd_1289451 : Nat := 49045047660795537091291

theorem tailTrace_1289451 : CollatzResearch.WordTrace tailWord_1289451 prefixEnd_1289451 49045047660795537091291 := by
  unfold tailWord_1289451
  simp only [CollatzResearch.WordTrace]
  refine ⟨47030141651546722543244207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31353427767697815028829471 47030141651546722543244207)
  ·
    refine ⟨70545212477320083814866311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47030141651546722543244207 70545212477320083814866311)
    ·
      refine ⟨105817818715980125722299467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70545212477320083814866311 105817818715980125722299467)
      ·
        refine ⟨158726728073970188583449201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105817818715980125722299467 158726728073970188583449201)
        ·
          refine ⟨119045046055477641437586901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158726728073970188583449201 119045046055477641437586901)
          ·
            refine ⟨2790118266925257221193443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 119045046055477641437586901 2790118266925257221193443)
            ·
              refine ⟨4185177400387885831790165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2790118266925257221193443 4185177400387885831790165)
              ·
                refine ⟨49045047660795537091291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4185177400387885831790165 49045047660795537091291)
                ·
                  rfl

theorem cell22_1289451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 8].length) (baseStart_1289451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289451 prefixEnd_1289451 := by exact prefixLift 1289451
  have htrace : WordTrace (prefixWord ++ tailWord_1289451) baseStart_1289451 baseEnd_1289451 := by
    simpa [prefixWord, tailWord_1289451, baseEnd_1289451] using wordTrace_append hprefix tailTrace_1289451
  have hstable : (prefixWord ++ tailWord_1289451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289451).length < 2 ^ (prefixWord ++ tailWord_1289451).sum := by decide
  have hdescent : baseEnd_1289451 < baseStart_1289451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289453 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_1289453 : Nat := 118140960795 + 1289453 * 2 ^ 59
def prefixEnd_1289453 : Nat := 4983230072969 + 3 ^ 40 * 1289453 * 2
def baseEnd_1289453 : Nat := 441406113588032495271613

theorem tailTrace_1289453 : CollatzResearch.WordTrace tailWord_1289453 prefixEnd_1289453 441406113588032495271613 := by
  unfold tailWord_1289453
  simp only [CollatzResearch.WordTrace]
  refine ⟨47030214597539476884817013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31353476398359651256544675 47030214597539476884817013)
  ·
    refine ⟨4409082618519325957951595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47030214597539476884817013 4409082618519325957951595)
    ·
      refine ⟨6613623927778988936927393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4409082618519325957951595 6613623927778988936927393)
      ·
        refine ⟨4960217945834241702695545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6613623927778988936927393 4960217945834241702695545)
        ·
          refine ⟨3720163459375681277021659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4960217945834241702695545 3720163459375681277021659)
          ·
            refine ⟨5580245189063521915532489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3720163459375681277021659 5580245189063521915532489)
            ·
              refine ⟨4185183891797641436649367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5580245189063521915532489 4185183891797641436649367)
              ·
                refine ⟨6277775837696462154974051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4185183891797641436649367 6277775837696462154974051)
                ·
                  refine ⟨9416663756544693232461077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6277775837696462154974051 9416663756544693232461077)
                  ·
                    refine ⟨441406113588032495271613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9416663756544693232461077 441406113588032495271613)
                    ·
                      rfl

theorem cell22_1289453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_1289453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289453 prefixEnd_1289453 := by exact prefixLift 1289453
  have htrace : WordTrace (prefixWord ++ tailWord_1289453) baseStart_1289453 baseEnd_1289453 := by
    simpa [prefixWord, tailWord_1289453, baseEnd_1289453] using wordTrace_append hprefix tailTrace_1289453
  have hstable : (prefixWord ++ tailWord_1289453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289453).length < 2 ^ (prefixWord ++ tailWord_1289453).sum := by decide
  have hdescent : baseEnd_1289453 < baseStart_1289453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289468 : List Nat := [2, 2, 2, 1, 5, 2, 8]
def baseStart_1289468 : Nat := 118140960795 + 1289468 * 2 ^ 59
def prefixEnd_1289468 : Nat := 4983230072969 + 3 ^ 40 * 1289468 * 2
def baseEnd_1289468 : Nat := 16348564755354720598021

theorem tailTrace_1289468 : CollatzResearch.WordTrace tailWord_1289468 prefixEnd_1289468 16348564755354720598021 := by
  unfold tailWord_1289468
  simp only [CollatzResearch.WordTrace]
  refine ⟨23515380846242567223306529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31353841128323422964408705 23515380846242567223306529)
  ·
    refine ⟨17636535634681925417479897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23515380846242567223306529 17636535634681925417479897)
    ·
      refine ⟨13227401726011444063109923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17636535634681925417479897 13227401726011444063109923)
      ·
        refine ⟨19841102589017166094664885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13227401726011444063109923 19841102589017166094664885)
        ·
          refine ⟨1860103367720359321374833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19841102589017166094664885 1860103367720359321374833)
          ·
            refine ⟨1395077525790269491031125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1860103367720359321374833 1395077525790269491031125)
            ·
              refine ⟨16348564755354720598021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1395077525790269491031125 16348564755354720598021)
              ·
                rfl

theorem cell22_1289468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 8].length) (baseStart_1289468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289468 prefixEnd_1289468 := by exact prefixLift 1289468
  have htrace : WordTrace (prefixWord ++ tailWord_1289468) baseStart_1289468 baseEnd_1289468 := by
    simpa [prefixWord, tailWord_1289468, baseEnd_1289468] using wordTrace_append hprefix tailTrace_1289468
  have hstable : (prefixWord ++ tailWord_1289468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289468).length < 2 ^ (prefixWord ++ tailWord_1289468).sum := by decide
  have hdescent : baseEnd_1289468 < baseStart_1289468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289470 : List Nat := [4, 2, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_1289470 : Nat := 118140960795 + 1289470 * 2 ^ 59
def prefixEnd_1289470 : Nat := 4983230072969 + 3 ^ 40 * 1289470 * 2
def baseEnd_1289470 : Nat := 441411933035450117596561

theorem tailTrace_1289470 : CollatzResearch.WordTrace tailWord_1289470 prefixEnd_1289470 441411933035450117596561 := by
  unfold tailWord_1289470
  simp only [CollatzResearch.WordTrace]
  refine ⟨5878854329809736098523233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31353889758985259192123909 5878854329809736098523233)
  ·
    refine ⟨4409140747357302073892425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5878854329809736098523233 4409140747357302073892425)
    ·
      refine ⟨3306855560517976555419319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4409140747357302073892425 3306855560517976555419319)
      ·
        refine ⟨4960283340776964833128979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3306855560517976555419319 4960283340776964833128979)
        ·
          refine ⟨7440425011165447249693469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4960283340776964833128979 7440425011165447249693469)
          ·
            refine ⟨2790159379187042718635051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7440425011165447249693469 2790159379187042718635051)
            ·
              refine ⟨4185239068780564077952577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2790159379187042718635051 4185239068780564077952577)
              ·
                refine ⟨3138929301585423058464433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4185239068780564077952577 3138929301585423058464433)
                ·
                  refine ⟨2354196976189067293848325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3138929301585423058464433 2354196976189067293848325)
                  ·
                    refine ⟨441411933035450117596561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2354196976189067293848325 441411933035450117596561)
                    ·
                      rfl

theorem cell22_1289470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_1289470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289470 prefixEnd_1289470 := by exact prefixLift 1289470
  have htrace : WordTrace (prefixWord ++ tailWord_1289470) baseStart_1289470 baseEnd_1289470 := by
    simpa [prefixWord, tailWord_1289470, baseEnd_1289470] using wordTrace_append hprefix tailTrace_1289470
  have hstable : (prefixWord ++ tailWord_1289470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289470).length < 2 ^ (prefixWord ++ tailWord_1289470).sum := by decide
  have hdescent : baseEnd_1289470 < baseStart_1289470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289474 : List Nat := [3, 4, 1, 1, 3, 1, 3, 2, 4]
def baseStart_1289474 : Nat := 118140960795 + 1289474 * 2 ^ 59
def prefixEnd_1289474 : Nat := 4983230072969 + 3 ^ 40 * 1289474 * 2
def baseEnd_1289474 : Nat := 147137767439065146832183

theorem tailTrace_1289474 : CollatzResearch.WordTrace tailWord_1289474 prefixEnd_1289474 147137767439065146832183 := by
  unfold tailWord_1289474
  simp only [CollatzResearch.WordTrace]
  refine ⟨11757745132615849367832869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31353987020308931647554317 11757745132615849367832869)
  ·
    refine ⟨2204577212365471756468663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11757745132615849367832869 2204577212365471756468663)
    ·
      refine ⟨3306865818548207634702995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2204577212365471756468663 3306865818548207634702995)
      ·
        refine ⟨4960298727822311452054493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3306865818548207634702995 4960298727822311452054493)
        ·
          refine ⟨1860112022933366794520435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4960298727822311452054493 1860112022933366794520435)
          ·
            refine ⟨2790168034400050191780653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1860112022933366794520435 2790168034400050191780653)
            ·
              refine ⟨1046313012900018821917745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2790168034400050191780653 1046313012900018821917745)
              ·
                refine ⟨784734759675014116438309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1046313012900018821917745 784734759675014116438309)
                ·
                  refine ⟨147137767439065146832183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 784734759675014116438309 147137767439065146832183)
                  ·
                    rfl

theorem cell22_1289474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_1289474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289474 prefixEnd_1289474 := by exact prefixLift 1289474
  have htrace : WordTrace (prefixWord ++ tailWord_1289474) baseStart_1289474 baseEnd_1289474 := by
    simpa [prefixWord, tailWord_1289474, baseEnd_1289474] using wordTrace_append hprefix tailTrace_1289474
  have hstable : (prefixWord ++ tailWord_1289474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289474).length < 2 ^ (prefixWord ++ tailWord_1289474).sum := by decide
  have hdescent : baseEnd_1289474 < baseStart_1289474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289481 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 2, 6]
def baseStart_1289481 : Nat := 118140960795 + 1289481 * 2 ^ 59
def prefixEnd_1289481 : Nat := 4983230072969 + 3 ^ 40 * 1289481 * 2
def baseEnd_1289481 : Nat := 441415698560249755571527

theorem tailTrace_1289481 : CollatzResearch.WordTrace tailWord_1289481 prefixEnd_1289481 441415698560249755571527 := by
  unfold tailWord_1289481
  simp only [CollatzResearch.WordTrace]
  refine ⟨47031235841438037666836297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31354157227625358444557531 47031235841438037666836297)
  ·
    refine ⟨35273426881078528250127223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47031235841438037666836297 35273426881078528250127223)
    ·
      refine ⟨52910140321617792375190835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35273426881078528250127223 52910140321617792375190835)
      ·
        refine ⟨79365210482426688562786253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52910140321617792375190835 79365210482426688562786253)
        ·
          refine ⟨29761953930910008211044845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79365210482426688562786253 29761953930910008211044845)
          ·
            refine ⟨11160732724091253079141817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29761953930910008211044845 11160732724091253079141817)
            ·
              refine ⟨8370549543068439809356363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11160732724091253079141817 8370549543068439809356363)
              ·
                refine ⟨12555824314602659714034545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8370549543068439809356363 12555824314602659714034545)
                ·
                  refine ⟨9416868235951994785525909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12555824314602659714034545 9416868235951994785525909)
                  ·
                    refine ⟨441415698560249755571527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9416868235951994785525909 441415698560249755571527)
                    ·
                      rfl

theorem cell22_1289481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_1289481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289481 prefixEnd_1289481 := by exact prefixLift 1289481
  have htrace : WordTrace (prefixWord ++ tailWord_1289481) baseStart_1289481 baseEnd_1289481 := by
    simpa [prefixWord, tailWord_1289481, baseEnd_1289481] using wordTrace_append hprefix tailTrace_1289481
  have hstable : (prefixWord ++ tailWord_1289481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289481).length < 2 ^ (prefixWord ++ tailWord_1289481).sum := by decide
  have hdescent : baseEnd_1289481 < baseStart_1289481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289541 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 10]
def baseStart_1289541 : Nat := 118140960795 + 1289541 * 2 ^ 59
def prefixEnd_1289541 : Nat := 4983230072969 + 3 ^ 40 * 1289541 * 2
def baseEnd_1289541 : Nat := 147145412595476533023781

theorem tailTrace_1289541 : CollatzResearch.WordTrace tailWord_1289541 prefixEnd_1289541 147145412595476533023781 := by
  unfold tailWord_1289541
  simp only [CollatzResearch.WordTrace]
  refine ⟨47033424221220667914020477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31355616147480445276013651 47033424221220667914020477)
  ·
    refine ⟨17637534082957750467757679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47033424221220667914020477 17637534082957750467757679)
    ·
      refine ⟨26456301124436625701636519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17637534082957750467757679 26456301124436625701636519)
      ·
        refine ⟨39684451686654938552454779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26456301124436625701636519 39684451686654938552454779)
        ·
          refine ⟨59526677529982407828682169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39684451686654938552454779 59526677529982407828682169)
          ·
            refine ⟨44645008147486805871511627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59526677529982407828682169 44645008147486805871511627)
            ·
              refine ⟨66967512221230208807267441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44645008147486805871511627 66967512221230208807267441)
              ·
                refine ⟨50225634165922656605450581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66967512221230208807267441 50225634165922656605450581)
                ·
                  refine ⟨147145412595476533023781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 50225634165922656605450581 147145412595476533023781)
                  ·
                    rfl

theorem cell22_1289541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_1289541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289541 prefixEnd_1289541 := by exact prefixLift 1289541
  have htrace : WordTrace (prefixWord ++ tailWord_1289541) baseStart_1289541 baseEnd_1289541 := by
    simpa [prefixWord, tailWord_1289541, baseEnd_1289541] using wordTrace_append hprefix tailTrace_1289541
  have hstable : (prefixWord ++ tailWord_1289541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289541).length < 2 ^ (prefixWord ++ tailWord_1289541).sum := by decide
  have hdescent : baseEnd_1289541 < baseStart_1289541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289543 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 3, 4]
def baseStart_1289543 : Nat := 118140960795 + 1289543 * 2 ^ 59
def prefixEnd_1289543 : Nat := 4983230072969 + 3 ^ 40 * 1289543 * 2
def baseEnd_1289543 : Nat := 441436922427302260521337

theorem tailTrace_1289543 : CollatzResearch.WordTrace tailWord_1289543 prefixEnd_1289543 441436922427302260521337 := by
  unfold tailWord_1289543
  simp only [CollatzResearch.WordTrace]
  refine ⟨47033497167213422255593283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31355664778142281503728855 47033497167213422255593283)
  ·
    refine ⟨70550245750820133383389925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47033497167213422255593283 70550245750820133383389925)
    ·
      refine ⟨13228171078278775009385611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70550245750820133383389925 13228171078278775009385611)
      ·
        refine ⟨19842256617418162514078417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13228171078278775009385611 19842256617418162514078417)
        ·
          refine ⟨14881692463063621885558813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19842256617418162514078417 14881692463063621885558813)
          ·
            refine ⟨5580634673648858207084555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14881692463063621885558813 5580634673648858207084555)
            ·
              refine ⟨8370952010473287310626833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5580634673648858207084555 8370952010473287310626833)
              ·
                refine ⟨6278214007854965482970125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8370952010473287310626833 6278214007854965482970125)
                ·
                  refine ⟨2354330252945612056113797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6278214007854965482970125 2354330252945612056113797)
                  ·
                    refine ⟨441436922427302260521337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2354330252945612056113797 441436922427302260521337)
                    ·
                      rfl

theorem cell22_1289543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_1289543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289543 prefixEnd_1289543 := by exact prefixLift 1289543
  have htrace : WordTrace (prefixWord ++ tailWord_1289543) baseStart_1289543 baseEnd_1289543 := by
    simpa [prefixWord, tailWord_1289543, baseEnd_1289543] using wordTrace_append hprefix tailTrace_1289543
  have hstable : (prefixWord ++ tailWord_1289543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289543).length < 2 ^ (prefixWord ++ tailWord_1289543).sum := by decide
  have hdescent : baseEnd_1289543 < baseStart_1289543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289573 : List Nat := [1, 3, 1, 3, 1, 2, 1, 4, 1, 5]
def baseStart_1289573 : Nat := 118140960795 + 1289573 * 2 ^ 59
def prefixEnd_1289573 : Nat := 4983230072969 + 3 ^ 40 * 1289573 * 2
def baseEnd_1289573 : Nat := 441447192040392182271245

theorem tailTrace_1289573 : CollatzResearch.WordTrace tailWord_1289573 prefixEnd_1289573 441447192040392182271245 := by
  unfold tailWord_1289573
  simp only [CollatzResearch.WordTrace]
  refine ⟨47034591357104737379185373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31356394238069824919456915 47034591357104737379185373)
  ·
    refine ⟨17637971758914276517194515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47034591357104737379185373 17637971758914276517194515)
    ·
      refine ⟨26456957638371414775791773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17637971758914276517194515 26456957638371414775791773)
      ·
        refine ⟨9921359114389280540921915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26456957638371414775791773 9921359114389280540921915)
        ·
          refine ⟨14882038671583920811382873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9921359114389280540921915 14882038671583920811382873)
          ·
            refine ⟨11161529003687940608537155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14882038671583920811382873 11161529003687940608537155)
            ·
              refine ⟨16742293505531910912805733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11161529003687940608537155 16742293505531910912805733)
              ·
                refine ⟨3139180032287233296151075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16742293505531910912805733 3139180032287233296151075)
                ·
                  refine ⟨4708770048430849944226613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3139180032287233296151075 4708770048430849944226613)
                  ·
                    refine ⟨441447192040392182271245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4708770048430849944226613 441447192040392182271245)
                    ·
                      rfl

theorem cell22_1289573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_1289573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289573 prefixEnd_1289573 := by exact prefixLift 1289573
  have htrace : WordTrace (prefixWord ++ tailWord_1289573) baseStart_1289573 baseEnd_1289573 := by
    simpa [prefixWord, tailWord_1289573, baseEnd_1289573] using wordTrace_append hprefix tailTrace_1289573
  have hstable : (prefixWord ++ tailWord_1289573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289573).length < 2 ^ (prefixWord ++ tailWord_1289573).sum := by decide
  have hdescent : baseEnd_1289573 < baseStart_1289573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289620 : List Nat := [2, 4, 2, 1, 2, 2, 1, 8]
def baseStart_1289620 : Nat := 118140960795 + 1289620 * 2 ^ 59
def prefixEnd_1289620 : Nat := 4983230072969 + 3 ^ 40 * 1289620 * 2
def baseEnd_1289620 : Nat := 49051475677877747371789

theorem tailTrace_1289620 : CollatzResearch.WordTrace tailWord_1289620 prefixEnd_1289620 49051475677877747371789 := by
  unfold tailWord_1289620
  simp only [CollatzResearch.WordTrace]
  refine ⟨23518152793967232203073157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31357537058622976270764209 23518152793967232203073157)
  ·
    refine ⟨4409653648868856038076217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23518152793967232203073157 4409653648868856038076217)
    ·
      refine ⟨3307240236651642028557163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4409653648868856038076217 3307240236651642028557163)
      ·
        refine ⟨4960860354977463042835745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3307240236651642028557163 4960860354977463042835745)
        ·
          refine ⟨3720645266233097282126809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4960860354977463042835745 3720645266233097282126809)
          ·
            refine ⟨2790483949674822961595107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3720645266233097282126809 2790483949674822961595107)
            ·
              refine ⟨4185725924512234442392661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2790483949674822961595107 4185725924512234442392661)
              ·
                refine ⟨49051475677877747371789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4185725924512234442392661 49051475677877747371789)
                ·
                  rfl

theorem cell22_1289620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 8].length) (baseStart_1289620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289620 prefixEnd_1289620 := by exact prefixLift 1289620
  have htrace : WordTrace (prefixWord ++ tailWord_1289620) baseStart_1289620 baseEnd_1289620 := by
    simpa [prefixWord, tailWord_1289620, baseEnd_1289620] using wordTrace_append hprefix tailTrace_1289620
  have hstable : (prefixWord ++ tailWord_1289620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289620).length < 2 ^ (prefixWord ++ tailWord_1289620).sum := by decide
  have hdescent : baseEnd_1289620 < baseStart_1289620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289663 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 2, 5]
def baseStart_1289663 : Nat := 118140960795 + 1289663 * 2 ^ 59
def prefixEnd_1289663 : Nat := 4983230072969 + 3 ^ 40 * 1289663 * 2
def baseEnd_1289663 : Nat := 441478000879661947520969

theorem tailTrace_1289663 : CollatzResearch.WordTrace tailWord_1289663 prefixEnd_1289663 441478000879661947520969 := by
  unfold tailWord_1289663
  simp only [CollatzResearch.WordTrace]
  refine ⟨47037873926778682749961643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31358582617852455166641095 47037873926778682749961643)
  ·
    refine ⟨70556810890168024124942465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47037873926778682749961643 70556810890168024124942465)
    ·
      refine ⟨52917608167626018093706849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70556810890168024124942465 52917608167626018093706849)
      ·
        refine ⟨39688206125719513570280137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52917608167626018093706849 39688206125719513570280137)
        ·
          refine ⟨29766154594289635177710103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39688206125719513570280137 29766154594289635177710103)
          ·
            refine ⟨44649231891434452766565155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29766154594289635177710103 44649231891434452766565155)
            ·
              refine ⟨66973847837151679149847733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44649231891434452766565155 66973847837151679149847733)
              ·
                refine ⟨6278798234732969920298225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66973847837151679149847733 6278798234732969920298225)
                ·
                  refine ⟨4709098676049727440223669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6278798234732969920298225 4709098676049727440223669)
                  ·
                    refine ⟨441478000879661947520969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4709098676049727440223669 441478000879661947520969)
                    ·
                      rfl

theorem cell22_1289663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_1289663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289663 prefixEnd_1289663 := by exact prefixLift 1289663
  have htrace : WordTrace (prefixWord ++ tailWord_1289663) baseStart_1289663 baseEnd_1289663 := by
    simpa [prefixWord, tailWord_1289663, baseEnd_1289663] using wordTrace_append hprefix tailTrace_1289663
  have hstable : (prefixWord ++ tailWord_1289663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289663).length < 2 ^ (prefixWord ++ tailWord_1289663).sum := by decide
  have hdescent : baseEnd_1289663 < baseStart_1289663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289710 : List Nat := [4, 1, 2, 1, 2, 1, 2, 3, 6]
def baseStart_1289710 : Nat := 118140960795 + 1289710 * 2 ^ 59
def prefixEnd_1289710 : Nat := 4983230072969 + 3 ^ 40 * 1289710 * 2
def baseEnd_1289710 : Nat := 147164696646723163865275

theorem tailTrace_1289710 : CollatzResearch.WordTrace tailWord_1289710 prefixEnd_1289710 147164696646723163865275 := by
  unfold tailWord_1289710
  simp only [CollatzResearch.WordTrace]
  refine ⟨5879948519701051222115323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31359725438405606517948389 5879948519701051222115323)
  ·
    refine ⟨8819922779551576833172985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5879948519701051222115323 8819922779551576833172985)
    ·
      refine ⟨6614942084663682624879739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8819922779551576833172985 6614942084663682624879739)
      ·
        refine ⟨9922413126995523937319609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6614942084663682624879739 9922413126995523937319609)
        ·
          refine ⟨7441809845246642952989707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9922413126995523937319609 7441809845246642952989707)
          ·
            refine ⟨11162714767869964429484561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7441809845246642952989707 11162714767869964429484561)
            ·
              refine ⟨8372036075902473322113421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11162714767869964429484561 8372036075902473322113421)
              ·
                refine ⟨3139513528463427495792533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8372036075902473322113421 3139513528463427495792533)
                ·
                  refine ⟨147164696646723163865275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3139513528463427495792533 147164696646723163865275)
                  ·
                    rfl

theorem cell22_1289710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_1289710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289710 prefixEnd_1289710 := by exact prefixLift 1289710
  have htrace : WordTrace (prefixWord ++ tailWord_1289710) baseStart_1289710 baseEnd_1289710 := by
    simpa [prefixWord, tailWord_1289710, baseEnd_1289710] using wordTrace_append hprefix tailTrace_1289710
  have hstable : (prefixWord ++ tailWord_1289710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289710).length < 2 ^ (prefixWord ++ tailWord_1289710).sum := by decide
  have hdescent : baseEnd_1289710 < baseStart_1289710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289723 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 3, 6]
def baseStart_1289723 : Nat := 118140960795 + 1289723 * 2 ^ 59
def prefixEnd_1289723 : Nat := 4983230072969 + 3 ^ 40 * 1289723 * 2
def baseEnd_1289723 : Nat := 441498540105841791020785

theorem tailTrace_1289723 : CollatzResearch.WordTrace tailWord_1289723 prefixEnd_1289723 441498540105841791020785 := by
  unfold tailWord_1289723
  simp only [CollatzResearch.WordTrace]
  refine ⟨47040062306561312997145823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31360041537707541998097215 47040062306561312997145823)
  ·
    refine ⟨70560093459841969495718735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47040062306561312997145823 70560093459841969495718735)
    ·
      refine ⟨105840140189762954243578103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70560093459841969495718735 105840140189762954243578103)
      ·
        refine ⟨158760210284644431365367155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105840140189762954243578103 158760210284644431365367155)
        ·
          refine ⟨238140315426966647048050733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158760210284644431365367155 238140315426966647048050733)
          ·
            refine ⟨89302618285112492643019025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238140315426966647048050733 89302618285112492643019025)
            ·
              refine ⟨66976963713834369482264269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89302618285112492643019025 66976963713834369482264269)
              ·
                refine ⟨25116361392687888555849101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66976963713834369482264269 25116361392687888555849101)
                ·
                  refine ⟨9418635522257958208443413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25116361392687888555849101 9418635522257958208443413)
                  ·
                    refine ⟨441498540105841791020785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9418635522257958208443413 441498540105841791020785)
                    ·
                      rfl

theorem cell22_1289723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 6].length) (baseStart_1289723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289723 prefixEnd_1289723 := by exact prefixLift 1289723
  have htrace : WordTrace (prefixWord ++ tailWord_1289723) baseStart_1289723 baseEnd_1289723 := by
    simpa [prefixWord, tailWord_1289723, baseEnd_1289723] using wordTrace_append hprefix tailTrace_1289723
  have hstable : (prefixWord ++ tailWord_1289723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289723).length < 2 ^ (prefixWord ++ tailWord_1289723).sum := by decide
  have hdescent : baseEnd_1289723 < baseStart_1289723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289725 : List Nat := [1, 4, 1, 1, 1, 4, 1, 3, 1, 5]
def baseStart_1289725 : Nat := 118140960795 + 1289725 * 2 ^ 59
def prefixEnd_1289725 : Nat := 4983230072969 + 3 ^ 40 * 1289725 * 2
def baseEnd_1289725 : Nat := 441499224746714452470779

theorem tailTrace_1289725 : CollatzResearch.WordTrace tailWord_1289725 prefixEnd_1289725 441499224746714452470779 := by
  unfold tailWord_1289725
  simp only [CollatzResearch.WordTrace]
  refine ⟨47040135252554067338718629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31360090168369378225812419 47040135252554067338718629)
  ·
    refine ⟨8820025359853887626009743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47040135252554067338718629 8820025359853887626009743)
    ·
      refine ⟨13230038039780831439014615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8820025359853887626009743 13230038039780831439014615)
      ·
        refine ⟨19845057059671247158521923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13230038039780831439014615 19845057059671247158521923)
        ·
          refine ⟨29767585589506870737782885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19845057059671247158521923 29767585589506870737782885)
          ·
            refine ⟨5581422298032538263334291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29767585589506870737782885 5581422298032538263334291)
            ·
              refine ⟨8372133447048807395001437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5581422298032538263334291 8372133447048807395001437)
              ·
                refine ⟨3139550042643302773125539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8372133447048807395001437 3139550042643302773125539)
                ·
                  refine ⟨4709325063964954159688309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3139550042643302773125539 4709325063964954159688309)
                  ·
                    refine ⟨441499224746714452470779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4709325063964954159688309 441499224746714452470779)
                    ·
                      rfl

theorem cell22_1289725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_1289725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289725 prefixEnd_1289725 := by exact prefixLift 1289725
  have htrace : WordTrace (prefixWord ++ tailWord_1289725) baseStart_1289725 baseEnd_1289725 := by
    simpa [prefixWord, tailWord_1289725, baseEnd_1289725] using wordTrace_append hprefix tailTrace_1289725
  have hstable : (prefixWord ++ tailWord_1289725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289725).length < 2 ^ (prefixWord ++ tailWord_1289725).sum := by decide
  have hdescent : baseEnd_1289725 < baseStart_1289725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289789 : List Nat := [1, 4, 1, 3, 3, 2, 2, 6]
def baseStart_1289789 : Nat := 118140960795 + 1289789 * 2 ^ 59
def prefixEnd_1289789 : Nat := 4983230072969 + 3 ^ 40 * 1289789 * 2
def baseEnd_1289789 : Nat := 49057903694959957652287

theorem tailTrace_1289789 : CollatzResearch.WordTrace tailWord_1289789 prefixEnd_1289789 49057903694959957652287 := by
  unfold tailWord_1289789
  simp only [CollatzResearch.WordTrace]
  refine ⟨47042469524322206269048421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31361646349548137512698947 47042469524322206269048421)
  ·
    refine ⟨8820463035810413675446579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47042469524322206269048421 8820463035810413675446579)
    ·
      refine ⟨13230694553715620513169869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8820463035810413675446579 13230694553715620513169869)
      ·
        refine ⟨4961510457643357692438701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13230694553715620513169869 4961510457643357692438701)
        ·
          refine ⟨1860566421616259134664513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4961510457643357692438701 1860566421616259134664513)
          ·
            refine ⟨1395424816212194350998385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1860566421616259134664513 1395424816212194350998385)
            ·
              refine ⟨1046568612159145763248789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1395424816212194350998385 1046568612159145763248789)
              ·
                refine ⟨49057903694959957652287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1046568612159145763248789 49057903694959957652287)
                ·
                  rfl

theorem cell22_1289789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 6].length) (baseStart_1289789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289789 prefixEnd_1289789 := by exact prefixLift 1289789
  have htrace : WordTrace (prefixWord ++ tailWord_1289789) baseStart_1289789 baseEnd_1289789 := by
    simpa [prefixWord, tailWord_1289789, baseEnd_1289789] using wordTrace_append hprefix tailTrace_1289789
  have hstable : (prefixWord ++ tailWord_1289789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289789).length < 2 ^ (prefixWord ++ tailWord_1289789).sum := by decide
  have hdescent : baseEnd_1289789 < baseStart_1289789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289834 : List Nat := [3, 1, 3, 2, 1, 2, 4, 1, 5]
def baseStart_1289834 : Nat := 118140960795 + 1289834 * 2 ^ 59
def prefixEnd_1289834 : Nat := 4983230072969 + 3 ^ 40 * 1289834 * 2
def baseEnd_1289834 : Nat := 147178845891424833831815

theorem tailTrace_1289834 : CollatzResearch.WordTrace tailWord_1289834 prefixEnd_1289834 147178845891424833831815 := by
  unfold tailWord_1289834
  simp only [CollatzResearch.WordTrace]
  refine ⟨11761027702289794738609139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31362740539439452636291037 11761027702289794738609139)
  ·
    refine ⟨17641541553434692107913709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11761027702289794738609139 17641541553434692107913709)
    ·
      refine ⟨6615578082538009540467641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17641541553434692107913709 6615578082538009540467641)
      ·
        refine ⟨4961683561903507155350731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6615578082538009540467641 4961683561903507155350731)
        ·
          refine ⟨7442525342855260733026097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4961683561903507155350731 7442525342855260733026097)
          ·
            refine ⟨5581894007141445549769573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7442525342855260733026097 5581894007141445549769573)
            ·
              refine ⟨1046605126339021040581795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5581894007141445549769573 1046605126339021040581795)
              ·
                refine ⟨1569907689508531560872693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1046605126339021040581795 1569907689508531560872693)
                ·
                  refine ⟨147178845891424833831815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1569907689508531560872693 147178845891424833831815)
                  ·
                    rfl

theorem cell22_1289834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 5].length) (baseStart_1289834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289834 prefixEnd_1289834 := by exact prefixLift 1289834
  have htrace : WordTrace (prefixWord ++ tailWord_1289834) baseStart_1289834 baseEnd_1289834 := by
    simpa [prefixWord, tailWord_1289834, baseEnd_1289834] using wordTrace_append hprefix tailTrace_1289834
  have hstable : (prefixWord ++ tailWord_1289834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289834).length < 2 ^ (prefixWord ++ tailWord_1289834).sum := by decide
  have hdescent : baseEnd_1289834 < baseStart_1289834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289877 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 4, 3]
def baseStart_1289877 : Nat := 118140960795 + 1289877 * 2 ^ 59
def prefixEnd_1289877 : Nat := 4983230072969 + 3 ^ 40 * 1289877 * 2
def baseEnd_1289877 : Nat := 441551257453036722670313

theorem tailTrace_1289877 : CollatzResearch.WordTrace tailWord_1289877 prefixEnd_1289877 441551257453036722670313 := by
  unfold tailWord_1289877
  simp only [CollatzResearch.WordTrace]
  refine ⟨47045679148003397298251885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31363786098668931532167923 47045679148003397298251885)
  ·
    refine ⟨17642129680501273986844457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47045679148003397298251885 17642129680501273986844457)
    ·
      refine ⟨13231597260375955490133343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17642129680501273986844457 13231597260375955490133343)
      ·
        refine ⟨19847395890563933235200015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13231597260375955490133343 19847395890563933235200015)
        ·
          refine ⟨29771093835845899852800023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19847395890563933235200015 29771093835845899852800023)
          ·
            refine ⟨44656640753768849779200035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29771093835845899852800023 44656640753768849779200035)
            ·
              refine ⟨66984961130653274668800053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44656640753768849779200035 66984961130653274668800053)
              ·
                refine ⟨6279840105998744500200005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66984961130653274668800053 6279840105998744500200005)
                ·
                  refine ⟨1177470019874764593787501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6279840105998744500200005 1177470019874764593787501)
                  ·
                    refine ⟨441551257453036722670313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1177470019874764593787501 441551257453036722670313)
                    ·
                      rfl

theorem cell22_1289877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_1289877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289877 prefixEnd_1289877 := by exact prefixLift 1289877
  have htrace : WordTrace (prefixWord ++ tailWord_1289877) baseStart_1289877 baseEnd_1289877 := by
    simpa [prefixWord, tailWord_1289877, baseEnd_1289877] using wordTrace_append hprefix tailTrace_1289877
  have hstable : (prefixWord ++ tailWord_1289877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289877).length < 2 ^ (prefixWord ++ tailWord_1289877).sum := by decide
  have hdescent : baseEnd_1289877 < baseStart_1289877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289879 : List Nat := [1, 1, 3, 3, 2, 3, 1, 4, 4]
def baseStart_1289879 : Nat := 118140960795 + 1289879 * 2 ^ 59
def prefixEnd_1289879 : Nat := 4983230072969 + 3 ^ 40 * 1289879 * 2
def baseEnd_1289879 : Nat := 147183980697969794706769

theorem tailTrace_1289879 : CollatzResearch.WordTrace tailWord_1289879 prefixEnd_1289879 147183980697969794706769 := by
  unfold tailWord_1289879
  simp only [CollatzResearch.WordTrace]
  refine ⟨47045752093996151639824691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31363834729330767759883127 47045752093996151639824691)
  ·
    refine ⟨70568628140994227459737037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47045752093996151639824691 70568628140994227459737037)
    ·
      refine ⟨26463235552872835297401389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70568628140994227459737037 26463235552872835297401389)
      ·
        refine ⟨9923713332327313236525521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26463235552872835297401389 9923713332327313236525521)
        ·
          refine ⟨7442784999245484927394141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9923713332327313236525521 7442784999245484927394141)
          ·
            refine ⟨2791044374717056847772803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7442784999245484927394141 2791044374717056847772803)
            ·
              refine ⟨4186566562075585271659205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2791044374717056847772803 4186566562075585271659205)
              ·
                refine ⟨784981230389172238436101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4186566562075585271659205 784981230389172238436101)
                ·
                  refine ⟨147183980697969794706769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 784981230389172238436101 147183980697969794706769)
                  ·
                    rfl

theorem cell22_1289879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 4].length) (baseStart_1289879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289879 prefixEnd_1289879 := by exact prefixLift 1289879
  have htrace : WordTrace (prefixWord ++ tailWord_1289879) baseStart_1289879 baseEnd_1289879 := by
    simpa [prefixWord, tailWord_1289879, baseEnd_1289879] using wordTrace_append hprefix tailTrace_1289879
  have hstable : (prefixWord ++ tailWord_1289879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289879).length < 2 ^ (prefixWord ++ tailWord_1289879).sum := by decide
  have hdescent : baseEnd_1289879 < baseStart_1289879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289907 : List Nat := [1, 1, 1, 2, 3, 3, 5, 6]
def baseStart_1289907 : Nat := 118140960795 + 1289907 * 2 ^ 59
def prefixEnd_1289907 : Nat := 4983230072969 + 3 ^ 40 * 1289907 * 2
def baseEnd_1289907 : Nat := 49062391896236293824469

theorem tailTrace_1289907 : CollatzResearch.WordTrace tailWord_1289907 prefixEnd_1289907 49062391896236293824469 := by
  unfold tailWord_1289907
  simp only [CollatzResearch.WordTrace]
  refine ⟨47046773337894712421843975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31364515558596474947895983 47046773337894712421843975)
  ·
    refine ⟨70570160006842068632765963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47046773337894712421843975 70570160006842068632765963)
    ·
      refine ⟨105855240010263102949148945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70570160006842068632765963 105855240010263102949148945)
      ·
        refine ⟨79391430007697327211861709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105855240010263102949148945 79391430007697327211861709)
        ·
          refine ⟨29771786252886497704448141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79391430007697327211861709 29771786252886497704448141)
          ·
            refine ⟨11164419844832436639168053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29771786252886497704448141 11164419844832436639168053)
            ·
              refine ⟨1046664360453040934922005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11164419844832436639168053 1046664360453040934922005)
              ·
                refine ⟨49062391896236293824469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1046664360453040934922005 49062391896236293824469)
                ·
                  rfl

theorem cell22_1289907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 6].length) (baseStart_1289907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289907 prefixEnd_1289907 := by exact prefixLift 1289907
  have htrace : WordTrace (prefixWord ++ tailWord_1289907) baseStart_1289907 baseEnd_1289907 := by
    simpa [prefixWord, tailWord_1289907, baseEnd_1289907] using wordTrace_append hprefix tailTrace_1289907
  have hstable : (prefixWord ++ tailWord_1289907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289907).length < 2 ^ (prefixWord ++ tailWord_1289907).sum := by decide
  have hdescent : baseEnd_1289907 < baseStart_1289907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289909 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 1, 6]
def baseStart_1289909 : Nat := 118140960795 + 1289909 * 2 ^ 59
def prefixEnd_1289909 : Nat := 4983230072969 + 3 ^ 40 * 1289909 * 2
def baseEnd_1289909 : Nat := 441562211706999305870215

theorem tailTrace_1289909 : CollatzResearch.WordTrace tailWord_1289909 prefixEnd_1289909 441562211706999305870215 := by
  unfold tailWord_1289909
  simp only [CollatzResearch.WordTrace]
  refine ⟨47046846283887466763416781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31364564189258311175611187 47046846283887466763416781)
  ·
    refine ⟨17642567356457800036281293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47046846283887466763416781 17642567356457800036281293)
    ·
      refine ⟨6615962758671675013605485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17642567356457800036281293 6615962758671675013605485)
      ·
        refine ⟨2480986034501878130102057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6615962758671675013605485 2480986034501878130102057)
        ·
          refine ⟨1860739525876408597576543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2480986034501878130102057 1860739525876408597576543)
          ·
            refine ⟨2791109288814612896364815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1860739525876408597576543 2791109288814612896364815)
            ·
              refine ⟨4186663933221919344547223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2791109288814612896364815 4186663933221919344547223)
              ·
                refine ⟨6279995899832879016820835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4186663933221919344547223 6279995899832879016820835)
                ·
                  refine ⟨9419993849749318525231253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6279995899832879016820835 9419993849749318525231253)
                  ·
                    refine ⟨441562211706999305870215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9419993849749318525231253 441562211706999305870215)
                    ·
                      rfl

theorem cell22_1289909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_1289909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289909 prefixEnd_1289909 := by exact prefixLift 1289909
  have htrace : WordTrace (prefixWord ++ tailWord_1289909) baseStart_1289909 baseEnd_1289909 := by
    simpa [prefixWord, tailWord_1289909, baseEnd_1289909] using wordTrace_append hprefix tailTrace_1289909
  have hstable : (prefixWord ++ tailWord_1289909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289909).length < 2 ^ (prefixWord ++ tailWord_1289909).sum := by decide
  have hdescent : baseEnd_1289909 < baseStart_1289909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289952 : List Nat := [2, 1, 1, 3, 1, 2, 2, 5, 5]
def baseStart_1289952 : Nat := 118140960795 + 1289952 * 2 ^ 59
def prefixEnd_1289952 : Nat := 4983230072969 + 3 ^ 40 * 1289952 * 2
def baseEnd_1289952 : Nat := 147192310495253842348361

theorem tailTrace_1289952 : CollatzResearch.WordTrace tailWord_1289952 prefixEnd_1289952 147192310495253842348361 := by
  unfold tailWord_1289952
  simp only [CollatzResearch.WordTrace]
  refine ⟨23524207311365842553616055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31365609748487790071488073 23524207311365842553616055)
  ·
    refine ⟨35286310967048763830424083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23524207311365842553616055 35286310967048763830424083)
    ·
      refine ⟨52929466450573145745636125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35286310967048763830424083 52929466450573145745636125)
      ·
        refine ⟨19848549918964929654613547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52929466450573145745636125 19848549918964929654613547)
        ·
          refine ⟨29772824878447394481920321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19848549918964929654613547 29772824878447394481920321)
          ·
            refine ⟨22329618658835545861440241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29772824878447394481920321 22329618658835545861440241)
            ·
              refine ⟨16747213994126659396080181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22329618658835545861440241 16747213994126659396080181)
              ·
                refine ⟨1570051311949374318382517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16747213994126659396080181 1570051311949374318382517)
                ·
                  refine ⟨147192310495253842348361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1570051311949374318382517 147192310495253842348361)
                  ·
                    rfl

theorem cell22_1289952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 5].length) (baseStart_1289952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1289952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1289952 prefixEnd_1289952 := by exact prefixLift 1289952
  have htrace : WordTrace (prefixWord ++ tailWord_1289952) baseStart_1289952 baseEnd_1289952 := by
    simpa [prefixWord, tailWord_1289952, baseEnd_1289952] using wordTrace_append hprefix tailTrace_1289952
  have hstable : (prefixWord ++ tailWord_1289952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289952).length < 2 ^ (prefixWord ++ tailWord_1289952).sum := by decide
  have hdescent : baseEnd_1289952 < baseStart_1289952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290042 : List Nat := [3, 1, 1, 1, 5, 11]
def baseStart_1290042 : Nat := 118140960795 + 1290042 * 2 ^ 59
def prefixEnd_1290042 : Nat := 4983230072969 + 3 ^ 40 * 1290042 * 2
def baseEnd_1290042 : Nat := 5451947411420139411047

theorem tailTrace_1290042 : CollatzResearch.WordTrace tailWord_1290042 prefixEnd_1290042 5451947411420139411047 := by
  unfold tailWord_1290042
  simp only [CollatzResearch.WordTrace]
  refine ⟨11762924298101407619502095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31367798128270420318672253 11762924298101407619502095)
  ·
    refine ⟨17644386447152111429253143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11762924298101407619502095 17644386447152111429253143)
    ·
      refine ⟨26466579670728167143879715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17644386447152111429253143 26466579670728167143879715)
      ·
        refine ⟨39699869506092250715819573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26466579670728167143879715 39699869506092250715819573)
        ·
          refine ⟨3721862766196148504608085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39699869506092250715819573 3721862766196148504608085)
          ·
            refine ⟨5451947411420139411047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3721862766196148504608085 5451947411420139411047)
            ·
              rfl

theorem cell22_1290042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 11].length) (baseStart_1290042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290042 prefixEnd_1290042 := by exact prefixLift 1290042
  have htrace : WordTrace (prefixWord ++ tailWord_1290042) baseStart_1290042 baseEnd_1290042 := by
    simpa [prefixWord, tailWord_1290042, baseEnd_1290042] using wordTrace_append hprefix tailTrace_1290042
  have hstable : (prefixWord ++ tailWord_1290042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290042).length < 2 ^ (prefixWord ++ tailWord_1290042).sum := by decide
  have hdescent : baseEnd_1290042 < baseStart_1290042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290044 : List Nat := [2, 2, 2, 2, 1, 1, 4, 2, 2, 4]
def baseStart_1290044 : Nat := 118140960795 + 1290044 * 2 ^ 59
def prefixEnd_1290044 : Nat := 4983230072969 + 3 ^ 40 * 1290044 * 2
def baseEnd_1290044 : Nat := 441608424965903953744801

theorem tailTrace_1290044 : CollatzResearch.WordTrace tailWord_1290044 prefixEnd_1290044 441608424965903953744801 := by
  unfold tailWord_1290044
  simp only [CollatzResearch.WordTrace]
  refine ⟨23525885069199192409790593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31367846758932256546387457 23525885069199192409790593)
  ·
    refine ⟨17644413801899394307342945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23525885069199192409790593 17644413801899394307342945)
    ·
      refine ⟨13233310351424545730507209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17644413801899394307342945 13233310351424545730507209)
      ·
        refine ⟨9924982763568409297880407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13233310351424545730507209 9924982763568409297880407)
        ·
          refine ⟨14887474145352613946820611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9924982763568409297880407 14887474145352613946820611)
          ·
            refine ⟨22331211218028920920230917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14887474145352613946820611 22331211218028920920230917)
            ·
              refine ⟨4187102103380422672543297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22331211218028920920230917 4187102103380422672543297)
              ·
                refine ⟨3140326577535317004407473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4187102103380422672543297 3140326577535317004407473)
                ·
                  refine ⟨2355244933151487753305605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3140326577535317004407473 2355244933151487753305605)
                  ·
                    refine ⟨441608424965903953744801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2355244933151487753305605 441608424965903953744801)
                    ·
                      rfl

theorem cell22_1290044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_1290044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290044 prefixEnd_1290044 := by exact prefixLift 1290044
  have htrace : WordTrace (prefixWord ++ tailWord_1290044) baseStart_1290044 baseEnd_1290044 := by
    simpa [prefixWord, tailWord_1290044, baseEnd_1290044] using wordTrace_append hprefix tailTrace_1290044
  have hstable : (prefixWord ++ tailWord_1290044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290044).length < 2 ^ (prefixWord ++ tailWord_1290044).sum := by decide
  have hdescent : baseEnd_1290044 < baseStart_1290044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290121 : List Nat := [1, 2, 1, 1, 5, 1, 5, 1, 5]
def baseStart_1290121 : Nat := 118140960795 + 1290121 * 2 ^ 59
def prefixEnd_1290121 : Nat := 4983230072969 + 3 ^ 40 * 1290121 * 2
def baseEnd_1290121 : Nat := 147211594546500473189855

theorem tailTrace_1290121 : CollatzResearch.WordTrace tailWord_1290121 prefixEnd_1290121 147211594546500473189855 := by
  unfold tailWord_1290121
  simp only [CollatzResearch.WordTrace]
  refine ⟨47054578559119426970134217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31369719039412951313422811 47054578559119426970134217)
  ·
    refine ⟨35290933919339570227600663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47054578559119426970134217 35290933919339570227600663)
    ·
      refine ⟨52936400879009355341400995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35290933919339570227600663 52936400879009355341400995)
      ·
        refine ⟨79404601318514033012101493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52936400879009355341400995 79404601318514033012101493)
        ·
          refine ⟨7444181373610690594884515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79404601318514033012101493 7444181373610690594884515)
          ·
            refine ⟨11166272060416035892326773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7444181373610690594884515 11166272060416035892326773)
            ·
              refine ⟨1046838005664003364905635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11166272060416035892326773 1046838005664003364905635)
              ·
                refine ⟨1570257008496005047358453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1046838005664003364905635 1570257008496005047358453)
                ·
                  refine ⟨147211594546500473189855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1570257008496005047358453 147211594546500473189855)
                  ·
                    rfl

theorem cell22_1290121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 5].length) (baseStart_1290121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290121 prefixEnd_1290121 := by exact prefixLift 1290121
  have htrace : WordTrace (prefixWord ++ tailWord_1290121) baseStart_1290121 baseEnd_1290121 := by
    simpa [prefixWord, tailWord_1290121, baseEnd_1290121] using wordTrace_append hprefix tailTrace_1290121
  have hstable : (prefixWord ++ tailWord_1290121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290121).length < 2 ^ (prefixWord ++ tailWord_1290121).sum := by decide
  have hdescent : baseEnd_1290121 < baseStart_1290121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290172 : List Nat := [2, 2, 2, 5, 2, 1, 2, 1, 5]
def baseStart_1290172 : Nat := 118140960795 + 1290172 * 2 ^ 59
def prefixEnd_1290172 : Nat := 4983230072969 + 3 ^ 40 * 1290172 * 2
def baseEnd_1290172 : Nat := 147217413993918095514803

theorem tailTrace_1290172 : CollatzResearch.WordTrace tailWord_1290172 prefixEnd_1290172 147217413993918095514803 := by
  unfold tailWord_1290172
  simp only [CollatzResearch.WordTrace]
  refine ⟨23528219340967331340120385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31370959121289775120160513 23528219340967331340120385)
  ·
    refine ⟨17646164505725498505090289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23528219340967331340120385 17646164505725498505090289)
    ·
      refine ⟨13234623379294123878817717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17646164505725498505090289 13234623379294123878817717)
      ·
        refine ⟨1240745941808824113639161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13234623379294123878817717 1240745941808824113639161)
        ·
          refine ⟨930559456356618085229371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1240745941808824113639161 930559456356618085229371)
          ·
            refine ⟨1395839184534927127844057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930559456356618085229371 1395839184534927127844057)
            ·
              refine ⟨1046879388401195345883043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1395839184534927127844057 1046879388401195345883043)
              ·
                refine ⟨1570319082601793018824565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1046879388401195345883043 1570319082601793018824565)
                ·
                  refine ⟨147217413993918095514803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1570319082601793018824565 147217413993918095514803)
                  ·
                    rfl

theorem cell22_1290172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 5].length) (baseStart_1290172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290172 prefixEnd_1290172 := by exact prefixLift 1290172
  have htrace : WordTrace (prefixWord ++ tailWord_1290172) baseStart_1290172 baseEnd_1290172 := by
    simpa [prefixWord, tailWord_1290172, baseEnd_1290172] using wordTrace_append hprefix tailTrace_1290172
  have hstable : (prefixWord ++ tailWord_1290172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290172).length < 2 ^ (prefixWord ++ tailWord_1290172).sum := by decide
  have hdescent : baseEnd_1290172 < baseStart_1290172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290215 : List Nat := [1, 1, 5, 2, 3, 1, 2, 2, 2, 3]
def baseStart_1290215 : Nat := 118140960795 + 1290215 * 2 ^ 59
def prefixEnd_1290215 : Nat := 4983230072969 + 3 ^ 40 * 1290215 * 2
def baseEnd_1290215 : Nat := 441666961760516507719277

theorem tailTrace_1290215 : CollatzResearch.WordTrace tailWord_1290215 prefixEnd_1290215 441666961760516507719277 := by
  unfold tailWord_1290215
  simp only [CollatzResearch.WordTrace]
  refine ⟨47058007020778881024056099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31372004680519254016037399 47058007020778881024056099)
  ·
    refine ⟨70587010531168321536084149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47058007020778881024056099 70587010531168321536084149)
    ·
      refine ⟨6617532237297030144007889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70587010531168321536084149 6617532237297030144007889)
      ·
        refine ⟨4963149177972772608005917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6617532237297030144007889 4963149177972772608005917)
        ·
          refine ⟨1861180941739789728002219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4963149177972772608005917 1861180941739789728002219)
          ·
            refine ⟨2791771412609684592003329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1861180941739789728002219 2791771412609684592003329)
            ·
              refine ⟨2093828559457263444002497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2791771412609684592003329 2093828559457263444002497)
              ·
                refine ⟨1570371419592947583001873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2093828559457263444002497 1570371419592947583001873)
                ·
                  refine ⟨1177778564694710687251405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1570371419592947583001873 1177778564694710687251405)
                  ·
                    refine ⟨441666961760516507719277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1177778564694710687251405 441666961760516507719277)
                    ·
                      rfl

theorem cell22_1290215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_1290215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290215 prefixEnd_1290215 := by exact prefixLift 1290215
  have htrace : WordTrace (prefixWord ++ tailWord_1290215) baseStart_1290215 baseEnd_1290215 := by
    simpa [prefixWord, tailWord_1290215, baseEnd_1290215] using wordTrace_append hprefix tailTrace_1290215
  have hstable : (prefixWord ++ tailWord_1290215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290215).length < 2 ^ (prefixWord ++ tailWord_1290215).sum := by decide
  have hdescent : baseEnd_1290215 < baseStart_1290215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290224 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 2, 6]
def baseStart_1290224 : Nat := 118140960795 + 1290224 * 2 ^ 59
def prefixEnd_1290224 : Nat := 4983230072969 + 3 ^ 40 * 1290224 * 2
def baseEnd_1290224 : Nat := 441670042644443484244249

theorem tailTrace_1290224 : CollatzResearch.WordTrace tailWord_1290224 prefixEnd_1290224 441670042644443484244249 := by
  unfold tailWord_1290224
  simp only [CollatzResearch.WordTrace]
  refine ⟨23529167638873137780566863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31372223518497517040755817 23529167638873137780566863)
  ·
    refine ⟨35293751458309706670850295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23529167638873137780566863 35293751458309706670850295)
    ·
      refine ⟨52940627187464560006275443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35293751458309706670850295 52940627187464560006275443)
      ·
        refine ⟨79410940781196840009413165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52940627187464560006275443 79410940781196840009413165)
        ·
          refine ⟨29779102792948815003529937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79410940781196840009413165 29779102792948815003529937)
          ·
            refine ⟨22334327094711611252647453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29779102792948815003529937 22334327094711611252647453)
            ·
              refine ⟨8375372660516854219742795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22334327094711611252647453 8375372660516854219742795)
              ·
                refine ⟨12563058990775281329614193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8375372660516854219742795 12563058990775281329614193)
                ·
                  refine ⟨9422294243081460997210645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12563058990775281329614193 9422294243081460997210645)
                  ·
                    refine ⟨441670042644443484244249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9422294243081460997210645 441670042644443484244249)
                    ·
                      rfl

theorem cell22_1290224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_1290224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290224 prefixEnd_1290224 := by exact prefixLift 1290224
  have htrace : WordTrace (prefixWord ++ tailWord_1290224) baseStart_1290224 baseEnd_1290224 := by
    simpa [prefixWord, tailWord_1290224, baseEnd_1290224] using wordTrace_append hprefix tailTrace_1290224
  have hstable : (prefixWord ++ tailWord_1290224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290224).length < 2 ^ (prefixWord ++ tailWord_1290224).sum := by decide
  have hdescent : baseEnd_1290224 < baseStart_1290224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290301 : List Nat := [1, 4, 1, 3, 1, 1, 1, 4, 6]
def baseStart_1290301 : Nat := 118140960795 + 1290301 * 2 ^ 59
def prefixEnd_1290301 : Nat := 4983230072969 + 3 ^ 40 * 1290301 * 2
def baseEnd_1290301 : Nat := 147232133772680316689671

theorem tailTrace_1290301 : CollatzResearch.WordTrace tailWord_1290301 prefixEnd_1290301 147232133772680316689671 := by
  unfold tailWord_1290301
  simp only [CollatzResearch.WordTrace]
  refine ⟨47061143698467317711686757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31374095798978211807791171 47061143698467317711686757)
  ·
    refine ⟨8823964443462622070941267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47061143698467317711686757 8823964443462622070941267)
    ·
      refine ⟨13235946665193933106411901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8823964443462622070941267 13235946665193933106411901)
      ·
        refine ⟨4963479999447724914904463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13235946665193933106411901 4963479999447724914904463)
        ·
          refine ⟨7445219999171587372356695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4963479999447724914904463 7445219999171587372356695)
          ·
            refine ⟨11167829998757381058535043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7445219999171587372356695 11167829998757381058535043)
            ·
              refine ⟨16751744998136071587802565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11167829998757381058535043 16751744998136071587802565)
              ·
                refine ⟨3140952187150513422712981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16751744998136071587802565 3140952187150513422712981)
                ·
                  refine ⟨147232133772680316689671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3140952187150513422712981 147232133772680316689671)
                  ·
                    rfl

theorem cell22_1290301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_1290301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290301 prefixEnd_1290301 := by exact prefixLift 1290301
  have htrace : WordTrace (prefixWord ++ tailWord_1290301) baseStart_1290301 baseEnd_1290301 := by
    simpa [prefixWord, tailWord_1290301, baseEnd_1290301] using wordTrace_append hprefix tailTrace_1290301
  have hstable : (prefixWord ++ tailWord_1290301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290301).length < 2 ^ (prefixWord ++ tailWord_1290301).sum := by decide
  have hdescent : baseEnd_1290301 < baseStart_1290301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290316 : List Nat := [2, 2, 1, 3, 1, 1, 2, 4, 1, 5]
def baseStart_1290316 : Nat := 118140960795 + 1290316 * 2 ^ 59
def prefixEnd_1290316 : Nat := 4983230072969 + 3 ^ 40 * 1290316 * 2
def baseEnd_1290316 : Nat := 441701536124585910943967

theorem tailTrace_1290316 : CollatzResearch.WordTrace tailWord_1290316 prefixEnd_1290316 441701536124585910943967 := by
  unfold tailWord_1290316
  simp only [CollatzResearch.WordTrace]
  refine ⟨23530845396706487636741401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31374460528941983515655201 23530845396706487636741401)
  ·
    refine ⟨17648134047529865727556051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23530845396706487636741401 17648134047529865727556051)
    ·
      refine ⟨26472201071294798591334077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17648134047529865727556051 26472201071294798591334077)
      ·
        refine ⟨9927075401735549471750279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26472201071294798591334077 9927075401735549471750279)
        ·
          refine ⟨14890613102603324207625419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9927075401735549471750279 14890613102603324207625419)
          ·
            refine ⟨22335919653904986311438129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14890613102603324207625419 22335919653904986311438129)
            ·
              refine ⟨16751939740428739733578597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22335919653904986311438129 16751939740428739733578597)
              ·
                refine ⟨3140988701330388700045987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16751939740428739733578597 3140988701330388700045987)
                ·
                  refine ⟨4711483051995583050068981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3140988701330388700045987 4711483051995583050068981)
                  ·
                    refine ⟨441701536124585910943967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4711483051995583050068981 441701536124585910943967)
                    ·
                      rfl

theorem cell22_1290316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_1290316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290316 prefixEnd_1290316 := by exact prefixLift 1290316
  have htrace : WordTrace (prefixWord ++ tailWord_1290316) baseStart_1290316 baseEnd_1290316 := by
    simpa [prefixWord, tailWord_1290316, baseEnd_1290316] using wordTrace_append hprefix tailTrace_1290316
  have hstable : (prefixWord ++ tailWord_1290316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290316).length < 2 ^ (prefixWord ++ tailWord_1290316).sum := by decide
  have hdescent : baseEnd_1290316 < baseStart_1290316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290350 : List Nat := [4, 1, 2, 2, 1, 1, 3, 3, 2, 3]
def baseStart_1290350 : Nat := 118140960795 + 1290350 * 2 ^ 59
def prefixEnd_1290350 : Nat := 4983230072969 + 3 ^ 40 * 1290350 * 2
def baseEnd_1290350 : Nat := 441713175019421155593863

theorem tailTrace_1290350 : CollatzResearch.WordTrace tailWord_1290350 prefixEnd_1290350 441713175019421155593863 := by
  unfold tailWord_1290350
  simp only [CollatzResearch.WordTrace]
  refine ⟨5882866359411224885027563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31375287250193199386813669 5882866359411224885027563)
  ·
    refine ⟨8824299539116837327541345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5882866359411224885027563 8824299539116837327541345)
    ·
      refine ⟨6618224654337627995656009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8824299539116837327541345 6618224654337627995656009)
      ·
        refine ⟨4963668490753220996742007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6618224654337627995656009 4963668490753220996742007)
        ·
          refine ⟨7445502736129831495113011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4963668490753220996742007 7445502736129831495113011)
          ·
            refine ⟨11168254104194747242669517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7445502736129831495113011 11168254104194747242669517)
            ·
              refine ⟨4188095289073030216001069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11168254104194747242669517 4188095289073030216001069)
              ·
                refine ⟨1570535733402386331000401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4188095289073030216001069 1570535733402386331000401)
                ·
                  refine ⟨1177901800051789748250301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1570535733402386331000401 1177901800051789748250301)
                  ·
                    refine ⟨441713175019421155593863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1177901800051789748250301 441713175019421155593863)
                    ·
                      rfl

theorem cell22_1290350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_1290350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290350 prefixEnd_1290350 := by exact prefixLift 1290350
  have htrace : WordTrace (prefixWord ++ tailWord_1290350) baseStart_1290350 baseEnd_1290350 := by
    simpa [prefixWord, tailWord_1290350, baseEnd_1290350] using wordTrace_append hprefix tailTrace_1290350
  have hstable : (prefixWord ++ tailWord_1290350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290350).length < 2 ^ (prefixWord ++ tailWord_1290350).sum := by decide
  have hdescent : baseEnd_1290350 < baseStart_1290350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290483 : List Nat := [1, 1, 1, 2, 2, 4, 2, 3, 2, 4]
def baseStart_1290483 : Nat := 118140960795 + 1290483 * 2 ^ 59
def prefixEnd_1290483 : Nat := 4983230072969 + 3 ^ 40 * 1290483 * 2
def baseEnd_1290483 : Nat := 441758703637453142018455

theorem tailTrace_1290483 : CollatzResearch.WordTrace tailWord_1290483 prefixEnd_1290483 441758703637453142018455 := by
  unfold tailWord_1290483
  simp only [CollatzResearch.WordTrace]
  refine ⟨47067781783807962794812103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31378521189205308529874735 47067781783807962794812103)
  ·
    refine ⟨70601672675711944192218155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47067781783807962794812103 70601672675711944192218155)
    ·
      refine ⟨105902509013567916288327233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70601672675711944192218155 105902509013567916288327233)
      ·
        refine ⟨79426881760175937216245425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105902509013567916288327233 79426881760175937216245425)
        ·
          refine ⟨59570161320131952912184069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79426881760175937216245425 59570161320131952912184069)
          ·
            refine ⟨11169405247524741171034513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59570161320131952912184069 11169405247524741171034513)
            ·
              refine ⟨8377053935643555878275885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11169405247524741171034513 8377053935643555878275885)
              ·
                refine ⟨3141395225866333454353457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8377053935643555878275885 3141395225866333454353457)
                ·
                  refine ⟨2356046419399750090765093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3141395225866333454353457 2356046419399750090765093)
                  ·
                    refine ⟨441758703637453142018455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2356046419399750090765093 441758703637453142018455)
                    ·
                      rfl

theorem cell22_1290483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 4].length) (baseStart_1290483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290483 prefixEnd_1290483 := by exact prefixLift 1290483
  have htrace : WordTrace (prefixWord ++ tailWord_1290483) baseStart_1290483 baseEnd_1290483 := by
    simpa [prefixWord, tailWord_1290483, baseEnd_1290483] using wordTrace_append hprefix tailTrace_1290483
  have hstable : (prefixWord ++ tailWord_1290483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290483).length < 2 ^ (prefixWord ++ tailWord_1290483).sum := by decide
  have hdescent : baseEnd_1290483 < baseStart_1290483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290519 : List Nat := [1, 1, 3, 4, 1, 4, 2, 1, 2, 3]
def baseStart_1290519 : Nat := 118140960795 + 1290519 * 2 ^ 59
def prefixEnd_1290519 : Nat := 4983230072969 + 3 ^ 40 * 1290519 * 2
def baseEnd_1290519 : Nat := 441771027173161048118345

theorem tailTrace_1290519 : CollatzResearch.WordTrace tailWord_1290519 prefixEnd_1290519 441771027173161048118345 := by
  unfold tailWord_1290519
  simp only [CollatzResearch.WordTrace]
  refine ⟨47069094811677540943122611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31379396541118360628748407 47069094811677540943122611)
  ·
    refine ⟨70603642217516311414683917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47069094811677540943122611 70603642217516311414683917)
    ·
      refine ⟨26476365831568616780506469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70603642217516311414683917 26476365831568616780506469)
      ·
        refine ⟨4964318593419115646344963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26476365831568616780506469 4964318593419115646344963)
        ·
          refine ⟨7446477890128673469517445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4964318593419115646344963 7446477890128673469517445)
          ·
            refine ⟨1396214604399126275534521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7446477890128673469517445 1396214604399126275534521)
            ·
              refine ⟨1047160953299344706650891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1396214604399126275534521 1047160953299344706650891)
              ·
                refine ⟨1570741429949017059976337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1047160953299344706650891 1570741429949017059976337)
                ·
                  refine ⟨1178056072461762794982253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1570741429949017059976337 1178056072461762794982253)
                  ·
                    refine ⟨441771027173161048118345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1178056072461762794982253 441771027173161048118345)
                    ·
                      rfl

theorem cell22_1290519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 2, 3].length) (baseStart_1290519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290519 prefixEnd_1290519 := by exact prefixLift 1290519
  have htrace : WordTrace (prefixWord ++ tailWord_1290519) baseStart_1290519 baseEnd_1290519 := by
    simpa [prefixWord, tailWord_1290519, baseEnd_1290519] using wordTrace_append hprefix tailTrace_1290519
  have hstable : (prefixWord ++ tailWord_1290519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290519).length < 2 ^ (prefixWord ++ tailWord_1290519).sum := by decide
  have hdescent : baseEnd_1290519 < baseStart_1290519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290547 : List Nat := [1, 1, 1, 2, 5, 1, 2, 5, 1, 3]
def baseStart_1290547 : Nat := 118140960795 + 1290547 * 2 ^ 59
def prefixEnd_1290547 : Nat := 4983230072969 + 3 ^ 40 * 1290547 * 2
def baseEnd_1290547 : Nat := 441780612145378308418259

theorem tailTrace_1290547 : CollatzResearch.WordTrace tailWord_1290547 prefixEnd_1290547 441780612145378308418259 := by
  unfold tailWord_1290547
  simp only [CollatzResearch.WordTrace]
  refine ⟨47070116055576101725141895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31380077370384067816761263 47070116055576101725141895)
  ·
    refine ⟨70605174083364152587712843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47070116055576101725141895 70605174083364152587712843)
    ·
      refine ⟨105907761125046228881569265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70605174083364152587712843 105907761125046228881569265)
      ·
        refine ⟨79430820843784671661176949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105907761125046228881569265 79430820843784671661176949)
        ·
          refine ⟨7446639454104812968235339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79430820843784671661176949 7446639454104812968235339)
          ·
            refine ⟨11169959181157219452353009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7446639454104812968235339 11169959181157219452353009)
            ·
              refine ⟨8377469385867914589264757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11169959181157219452353009 8377469385867914589264757)
              ·
                refine ⟨785387754925116992743571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8377469385867914589264757 785387754925116992743571)
                ·
                  refine ⟨1178081632387675489115357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 785387754925116992743571 1178081632387675489115357)
                  ·
                    refine ⟨441780612145378308418259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1178081632387675489115357 441780612145378308418259)
                    ·
                      rfl

theorem cell22_1290547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 1, 3].length) (baseStart_1290547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290547 prefixEnd_1290547 := by exact prefixLift 1290547
  have htrace : WordTrace (prefixWord ++ tailWord_1290547) baseStart_1290547 baseEnd_1290547 := by
    simpa [prefixWord, tailWord_1290547, baseEnd_1290547] using wordTrace_append hprefix tailTrace_1290547
  have hstable : (prefixWord ++ tailWord_1290547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290547).length < 2 ^ (prefixWord ++ tailWord_1290547).sum := by decide
  have hdescent : baseEnd_1290547 < baseStart_1290547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290618 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 5, 6]
def baseStart_1290618 : Nat := 118140960795 + 1290618 * 2 ^ 59
def prefixEnd_1290618 : Nat := 4983230072969 + 3 ^ 40 * 1290618 * 2
def baseEnd_1290618 : Nat := 441804916896357789893041

theorem tailTrace_1290618 : CollatzResearch.WordTrace tailWord_1290618 prefixEnd_1290618 441804916896357789893041 := by
  unfold tailWord_1290618
  simp only [CollatzResearch.WordTrace]
  refine ⟨11768176409579720212744127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31381803758879253900651005 11768176409579720212744127)
  ·
    refine ⟨17652264614369580319116191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11768176409579720212744127 17652264614369580319116191)
    ·
      refine ⟨26478396921554370478674287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17652264614369580319116191 26478396921554370478674287)
      ·
        refine ⟨39717595382331555718011431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26478396921554370478674287 39717595382331555718011431)
        ·
          refine ⟨59576393073497333577017147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39717595382331555718011431 59576393073497333577017147)
          ·
            refine ⟨89364589610246000365525721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59576393073497333577017147 89364589610246000365525721)
            ·
              refine ⟨67023442207684500274144291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89364589610246000365525721 67023442207684500274144291)
              ·
                refine ⟨100535163311526750411216437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67023442207684500274144291 100535163311526750411216437)
                ·
                  refine ⟨9425171560455632851051541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100535163311526750411216437 9425171560455632851051541)
                  ·
                    refine ⟨441804916896357789893041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9425171560455632851051541 441804916896357789893041)
                    ·
                      rfl

theorem cell22_1290618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_1290618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290618 prefixEnd_1290618 := by exact prefixLift 1290618
  have htrace : WordTrace (prefixWord ++ tailWord_1290618) baseStart_1290618 baseEnd_1290618 := by
    simpa [prefixWord, tailWord_1290618, baseEnd_1290618] using wordTrace_append hprefix tailTrace_1290618
  have hstable : (prefixWord ++ tailWord_1290618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290618).length < 2 ^ (prefixWord ++ tailWord_1290618).sum := by decide
  have hdescent : baseEnd_1290618 < baseStart_1290618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290650 : List Nat := [3, 1, 1, 4, 1, 3, 1, 8]
def baseStart_1290650 : Nat := 118140960795 + 1290650 * 2 ^ 59
def prefixEnd_1290650 : Nat := 4983230072969 + 3 ^ 40 * 1290650 * 2
def baseEnd_1290650 : Nat := 49090652350035597010327

theorem tailTrace_1290650 : CollatzResearch.WordTrace tailWord_1290650 prefixEnd_1290650 49090652350035597010327 := by
  unfold tailWord_1290650
  simp only [CollatzResearch.WordTrace]
  refine ⟨11768468193550737579035351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31382581849468633544094269 11768468193550737579035351)
  ·
    refine ⟨17652702290326106368553027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11768468193550737579035351 17652702290326106368553027)
    ·
      refine ⟨26479053435489159552829541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17652702290326106368553027 26479053435489159552829541)
      ·
        refine ⟨4964822519154217416155539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26479053435489159552829541 4964822519154217416155539)
        ·
          refine ⟨7447233778731326124233309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4964822519154217416155539 7447233778731326124233309)
          ·
            refine ⟨2792712667024247296587491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7447233778731326124233309 2792712667024247296587491)
            ·
              refine ⟨4189069000536370944881237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2792712667024247296587491 4189069000536370944881237)
              ·
                refine ⟨49090652350035597010327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4189069000536370944881237 49090652350035597010327)
                ·
                  rfl

theorem cell22_1290650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 8].length) (baseStart_1290650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290650 prefixEnd_1290650 := by exact prefixLift 1290650
  have htrace : WordTrace (prefixWord ++ tailWord_1290650) baseStart_1290650 baseEnd_1290650 := by
    simpa [prefixWord, tailWord_1290650, baseEnd_1290650] using wordTrace_append hprefix tailTrace_1290650
  have hstable : (prefixWord ++ tailWord_1290650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290650).length < 2 ^ (prefixWord ++ tailWord_1290650).sum := by decide
  have hdescent : baseEnd_1290650 < baseStart_1290650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290654 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_1290654 : Nat := 118140960795 + 1290654 * 2 ^ 59
def prefixEnd_1290654 : Nat := 4983230072969 + 3 ^ 40 * 1290654 * 2
def baseEnd_1290654 : Nat := 441817240432065695992931

theorem tailTrace_1290654 : CollatzResearch.WordTrace tailWord_1290654 prefixEnd_1290654 441817240432065695992931 := by
  unfold tailWord_1290654
  simp only [CollatzResearch.WordTrace]
  refine ⟨5884252333273557374910877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31382679110792305999524677 5884252333273557374910877)
  ·
    refine ⟨2206594624977584015591579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5884252333273557374910877 2206594624977584015591579)
    ·
      refine ⟨3309891937466376023387369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2206594624977584015591579 3309891937466376023387369)
      ·
        refine ⟨2482418953099782017540527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3309891937466376023387369 2482418953099782017540527)
        ·
          refine ⟨3723628429649673026310791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2482418953099782017540527 3723628429649673026310791)
          ·
            refine ⟨5585442644474509539466187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3723628429649673026310791 5585442644474509539466187)
            ·
              refine ⟨8378163966711764309199281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5585442644474509539466187 8378163966711764309199281)
              ·
                refine ⟨6283622975033823231899461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8378163966711764309199281 6283622975033823231899461)
                ·
                  refine ⟨1178179307818841855981149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6283622975033823231899461 1178179307818841855981149)
                  ·
                    refine ⟨441817240432065695992931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1178179307818841855981149 441817240432065695992931)
                    ·
                      rfl

theorem cell22_1290654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_1290654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290654 prefixEnd_1290654 := by exact prefixLift 1290654
  have htrace : WordTrace (prefixWord ++ tailWord_1290654) baseStart_1290654 baseEnd_1290654 := by
    simpa [prefixWord, tailWord_1290654, baseEnd_1290654] using wordTrace_append hprefix tailTrace_1290654
  have hstable : (prefixWord ++ tailWord_1290654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290654).length < 2 ^ (prefixWord ++ tailWord_1290654).sum := by decide
  have hdescent : baseEnd_1290654 < baseStart_1290654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290665 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 5, 3]
def baseStart_1290665 : Nat := 118140960795 + 1290665 * 2 ^ 59
def prefixEnd_1290665 : Nat := 4983230072969 + 3 ^ 40 * 1290665 * 2
def baseEnd_1290665 : Nat := 441821005956865333967897

theorem tailTrace_1290665 : CollatzResearch.WordTrace tailWord_1290665 prefixEnd_1290665 441821005956865333967897 := by
  unfold tailWord_1290665
  simp only [CollatzResearch.WordTrace]
  refine ⟨47074419869148607877937449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31382946579432405251958299 47074419869148607877937449)
  ·
    refine ⟨35305814901861455908453087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47074419869148607877937449 35305814901861455908453087)
    ·
      refine ⟨52958722352792183862679631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35305814901861455908453087 52958722352792183862679631)
      ·
        refine ⟨79438083529188275794019447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52958722352792183862679631 79438083529188275794019447)
        ·
          refine ⟨119157125293782413691029171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79438083529188275794019447 119157125293782413691029171)
          ·
            refine ⟨178735687940673620536543757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119157125293782413691029171 178735687940673620536543757)
            ·
              refine ⟨67025882977752607701203909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178735687940673620536543757 67025882977752607701203909)
              ·
                refine ⟨12567353058328613943975733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67025882977752607701203909 12567353058328613943975733)
                ·
                  refine ⟨1178189349218307557247725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12567353058328613943975733 1178189349218307557247725)
                  ·
                    refine ⟨441821005956865333967897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1178189349218307557247725 441821005956865333967897)
                    ·
                      rfl

theorem cell22_1290665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 3].length) (baseStart_1290665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290665 prefixEnd_1290665 := by exact prefixLift 1290665
  have htrace : WordTrace (prefixWord ++ tailWord_1290665) baseStart_1290665 baseEnd_1290665 := by
    simpa [prefixWord, tailWord_1290665, baseEnd_1290665] using wordTrace_append hprefix tailTrace_1290665
  have hstable : (prefixWord ++ tailWord_1290665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290665).length < 2 ^ (prefixWord ++ tailWord_1290665).sum := by decide
  have hdescent : baseEnd_1290665 < baseStart_1290665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290669 : List Nat := [1, 5, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_1290669 : Nat := 118140960795 + 1290669 * 2 ^ 59
def prefixEnd_1290669 : Nat := 4983230072969 + 3 ^ 40 * 1290669 * 2
def baseEnd_1290669 : Nat := 441822375238610656867885

theorem tailTrace_1290669 : CollatzResearch.WordTrace tailWord_1290669 prefixEnd_1290669 441822375238610656867885 := by
  unfold tailWord_1290669
  simp only [CollatzResearch.WordTrace]
  refine ⟨47074565761134116561083061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31383043840756077707388707 47074565761134116561083061)
  ·
    refine ⟨4413240540106323427601537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47074565761134116561083061 4413240540106323427601537)
    ·
      refine ⟨3309930405079742570701153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4413240540106323427601537 3309930405079742570701153)
      ·
        refine ⟨2482447803809806928025865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3309930405079742570701153 2482447803809806928025865)
        ·
          refine ⟨1861835852857355196019399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2482447803809806928025865 1861835852857355196019399)
          ·
            refine ⟨2792753779286032794029099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1861835852857355196019399 2792753779286032794029099)
            ·
              refine ⟨4189130668929049191043649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2792753779286032794029099 4189130668929049191043649)
              ·
                refine ⟨3141848001696786893282737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4189130668929049191043649 3141848001696786893282737)
                ·
                  refine ⟨2356386001272590169962053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3141848001696786893282737 2356386001272590169962053)
                  ·
                    refine ⟨441822375238610656867885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2356386001272590169962053 441822375238610656867885)
                    ·
                      rfl

theorem cell22_1290669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_1290669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290669 prefixEnd_1290669 := by exact prefixLift 1290669
  have htrace : WordTrace (prefixWord ++ tailWord_1290669) baseStart_1290669 baseEnd_1290669 := by
    simpa [prefixWord, tailWord_1290669, baseEnd_1290669] using wordTrace_append hprefix tailTrace_1290669
  have hstable : (prefixWord ++ tailWord_1290669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290669).length < 2 ^ (prefixWord ++ tailWord_1290669).sum := by decide
  have hdescent : baseEnd_1290669 < baseStart_1290669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290733 : List Nat := [1, 5, 1, 3, 1, 1, 4, 2, 1, 3]
def baseStart_1290733 : Nat := 118140960795 + 1290733 * 2 ^ 59
def prefixEnd_1290733 : Nat := 4983230072969 + 3 ^ 40 * 1290733 * 2
def baseEnd_1290733 : Nat := 441844283746535823267689

theorem tailTrace_1290733 : CollatzResearch.WordTrace tailWord_1290733 prefixEnd_1290733 441844283746535823267689 := by
  unfold tailWord_1290733
  simp only [CollatzResearch.WordTrace]
  refine ⟨47076900032902255491412853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31384600021934836994275235 47076900032902255491412853)
  ·
    refine ⟨4413459378084586452319955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47076900032902255491412853 4413459378084586452319955)
    ·
      refine ⟨6620189067126879678479933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4413459378084586452319955 6620189067126879678479933)
      ·
        refine ⟨2482570900172579879429975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6620189067126879678479933 2482570900172579879429975)
        ·
          refine ⟨3723856350258869819144963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2482570900172579879429975 3723856350258869819144963)
          ·
            refine ⟨5585784525388304728717445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3723856350258869819144963 5585784525388304728717445)
            ·
              refine ⟨1047334598510307136634521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5585784525388304728717445 1047334598510307136634521)
              ·
                refine ⟨785500948882730352475891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1047334598510307136634521 785500948882730352475891)
                ·
                  refine ⟨1178251423324095528713837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 785500948882730352475891 1178251423324095528713837)
                  ·
                    refine ⟨441844283746535823267689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1178251423324095528713837 441844283746535823267689)
                    ·
                      rfl

theorem cell22_1290733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_1290733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290733 prefixEnd_1290733 := by exact prefixLift 1290733
  have htrace : WordTrace (prefixWord ++ tailWord_1290733) baseStart_1290733 baseEnd_1290733 := by
    simpa [prefixWord, tailWord_1290733, baseEnd_1290733] using wordTrace_append hprefix tailTrace_1290733
  have hstable : (prefixWord ++ tailWord_1290733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290733).length < 2 ^ (prefixWord ++ tailWord_1290733).sum := by decide
  have hdescent : baseEnd_1290733 < baseStart_1290733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290742 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_1290742 : Nat := 118140960795 + 1290742 * 2 ^ 59
def prefixEnd_1290742 : Nat := 4983230072969 + 3 ^ 40 * 1290742 * 2
def baseEnd_1290742 : Nat := 441847364630462799792661

theorem tailTrace_1290742 : CollatzResearch.WordTrace tailWord_1290742 prefixEnd_1290742 441847364630462799792661 := by
  unfold tailWord_1290742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2942326768116853126780655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31384818859913100018993653 2942326768116853126780655)
  ·
    refine ⟨4413490152175279690170983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2942326768116853126780655 4413490152175279690170983)
    ·
      refine ⟨6620235228262919535256475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4413490152175279690170983 6620235228262919535256475)
      ·
        refine ⟨9930352842394379302884713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6620235228262919535256475 9930352842394379302884713)
        ·
          refine ⟨7447764631795784477163535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9930352842394379302884713 7447764631795784477163535)
          ·
            refine ⟨11171646947693676715745303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7447764631795784477163535 11171646947693676715745303)
            ·
              refine ⟨16757470421540515073617955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11171646947693676715745303 16757470421540515073617955)
              ·
                refine ⟨25136205632310772610426933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16757470421540515073617955 25136205632310772610426933)
                ·
                  refine ⟨2356519278029134932227525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25136205632310772610426933 2356519278029134932227525)
                  ·
                    refine ⟨441847364630462799792661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2356519278029134932227525 441847364630462799792661)
                    ·
                      rfl

theorem cell22_1290742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_1290742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290742 prefixEnd_1290742 := by exact prefixLift 1290742
  have htrace : WordTrace (prefixWord ++ tailWord_1290742) baseStart_1290742 baseEnd_1290742 := by
    simpa [prefixWord, tailWord_1290742, baseEnd_1290742] using wordTrace_append hprefix tailTrace_1290742
  have hstable : (prefixWord ++ tailWord_1290742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290742).length < 2 ^ (prefixWord ++ tailWord_1290742).sum := by decide
  have hdescent : baseEnd_1290742 < baseStart_1290742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290776 : List Nat := [2, 1, 2, 3, 3, 3, 2, 1, 1, 4]
def baseStart_1290776 : Nat := 118140960795 + 1290776 * 2 ^ 59
def prefixEnd_1290776 : Nat := 4983230072969 + 3 ^ 40 * 1290776 * 2
def baseEnd_1290776 : Nat := 441859003525298044442557

theorem tailTrace_1290776 : CollatzResearch.WordTrace tailWord_1290776 prefixEnd_1290776 441859003525298044442557 := by
  unfold tailWord_1290776
  simp only [CollatzResearch.WordTrace]
  refine ⟨23539234185873236917614091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31385645581164315890152121 23539234185873236917614091)
  ·
    refine ⟨35308851278809855376421137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23539234185873236917614091 35308851278809855376421137)
    ·
      refine ⟨26481638459107391532315853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35308851278809855376421137 26481638459107391532315853)
      ·
        refine ⟨9930614422165271824618445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26481638459107391532315853 9930614422165271824618445)
        ·
          refine ⟨3723980408311976934231917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9930614422165271824618445 3723980408311976934231917)
          ·
            refine ⟨1396492653116991350336969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3723980408311976934231917 1396492653116991350336969)
            ·
              refine ⟨1047369489837743512752727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1396492653116991350336969 1047369489837743512752727)
              ·
                refine ⟨1571054234756615269129091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1047369489837743512752727 1571054234756615269129091)
                ·
                  refine ⟨2356581352134922903693637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1571054234756615269129091 2356581352134922903693637)
                  ·
                    refine ⟨441859003525298044442557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2356581352134922903693637 441859003525298044442557)
                    ·
                      rfl

theorem cell22_1290776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 1, 4].length) (baseStart_1290776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290776 prefixEnd_1290776 := by exact prefixLift 1290776
  have htrace : WordTrace (prefixWord ++ tailWord_1290776) baseStart_1290776 baseEnd_1290776 := by
    simpa [prefixWord, tailWord_1290776, baseEnd_1290776] using wordTrace_append hprefix tailTrace_1290776
  have hstable : (prefixWord ++ tailWord_1290776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290776).length < 2 ^ (prefixWord ++ tailWord_1290776).sum := by decide
  have hdescent : baseEnd_1290776 < baseStart_1290776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290785 : List Nat := [1, 2, 3, 2, 2, 1, 11]
def baseStart_1290785 : Nat := 118140960795 + 1290785 * 2 ^ 59
def prefixEnd_1290785 : Nat := 4983230072969 + 3 ^ 40 * 1290785 * 2
def baseEnd_1290785 : Nat := 16365262385526852628427

theorem tailTrace_1290785 : CollatzResearch.WordTrace tailWord_1290785 prefixEnd_1290785 16365262385526852628427 := by
  unfold tailWord_1290785
  simp only [CollatzResearch.WordTrace]
  refine ⟨47078796628713868372305809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31385864419142578914870539 47078796628713868372305809)
  ·
    refine ⟨35309097471535401279229357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47078796628713868372305809 35309097471535401279229357)
    ·
      refine ⟨13240911551825775479711009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35309097471535401279229357 13240911551825775479711009)
      ·
        refine ⟨9930683663869331609783257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13240911551825775479711009 9930683663869331609783257)
        ·
          refine ⟨7448012747901998707337443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9930683663869331609783257 7448012747901998707337443)
          ·
            refine ⟨11172019121852998061006165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7448012747901998707337443 11172019121852998061006165)
            ·
              refine ⟨16365262385526852628427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11172019121852998061006165 16365262385526852628427)
              ·
                rfl

theorem cell22_1290785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 11].length) (baseStart_1290785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290785 prefixEnd_1290785 := by exact prefixLift 1290785
  have htrace : WordTrace (prefixWord ++ tailWord_1290785) baseStart_1290785 baseEnd_1290785 := by
    simpa [prefixWord, tailWord_1290785, baseEnd_1290785] using wordTrace_append hprefix tailTrace_1290785
  have hstable : (prefixWord ++ tailWord_1290785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290785).length < 2 ^ (prefixWord ++ tailWord_1290785).sum := by decide
  have hdescent : baseEnd_1290785 < baseStart_1290785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290789 : List Nat := [1, 3, 1, 2, 2, 1, 5, 2, 2, 3]
def baseStart_1290789 : Nat := 118140960795 + 1290789 * 2 ^ 59
def prefixEnd_1290789 : Nat := 4983230072969 + 3 ^ 40 * 1290789 * 2
def baseEnd_1290789 : Nat := 441863453690970343867517

theorem tailTrace_1290789 : CollatzResearch.WordTrace tailWord_1290789 prefixEnd_1290789 441863453690970343867517 := by
  unfold tailWord_1290789
  simp only [CollatzResearch.WordTrace]
  refine ⟨47078942520699377055451421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31385961680466251370300947 47078942520699377055451421)
  ·
    refine ⟨17654603445262266395794283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47078942520699377055451421 17654603445262266395794283)
    ·
      refine ⟨26481905167893399593691425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17654603445262266395794283 26481905167893399593691425)
      ·
        refine ⟨19861428875920049695268569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26481905167893399593691425 19861428875920049695268569)
        ·
          refine ⟨14896071656940037271451427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19861428875920049695268569 14896071656940037271451427)
          ·
            refine ⟨22344107485410055907177141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14896071656940037271451427 22344107485410055907177141)
            ·
              refine ⟨2094760076757192741297857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22344107485410055907177141 2094760076757192741297857)
              ·
                refine ⟨1571070057567894555973393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2094760076757192741297857 1571070057567894555973393)
                ·
                  refine ⟨1178302543175920916980045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1571070057567894555973393 1178302543175920916980045)
                  ·
                    refine ⟨441863453690970343867517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1178302543175920916980045 441863453690970343867517)
                    ·
                      rfl

theorem cell22_1290789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 3].length) (baseStart_1290789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290789 prefixEnd_1290789 := by exact prefixLift 1290789
  have htrace : WordTrace (prefixWord ++ tailWord_1290789) baseStart_1290789 baseEnd_1290789 := by
    simpa [prefixWord, tailWord_1290789, baseEnd_1290789] using wordTrace_append hprefix tailTrace_1290789
  have hstable : (prefixWord ++ tailWord_1290789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290789).length < 2 ^ (prefixWord ++ tailWord_1290789).sum := by decide
  have hdescent : baseEnd_1290789 < baseStart_1290789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290791 : List Nat := [1, 1, 7, 2, 1, 1, 2, 1, 6]
def baseStart_1290791 : Nat := 118140960795 + 1290791 * 2 ^ 59
def prefixEnd_1290791 : Nat := 4983230072969 + 3 ^ 40 * 1290791 * 2
def baseEnd_1290791 : Nat := 147288046110614335105837

theorem tailTrace_1290791 : CollatzResearch.WordTrace tailWord_1290791 prefixEnd_1290791 147288046110614335105837 := by
  unfold tailWord_1290791
  simp only [CollatzResearch.WordTrace]
  refine ⟨47079015466692131397024227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31386010311128087598016151 47079015466692131397024227)
  ·
    refine ⟨70618523200038197095536341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47079015466692131397024227 70618523200038197095536341)
    ·
      refine ⟨1655121637500895244426633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 70618523200038197095536341 1655121637500895244426633)
      ·
        refine ⟨1241341228125671433319975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1655121637500895244426633 1241341228125671433319975)
        ·
          refine ⟨1862011842188507149979963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1241341228125671433319975 1862011842188507149979963)
          ·
            refine ⟨2793017763282760724969945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1862011842188507149979963 2793017763282760724969945)
            ·
              refine ⟨2094763322462070543727459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2793017763282760724969945 2094763322462070543727459)
              ·
                refine ⟨3142144983693105815591189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2094763322462070543727459 3142144983693105815591189)
                ·
                  refine ⟨147288046110614335105837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3142144983693105815591189 147288046110614335105837)
                  ·
                    rfl

theorem cell22_1290791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 6].length) (baseStart_1290791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290791 prefixEnd_1290791 := by exact prefixLift 1290791
  have htrace : WordTrace (prefixWord ++ tailWord_1290791) baseStart_1290791 baseEnd_1290791 := by
    simpa [prefixWord, tailWord_1290791, baseEnd_1290791] using wordTrace_append hprefix tailTrace_1290791
  have hstable : (prefixWord ++ tailWord_1290791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290791).length < 2 ^ (prefixWord ++ tailWord_1290791).sum := by decide
  have hdescent : baseEnd_1290791 < baseStart_1290791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290806 : List Nat := [5, 1, 2, 1, 2, 3, 1, 1, 1, 5]
def baseStart_1290806 : Nat := 118140960795 + 1290806 * 2 ^ 59
def prefixEnd_1290806 : Nat := 4983230072969 + 3 ^ 40 * 1290806 * 2
def baseEnd_1290806 : Nat := 441869273138387966192465

theorem tailTrace_1290806 : CollatzResearch.WordTrace tailWord_1290806 prefixEnd_1290806 441869273138387966192465 := by
  unfold tailWord_1290806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2942472660102361809926267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31386375041091859305880181 2942472660102361809926267)
  ·
    refine ⟨4413708990153542714889401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2942472660102361809926267 4413708990153542714889401)
    ·
      refine ⟨3310281742615157036167051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4413708990153542714889401 3310281742615157036167051)
      ·
        refine ⟨4965422613922735554250577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3310281742615157036167051 4965422613922735554250577)
        ·
          refine ⟨3724066960442051665687933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4965422613922735554250577 3724066960442051665687933)
          ·
            refine ⟨1396525110165769374632975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3724066960442051665687933 1396525110165769374632975)
            ·
              refine ⟨2094787665248654061949463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1396525110165769374632975 2094787665248654061949463)
              ·
                refine ⟨3142181497872981092924195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2094787665248654061949463 3142181497872981092924195)
                ·
                  refine ⟨4713272246809471639386293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3142181497872981092924195 4713272246809471639386293)
                  ·
                    refine ⟨441869273138387966192465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4713272246809471639386293 441869273138387966192465)
                    ·
                      rfl

theorem cell22_1290806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_1290806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290806 prefixEnd_1290806 := by exact prefixLift 1290806
  have htrace : WordTrace (prefixWord ++ tailWord_1290806) baseStart_1290806 baseEnd_1290806 := by
    simpa [prefixWord, tailWord_1290806, baseEnd_1290806] using wordTrace_append hprefix tailTrace_1290806
  have hstable : (prefixWord ++ tailWord_1290806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290806).length < 2 ^ (prefixWord ++ tailWord_1290806).sum := by decide
  have hdescent : baseEnd_1290806 < baseStart_1290806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290864 : List Nat := [2, 1, 1, 1, 7, 1, 1, 3, 5]
def baseStart_1290864 : Nat := 118140960795 + 1290864 * 2 ^ 59
def prefixEnd_1290864 : Nat := 4983230072969 + 3 ^ 40 * 1290864 * 2
def baseEnd_1290864 : Nat := 147296375907898382747429

theorem tailTrace_1290864 : CollatzResearch.WordTrace tailWord_1290864 prefixEnd_1290864 147296375907898382747429 := by
  unfold tailWord_1290864
  simp only [CollatzResearch.WordTrace]
  refine ⟨23540838997713832432215823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31387785330285109909621097 23540838997713832432215823)
  ·
    refine ⟨35311258496570748648323735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23540838997713832432215823 35311258496570748648323735)
    ·
      refine ⟨52966887744856122972485603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35311258496570748648323735 52966887744856122972485603)
      ·
        refine ⟨79450331617284184458728405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52966887744856122972485603 79450331617284184458728405)
        ·
          refine ⟨1862117147280098073251447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 79450331617284184458728405 1862117147280098073251447)
          ·
            refine ⟨2793175720920147109877171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1862117147280098073251447 2793175720920147109877171)
            ·
              refine ⟨4189763581380220664815757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2793175720920147109877171 4189763581380220664815757)
              ·
                refine ⟨1571161343017582749305909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4189763581380220664815757 1571161343017582749305909)
                ·
                  refine ⟨147296375907898382747429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1571161343017582749305909 147296375907898382747429)
                  ·
                    rfl

theorem cell22_1290864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 5].length) (baseStart_1290864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290864 prefixEnd_1290864 := by exact prefixLift 1290864
  have htrace : WordTrace (prefixWord ++ tailWord_1290864) baseStart_1290864 baseEnd_1290864 := by
    simpa [prefixWord, tailWord_1290864, baseEnd_1290864] using wordTrace_append hprefix tailTrace_1290864
  have hstable : (prefixWord ++ tailWord_1290864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290864).length < 2 ^ (prefixWord ++ tailWord_1290864).sum := by decide
  have hdescent : baseEnd_1290864 < baseStart_1290864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290926 : List Nat := [4, 1, 4, 1, 1, 2, 1, 2, 6]
def baseStart_1290926 : Nat := 118140960795 + 1290926 * 2 ^ 59
def prefixEnd_1290926 : Nat := 4983230072969 + 3 ^ 40 * 1290926 * 2
def baseEnd_1290926 : Nat := 147303450530249217730699

theorem tailTrace_1290926 : CollatzResearch.WordTrace tailWord_1290926 prefixEnd_1290926 147303450530249217730699 := by
  unfold tailWord_1290926
  simp only [CollatzResearch.WordTrace]
  refine ⟨5885492415150381181648579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31389292880802032968792421 5885492415150381181648579)
  ·
    refine ⟨8828238622725571772472869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5885492415150381181648579 8828238622725571772472869)
    ·
      refine ⟨1655294741761044707338663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8828238622725571772472869 1655294741761044707338663)
      ·
        refine ⟨2482942112641567061007995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1655294741761044707338663 2482942112641567061007995)
        ·
          refine ⟨3724413168962350591511993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2482942112641567061007995 3724413168962350591511993)
          ·
            refine ⟨2793309876721762943633995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3724413168962350591511993 2793309876721762943633995)
            ·
              refine ⟨4189964815082644415450993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2793309876721762943633995 4189964815082644415450993)
              ·
                refine ⟨3142473611311983311588245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4189964815082644415450993 3142473611311983311588245)
                ·
                  refine ⟨147303450530249217730699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3142473611311983311588245 147303450530249217730699)
                  ·
                    rfl

theorem cell22_1290926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_1290926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290926 prefixEnd_1290926 := by exact prefixLift 1290926
  have htrace : WordTrace (prefixWord ++ tailWord_1290926) baseStart_1290926 baseEnd_1290926 := by
    simpa [prefixWord, tailWord_1290926, baseEnd_1290926] using wordTrace_append hprefix tailTrace_1290926
  have hstable : (prefixWord ++ tailWord_1290926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290926).length < 2 ^ (prefixWord ++ tailWord_1290926).sum := by decide
  have hdescent : baseEnd_1290926 < baseStart_1290926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290958 : List Nat := [4, 1, 1, 1, 3, 4, 1, 2, 2, 3]
def baseStart_1290958 : Nat := 118140960795 + 1290958 * 2 ^ 59
def prefixEnd_1290958 : Nat := 4983230072969 + 3 ^ 40 * 1290958 * 2
def baseEnd_1290958 : Nat := 441921305844710236391999

theorem tailTrace_1290958 : CollatzResearch.WordTrace tailWord_1290958 prefixEnd_1290958 441921305844710236391999 := by
  unfold tailWord_1290958
  simp only [CollatzResearch.WordTrace]
  refine ⟨5885638307135889864794191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31390070971391412612235685 5885638307135889864794191)
  ·
    refine ⟨8828457460703834797191287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5885638307135889864794191 8828457460703834797191287)
    ·
      refine ⟨13242686191055752195786931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8828457460703834797191287 13242686191055752195786931)
      ·
        refine ⟨19864029286583628293680397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13242686191055752195786931 19864029286583628293680397)
        ·
          refine ⟨7449010982468860610130149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19864029286583628293680397 7449010982468860610130149)
          ·
            refine ⟨1396689559212911364399403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7449010982468860610130149 1396689559212911364399403)
            ·
              refine ⟨2095034338819367046599105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1396689559212911364399403 2095034338819367046599105)
              ·
                refine ⟨1571275754114525284949329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2095034338819367046599105 1571275754114525284949329)
                ·
                  refine ⟨1178456815585893963711997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1571275754114525284949329 1178456815585893963711997)
                  ·
                    refine ⟨441921305844710236391999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1178456815585893963711997 441921305844710236391999)
                    ·
                      rfl

theorem cell22_1290958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_1290958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1290958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1290958 prefixEnd_1290958 := by exact prefixLift 1290958
  have htrace : WordTrace (prefixWord ++ tailWord_1290958) baseStart_1290958 baseEnd_1290958 := by
    simpa [prefixWord, tailWord_1290958, baseEnd_1290958] using wordTrace_append hprefix tailTrace_1290958
  have hstable : (prefixWord ++ tailWord_1290958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290958).length < 2 ^ (prefixWord ++ tailWord_1290958).sum := by decide
  have hdescent : baseEnd_1290958 < baseStart_1290958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291029 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 3, 4]
def baseStart_1291029 : Nat := 118140960795 + 1291029 * 2 ^ 59
def prefixEnd_1291029 : Nat := 4983230072969 + 3 ^ 40 * 1291029 * 2
def baseEnd_1291029 : Nat := 441945610595689717866781

theorem tailTrace_1291029 : CollatzResearch.WordTrace tailWord_1291029 prefixEnd_1291029 441945610595689717866781 := by
  unfold tailWord_1291029
  simp only [CollatzResearch.WordTrace]
  refine ⟨47087696039829898044188141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31391797359886598696125427 47087696039829898044188141)
  ·
    refine ⟨17657886014936211766570553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47087696039829898044188141 17657886014936211766570553)
    ·
      refine ⟨13243414511202158824927915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17657886014936211766570553 13243414511202158824927915)
      ·
        refine ⟨19865121766803238237391873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13243414511202158824927915 19865121766803238237391873)
        ·
          refine ⟨14898841325102428678043905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19865121766803238237391873 14898841325102428678043905)
          ·
            refine ⟨11174130993826821508532929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14898841325102428678043905 11174130993826821508532929)
            ·
              refine ⟨8380598245370116131399697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11174130993826821508532929 8380598245370116131399697)
              ·
                refine ⟨6285448684027587098549773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8380598245370116131399697 6285448684027587098549773)
                ·
                  refine ⟨2357043256510345161956165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6285448684027587098549773 2357043256510345161956165)
                  ·
                    refine ⟨441945610595689717866781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2357043256510345161956165 441945610595689717866781)
                    ·
                      rfl

theorem cell22_1291029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_1291029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291029 prefixEnd_1291029 := by exact prefixLift 1291029
  have htrace : WordTrace (prefixWord ++ tailWord_1291029) baseStart_1291029 baseEnd_1291029 := by
    simpa [prefixWord, tailWord_1291029, baseEnd_1291029] using wordTrace_append hprefix tailTrace_1291029
  have hstable : (prefixWord ++ tailWord_1291029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291029).length < 2 ^ (prefixWord ++ tailWord_1291029).sum := by decide
  have hdescent : baseEnd_1291029 < baseStart_1291029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291059 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 3, 5]
def baseStart_1291059 : Nat := 118140960795 + 1291059 * 2 ^ 59
def prefixEnd_1291059 : Nat := 4983230072969 + 3 ^ 40 * 1291059 * 2
def baseEnd_1291059 : Nat := 441955880208779639616689

theorem tailTrace_1291059 : CollatzResearch.WordTrace tailWord_1291059 prefixEnd_1291059 441955880208779639616689 := by
  unfold tailWord_1291059
  simp only [CollatzResearch.WordTrace]
  refine ⟨47088790229721213167780231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31392526819814142111853487 47088790229721213167780231)
  ·
    refine ⟨70633185344581819751670347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47088790229721213167780231 70633185344581819751670347)
    ·
      refine ⟨105949778016872729627505521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70633185344581819751670347 105949778016872729627505521)
      ·
        refine ⟨79462333512654547220629141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105949778016872729627505521 79462333512654547220629141)
        ·
          refine ⟨3724796883405681900966991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79462333512654547220629141 3724796883405681900966991)
          ·
            refine ⟨5587195325108522851450487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3724796883405681900966991 5587195325108522851450487)
            ·
              refine ⟨8380792987662784277175731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5587195325108522851450487 8380792987662784277175731)
              ·
                refine ⟨12571189481494176415763597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8380792987662784277175731 12571189481494176415763597)
                ·
                  refine ⟨4714196055560316155911349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12571189481494176415763597 4714196055560316155911349)
                  ·
                    refine ⟨441955880208779639616689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4714196055560316155911349 441955880208779639616689)
                    ·
                      rfl

theorem cell22_1291059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 5].length) (baseStart_1291059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291059 prefixEnd_1291059 := by exact prefixLift 1291059
  have htrace : WordTrace (prefixWord ++ tailWord_1291059) baseStart_1291059 baseEnd_1291059 := by
    simpa [prefixWord, tailWord_1291059, baseEnd_1291059] using wordTrace_append hprefix tailTrace_1291059
  have hstable : (prefixWord ++ tailWord_1291059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291059).length < 2 ^ (prefixWord ++ tailWord_1291059).sum := by decide
  have hdescent : baseEnd_1291059 < baseStart_1291059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291108 : List Nat := [2, 3, 1, 1, 4, 3, 1, 1, 2, 4]
def baseStart_1291108 : Nat := 118140960795 + 1291108 * 2 ^ 59
def prefixEnd_1291108 : Nat := 4983230072969 + 3 ^ 40 * 1291108 * 2
def baseEnd_1291108 : Nat := 441972653910159845141539

theorem tailTrace_1291108 : CollatzResearch.WordTrace tailWord_1291108 prefixEnd_1291108 441972653910159845141539 := by
  unfold tailWord_1291108
  simp only [CollatzResearch.WordTrace]
  refine ⟨23545288703271847268156989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31393718271029129690875985 23545288703271847268156989)
  ·
    refine ⟨8829483263726942725558871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23545288703271847268156989 8829483263726942725558871)
    ·
      refine ⟨13244224895590414088338307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8829483263726942725558871 13244224895590414088338307)
      ·
        refine ⟨19866337343385621132507461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13244224895590414088338307 19866337343385621132507461)
        ·
          refine ⟨3724938251884803962345149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19866337343385621132507461 3724938251884803962345149)
          ·
            refine ⟨1396851844456801485879431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3724938251884803962345149 1396851844456801485879431)
            ·
              refine ⟨2095277766685202228819147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1396851844456801485879431 2095277766685202228819147)
              ·
                refine ⟨3142916650027803343228721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2095277766685202228819147 3142916650027803343228721)
                ·
                  refine ⟨2357187487520852507421541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3142916650027803343228721 2357187487520852507421541)
                  ·
                    refine ⟨441972653910159845141539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2357187487520852507421541 441972653910159845141539)
                    ·
                      rfl

theorem cell22_1291108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_1291108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291108 prefixEnd_1291108 := by exact prefixLift 1291108
  have htrace : WordTrace (prefixWord ++ tailWord_1291108) baseStart_1291108 baseEnd_1291108 := by
    simpa [prefixWord, tailWord_1291108, baseEnd_1291108] using wordTrace_append hprefix tailTrace_1291108
  have hstable : (prefixWord ++ tailWord_1291108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291108).length < 2 ^ (prefixWord ++ tailWord_1291108).sum := by decide
  have hdescent : baseEnd_1291108 < baseStart_1291108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291271 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 2, 6]
def baseStart_1291271 : Nat := 118140960795 + 1291271 * 2 ^ 59
def prefixEnd_1291271 : Nat := 4983230072969 + 3 ^ 40 * 1291271 * 2
def baseEnd_1291271 : Nat := 442028452141281753316039

theorem tailTrace_1291271 : CollatzResearch.WordTrace tailWord_1291271 prefixEnd_1291271 442028452141281753316039 := by
  unfold tailWord_1291271
  simp only [CollatzResearch.WordTrace]
  refine ⟨47096522504953173374497667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31397681669968782249665111 47096522504953173374497667)
  ·
    refine ⟨70644783757429760061746501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47096522504953173374497667 70644783757429760061746501)
    ·
      refine ⟨13245896954518080011577469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70644783757429760061746501 13245896954518080011577469)
      ·
        refine ⟨4967211357944280004341551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13245896954518080011577469 4967211357944280004341551)
        ·
          refine ⟨7450817036916420006512327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4967211357944280004341551 7450817036916420006512327)
          ·
            refine ⟨11176225555374630009768491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7450817036916420006512327 11176225555374630009768491)
            ·
              refine ⟨16764338333061945014652737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11176225555374630009768491 16764338333061945014652737)
              ·
                refine ⟨12573253749796458760989553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16764338333061945014652737 12573253749796458760989553)
                ·
                  refine ⟨9429940312347344070742165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12573253749796458760989553 9429940312347344070742165)
                  ·
                    refine ⟨442028452141281753316039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9429940312347344070742165 442028452141281753316039)
                    ·
                      rfl

theorem cell22_1291271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_1291271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291271 prefixEnd_1291271 := by exact prefixLift 1291271
  have htrace : WordTrace (prefixWord ++ tailWord_1291271) baseStart_1291271 baseEnd_1291271 := by
    simpa [prefixWord, tailWord_1291271, baseEnd_1291271] using wordTrace_append hprefix tailTrace_1291271
  have hstable : (prefixWord ++ tailWord_1291271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291271).length < 2 ^ (prefixWord ++ tailWord_1291271).sum := by decide
  have hdescent : baseEnd_1291271 < baseStart_1291271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291301 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 4, 5]
def baseStart_1291301 : Nat := 118140960795 + 1291301 * 2 ^ 59
def prefixEnd_1291301 : Nat := 4983230072969 + 3 ^ 40 * 1291301 * 2
def baseEnd_1291301 : Nat := 442038721754371675065947

theorem tailTrace_1291301 : CollatzResearch.WordTrace tailWord_1291301 prefixEnd_1291301 442038721754371675065947 := by
  unfold tailWord_1291301
  simp only [CollatzResearch.WordTrace]
  refine ⟨47097616694844488498089757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31398411129896325665393171 47097616694844488498089757)
  ·
    refine ⟨17661606260566683186783659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47097616694844488498089757 17661606260566683186783659)
    ·
      refine ⟨26492409390850024780175489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17661606260566683186783659 26492409390850024780175489)
      ·
        refine ⟨19869307043137518585131617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26492409390850024780175489 19869307043137518585131617)
        ·
          refine ⟨14901980282353138938848713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19869307043137518585131617 14901980282353138938848713)
          ·
            refine ⟨11176485211764854204136535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14901980282353138938848713 11176485211764854204136535)
            ·
              refine ⟨16764727817647281306204803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11176485211764854204136535 16764727817647281306204803)
              ·
                refine ⟨25147091726470921959307205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16764727817647281306204803 25147091726470921959307205)
                ·
                  refine ⟨4715079698713297867370101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25147091726470921959307205 4715079698713297867370101)
                  ·
                    refine ⟨442038721754371675065947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4715079698713297867370101 442038721754371675065947)
                    ·
                      rfl

theorem cell22_1291301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_1291301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291301 prefixEnd_1291301 := by exact prefixLift 1291301
  have htrace : WordTrace (prefixWord ++ tailWord_1291301) baseStart_1291301 baseEnd_1291301 := by
    simpa [prefixWord, tailWord_1291301, baseEnd_1291301] using wordTrace_append hprefix tailTrace_1291301
  have hstable : (prefixWord ++ tailWord_1291301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291301).length < 2 ^ (prefixWord ++ tailWord_1291301).sum := by decide
  have hdescent : baseEnd_1291301 < baseStart_1291301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291320 : List Nat := [2, 1, 2, 1, 5, 2, 3, 1, 5]
def baseStart_1291320 : Nat := 118140960795 + 1291320 * 2 ^ 59
def prefixEnd_1291320 : Nat := 4983230072969 + 3 ^ 40 * 1291320 * 2
def baseEnd_1291320 : Nat := 147348408614220652946963

theorem tailTrace_1291320 : CollatzResearch.WordTrace tailWord_1291320 prefixEnd_1291320 147348408614220652946963 := by
  unfold tailWord_1291320
  simp only [CollatzResearch.WordTrace]
  refine ⟨23549154840887827371515707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31398873121183769828687609 23549154840887827371515707)
  ·
    refine ⟨35323732261331741057273561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23549154840887827371515707 35323732261331741057273561)
    ·
      refine ⟨26492799195998805792955171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35323732261331741057273561 26492799195998805792955171)
      ·
        refine ⟨39739198793998208689432757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26492799195998805792955171 39739198793998208689432757)
        ·
          refine ⟨3725549886937332064634321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39739198793998208689432757 3725549886937332064634321)
          ·
            refine ⟨2794162415202999048475741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3725549886937332064634321 2794162415202999048475741)
            ·
              refine ⟨1047810905701124643178403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2794162415202999048475741 1047810905701124643178403)
              ·
                refine ⟨1571716358551686964767605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1047810905701124643178403 1571716358551686964767605)
                ·
                  refine ⟨147348408614220652946963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1571716358551686964767605 147348408614220652946963)
                  ·
                    rfl

theorem cell22_1291320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 5].length) (baseStart_1291320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291320 prefixEnd_1291320 := by exact prefixLift 1291320
  have htrace : WordTrace (prefixWord ++ tailWord_1291320) baseStart_1291320 baseEnd_1291320 := by
    simpa [prefixWord, tailWord_1291320, baseEnd_1291320] using wordTrace_append hprefix tailTrace_1291320
  have hstable : (prefixWord ++ tailWord_1291320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291320).length < 2 ^ (prefixWord ++ tailWord_1291320).sum := by decide
  have hdescent : baseEnd_1291320 < baseStart_1291320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291331 : List Nat := [1, 1, 1, 3, 1, 2, 3, 4, 6]
def baseStart_1291331 : Nat := 118140960795 + 1291331 * 2 ^ 59
def prefixEnd_1291331 : Nat := 4983230072969 + 3 ^ 40 * 1291331 * 2
def baseEnd_1291331 : Nat := 147349663789153865605285

theorem tailTrace_1291331 : CollatzResearch.WordTrace tailWord_1291331 prefixEnd_1291331 147349663789153865605285 := by
  unfold tailWord_1291331
  simp only [CollatzResearch.WordTrace]
  refine ⟨47098710884735803621681847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31399140589823869081121231 47098710884735803621681847)
  ·
    refine ⟨70648066327103705432522771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47098710884735803621681847 70648066327103705432522771)
    ·
      refine ⟨105972099490655558148784157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70648066327103705432522771 105972099490655558148784157)
      ·
        refine ⟨39739537308995834305794059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105972099490655558148784157 39739537308995834305794059)
        ·
          refine ⟨59609305963493751458691089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39739537308995834305794059 59609305963493751458691089)
          ·
            refine ⟨44706979472620313594018317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59609305963493751458691089 44706979472620313594018317)
            ·
              refine ⟨16765117302232617597756869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44706979472620313594018317 16765117302232617597756869)
              ·
                refine ⟨3143459494168615799579413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16765117302232617597756869 3143459494168615799579413)
                ·
                  refine ⟨147349663789153865605285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3143459494168615799579413 147349663789153865605285)
                  ·
                    rfl

theorem cell22_1291331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 6].length) (baseStart_1291331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291331 prefixEnd_1291331 := by exact prefixLift 1291331
  have htrace : WordTrace (prefixWord ++ tailWord_1291331) baseStart_1291331 baseEnd_1291331 := by
    simpa [prefixWord, tailWord_1291331, baseEnd_1291331] using wordTrace_append hprefix tailTrace_1291331
  have hstable : (prefixWord ++ tailWord_1291331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291331).length < 2 ^ (prefixWord ++ tailWord_1291331).sum := by decide
  have hdescent : baseEnd_1291331 < baseStart_1291331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291333 : List Nat := [1, 3, 1, 1, 1, 3, 3, 4, 1, 4]
def baseStart_1291333 : Nat := 118140960795 + 1291333 * 2 ^ 59
def prefixEnd_1291333 : Nat := 4983230072969 + 3 ^ 40 * 1291333 * 2
def baseEnd_1291333 : Nat := 442049676008334258265849

theorem tailTrace_1291333 : CollatzResearch.WordTrace tailWord_1291333 prefixEnd_1291333 442049676008334258265849 := by
  unfold tailWord_1291333
  simp only [CollatzResearch.WordTrace]
  refine ⟨47098783830728557963254653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31399189220485705308836435 47098783830728557963254653)
  ·
    refine ⟨17662043936523209236220495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47098783830728557963254653 17662043936523209236220495)
    ·
      refine ⟨26493065904784813854330743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17662043936523209236220495 26493065904784813854330743)
      ·
        refine ⟨39739598857177220781496115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26493065904784813854330743 39739598857177220781496115)
        ·
          refine ⟨59609398285765831172244173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39739598857177220781496115 59609398285765831172244173)
          ·
            refine ⟨22353524357162186689591565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59609398285765831172244173 22353524357162186689591565)
            ·
              refine ⟨8382571633935820008596837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22353524357162186689591565 8382571633935820008596837)
              ·
                refine ⟨1571732181362966251611907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8382571633935820008596837 1571732181362966251611907)
                ·
                  refine ⟨2357598272044449377417861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1571732181362966251611907 2357598272044449377417861)
                  ·
                    refine ⟨442049676008334258265849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2357598272044449377417861 442049676008334258265849)
                    ·
                      rfl

theorem cell22_1291333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_1291333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291333 prefixEnd_1291333 := by exact prefixLift 1291333
  have htrace : WordTrace (prefixWord ++ tailWord_1291333) baseStart_1291333 baseEnd_1291333 := by
    simpa [prefixWord, tailWord_1291333, baseEnd_1291333] using wordTrace_append hprefix tailTrace_1291333
  have hstable : (prefixWord ++ tailWord_1291333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291333).length < 2 ^ (prefixWord ++ tailWord_1291333).sum := by decide
  have hdescent : baseEnd_1291333 < baseStart_1291333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291358 : List Nat := [4, 4, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_1291358 : Nat := 118140960795 + 1291358 * 2 ^ 59
def prefixEnd_1291358 : Nat := 4983230072969 + 3 ^ 40 * 1291358 * 2
def baseEnd_1291358 : Nat := 442058234019242526390773

theorem tailTrace_1291358 : CollatzResearch.WordTrace tailWord_1291358 prefixEnd_1291358 442058234019242526390773 := by
  unfold tailWord_1291358
  simp only [CollatzResearch.WordTrace]
  refine ⟨5887461956954748404114341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31399797103758658155276485 5887461956954748404114341)
  ·
    refine ⟨1103899116929015325771439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5887461956954748404114341 1103899116929015325771439)
    ·
      refine ⟨1655848675393522988657159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1103899116929015325771439 1655848675393522988657159)
      ·
        refine ⟨2483773013090284482985739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1655848675393522988657159 2483773013090284482985739)
        ·
          refine ⟨3725659519635426724478609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2483773013090284482985739 3725659519635426724478609)
          ·
            refine ⟨2794244639726570043358957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3725659519635426724478609 2794244639726570043358957)
            ·
              refine ⟨1047841739897463766259609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2794244639726570043358957 1047841739897463766259609)
              ·
                refine ⟨785881304923097824694707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1047841739897463766259609 785881304923097824694707)
                ·
                  refine ⟨1178821957384646737042061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 785881304923097824694707 1178821957384646737042061)
                  ·
                    refine ⟨442058234019242526390773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1178821957384646737042061 442058234019242526390773)
                    ·
                      rfl

theorem cell22_1291358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_1291358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291358 prefixEnd_1291358 := by exact prefixLift 1291358
  have htrace : WordTrace (prefixWord ++ tailWord_1291358) baseStart_1291358 baseEnd_1291358 := by
    simpa [prefixWord, tailWord_1291358, baseEnd_1291358] using wordTrace_append hprefix tailTrace_1291358
  have hstable : (prefixWord ++ tailWord_1291358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291358).length < 2 ^ (prefixWord ++ tailWord_1291358).sum := by decide
  have hdescent : baseEnd_1291358 < baseStart_1291358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291378 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 4, 4]
def baseStart_1291378 : Nat := 118140960795 + 1291378 * 2 ^ 59
def prefixEnd_1291378 : Nat := 4983230072969 + 3 ^ 40 * 1291378 * 2
def baseEnd_1291378 : Nat := 442065080427969140890711

theorem tailTrace_1291378 : CollatzResearch.WordTrace tailWord_1291378 prefixEnd_1291378 442065080427969140890711 := by
  unfold tailWord_1291378
  simp only [CollatzResearch.WordTrace]
  refine ⟨11775106278891382662160697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31400283410377020432428525 11775106278891382662160697)
  ·
    refine ⟨8831329709168536996620523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11775106278891382662160697 8831329709168536996620523)
    ·
      refine ⟨13246994563752805494930785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8831329709168536996620523 13246994563752805494930785)
      ·
        refine ⟨9935245922814604121198089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13246994563752805494930785 9935245922814604121198089)
        ·
          refine ⟨7451434442110953090898567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9935245922814604121198089 7451434442110953090898567)
          ·
            refine ⟨11177151663166429636347851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7451434442110953090898567 11177151663166429636347851)
            ·
              refine ⟨16765727494749644454521777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11177151663166429636347851 16765727494749644454521777)
              ·
                refine ⟨12574295621062233340891333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16765727494749644454521777 12574295621062233340891333)
                ·
                  refine ⟨2357680428949168751417125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12574295621062233340891333 2357680428949168751417125)
                  ·
                    refine ⟨442065080427969140890711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2357680428949168751417125 442065080427969140890711)
                    ·
                      rfl

theorem cell22_1291378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_1291378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291378 prefixEnd_1291378 := by exact prefixLift 1291378
  have htrace : WordTrace (prefixWord ++ tailWord_1291378) baseStart_1291378 baseEnd_1291378 := by
    simpa [prefixWord, tailWord_1291378, baseEnd_1291378] using wordTrace_append hprefix tailTrace_1291378
  have hstable : (prefixWord ++ tailWord_1291378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291378).length < 2 ^ (prefixWord ++ tailWord_1291378).sum := by decide
  have hdescent : baseEnd_1291378 < baseStart_1291378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291393 : List Nat := [1, 2, 4, 2, 2, 1, 2, 8]
def baseStart_1291393 : Nat := 118140960795 + 1291393 * 2 ^ 59
def prefixEnd_1291393 : Nat := 4983230072969 + 3 ^ 40 * 1291393 * 2
def baseEnd_1291393 : Nat := 49118912803834900196185

theorem tailTrace_1291393 : CollatzResearch.WordTrace tailWord_1291393 prefixEnd_1291393 49118912803834900196185 := by
  unfold tailWord_1291393
  simp only [CollatzResearch.WordTrace]
  refine ⟨47100972210511188210438833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31400648140340792140292555 47100972210511188210438833)
  ·
    refine ⟨35325729157883391157829125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47100972210511188210438833 35325729157883391157829125)
    ·
      refine ⟨6623574217103135842092961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35325729157883391157829125 6623574217103135842092961)
      ·
        refine ⟨4967680662827351881569721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6623574217103135842092961 4967680662827351881569721)
        ·
          refine ⟨3725760497120513911177291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4967680662827351881569721 3725760497120513911177291)
          ·
            refine ⟨5588640745680770866765937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3725760497120513911177291 5588640745680770866765937)
            ·
              refine ⟨4191480559260578150074453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5588640745680770866765937 4191480559260578150074453)
              ·
                refine ⟨49118912803834900196185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4191480559260578150074453 49118912803834900196185)
                ·
                  rfl

theorem cell22_1291393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 8].length) (baseStart_1291393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291393 prefixEnd_1291393 := by exact prefixLift 1291393
  have htrace : WordTrace (prefixWord ++ tailWord_1291393) baseStart_1291393 baseEnd_1291393 := by
    simpa [prefixWord, tailWord_1291393, baseEnd_1291393] using wordTrace_append hprefix tailTrace_1291393
  have hstable : (prefixWord ++ tailWord_1291393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291393).length < 2 ^ (prefixWord ++ tailWord_1291393).sum := by decide
  have hdescent : baseEnd_1291393 < baseStart_1291393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291408 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 7, 3]
def baseStart_1291408 : Nat := 118140960795 + 1291408 * 2 ^ 59
def prefixEnd_1291408 : Nat := 4983230072969 + 3 ^ 40 * 1291408 * 2
def baseEnd_1291408 : Nat := 442075350041059062640619

theorem tailTrace_1291408 : CollatzResearch.WordTrace tailWord_1291408 prefixEnd_1291408 442075350041059062640619 := by
  unfold tailWord_1291408
  simp only [CollatzResearch.WordTrace]
  refine ⟨23550759652728422886117439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31401012870304563848156585 23550759652728422886117439)
  ·
    refine ⟨35326139479092634329176159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23550759652728422886117439 35326139479092634329176159)
    ·
      refine ⟨52989209218638951493764239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35326139479092634329176159 52989209218638951493764239)
      ·
        refine ⟨79483813827958427240646359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52989209218638951493764239 79483813827958427240646359)
        ·
          refine ⟨119225720741937640860969539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79483813827958427240646359 119225720741937640860969539)
          ·
            refine ⟨178838581112906461291454309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119225720741937640860969539 178838581112906461291454309)
            ·
              refine ⟨33532233958669961492147683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 178838581112906461291454309 33532233958669961492147683)
              ·
                refine ⟨50298350938004942238221525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33532233958669961492147683 50298350938004942238221525)
                ·
                  refine ⟨1178867600109490833708317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 50298350938004942238221525 1178867600109490833708317)
                  ·
                    refine ⟨442075350041059062640619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1178867600109490833708317 442075350041059062640619)
                    ·
                      rfl

theorem cell22_1291408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 7, 3].length) (baseStart_1291408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291408 prefixEnd_1291408 := by exact prefixLift 1291408
  have htrace : WordTrace (prefixWord ++ tailWord_1291408) baseStart_1291408 baseEnd_1291408 := by
    simpa [prefixWord, tailWord_1291408, baseEnd_1291408] using wordTrace_append hprefix tailTrace_1291408
  have hstable : (prefixWord ++ tailWord_1291408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291408).length < 2 ^ (prefixWord ++ tailWord_1291408).sum := by decide
  have hdescent : baseEnd_1291408 < baseStart_1291408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291425 : List Nat := [1, 2, 3, 3, 1, 1, 2, 3, 3, 3]
def baseStart_1291425 : Nat := 118140960795 + 1291425 * 2 ^ 59
def prefixEnd_1291425 : Nat := 4983230072969 + 3 ^ 40 * 1291425 * 2
def baseEnd_1291425 : Nat := 442081169488476684965567

theorem tailTrace_1291425 : CollatzResearch.WordTrace tailWord_1291425 prefixEnd_1291425 442081169488476684965567 := by
  unfold tailWord_1291425
  simp only [CollatzResearch.WordTrace]
  refine ⟨47102139346395257675603729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31401426230930171783735819 47102139346395257675603729)
  ·
    refine ⟨35326604509796443256702797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47102139346395257675603729 35326604509796443256702797)
    ·
      refine ⟨13247476691173666221263549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35326604509796443256702797 13247476691173666221263549)
      ·
        refine ⟨4967803759190124832973831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13247476691173666221263549 4967803759190124832973831)
        ·
          refine ⟨7451705638785187249460747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4967803759190124832973831 7451705638785187249460747)
          ·
            refine ⟨11177558458177780874191121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7451705638785187249460747 11177558458177780874191121)
            ·
              refine ⟨8383168843633335655643341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11177558458177780874191121 8383168843633335655643341)
              ·
                refine ⟨3143688316362500870866253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8383168843633335655643341 3143688316362500870866253)
                ·
                  refine ⟨1178883118635937826574845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3143688316362500870866253 1178883118635937826574845)
                  ·
                    refine ⟨442081169488476684965567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1178883118635937826574845 442081169488476684965567)
                    ·
                      rfl

theorem cell22_1291425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_1291425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291425 prefixEnd_1291425 := by exact prefixLift 1291425
  have htrace : WordTrace (prefixWord ++ tailWord_1291425) baseStart_1291425 baseEnd_1291425 := by
    simpa [prefixWord, tailWord_1291425, baseEnd_1291425] using wordTrace_append hprefix tailTrace_1291425
  have hstable : (prefixWord ++ tailWord_1291425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291425).length < 2 ^ (prefixWord ++ tailWord_1291425).sum := by decide
  have hdescent : baseEnd_1291425 < baseStart_1291425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291446 : List Nat := [5, 1, 3, 2, 1, 2, 1, 1, 2, 4]
def baseStart_1291446 : Nat := 118140960795 + 1291446 * 2 ^ 59
def prefixEnd_1291446 : Nat := 4983230072969 + 3 ^ 40 * 1291446 * 2
def baseEnd_1291446 : Nat := 442088358217639630190503

theorem tailTrace_1291446 : CollatzResearch.WordTrace tailWord_1291446 prefixEnd_1291446 442088358217639630190503 := by
  unfold tailWord_1291446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2943931579957448641382387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31401936852879452174745461 2943931579957448641382387)
  ·
    refine ⟨4415897369936172962073581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2943931579957448641382387 4415897369936172962073581)
    ·
      refine ⟨1655961513726064860777593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4415897369936172962073581 1655961513726064860777593)
      ·
        refine ⟨1241971135294548645583195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1655961513726064860777593 1241971135294548645583195)
        ·
          refine ⟨1862956702941822968374793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1241971135294548645583195 1862956702941822968374793)
          ·
            refine ⟨1397217527206367226281095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1862956702941822968374793 1397217527206367226281095)
            ·
              refine ⟨2095826290809550839421643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1397217527206367226281095 2095826290809550839421643)
              ·
                refine ⟨3143739436214326259132465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2095826290809550839421643 3143739436214326259132465)
                ·
                  refine ⟨2357804577160744694349349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3143739436214326259132465 2357804577160744694349349)
                  ·
                    refine ⟨442088358217639630190503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2357804577160744694349349 442088358217639630190503)
                    ·
                      rfl

theorem cell22_1291446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_1291446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291446 prefixEnd_1291446 := by exact prefixLift 1291446
  have htrace : WordTrace (prefixWord ++ tailWord_1291446) baseStart_1291446 baseEnd_1291446 := by
    simpa [prefixWord, tailWord_1291446, baseEnd_1291446] using wordTrace_append hprefix tailTrace_1291446
  have hstable : (prefixWord ++ tailWord_1291446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291446).length < 2 ^ (prefixWord ++ tailWord_1291446).sum := by decide
  have hdescent : baseEnd_1291446 < baseStart_1291446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291513 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 1, 6]
def baseStart_1291513 : Nat := 118140960795 + 1291513 * 2 ^ 59
def prefixEnd_1291513 : Nat := 4983230072969 + 3 ^ 40 * 1291513 * 2
def baseEnd_1291513 : Nat := 442111293686873788765297

theorem tailTrace_1291513 : CollatzResearch.WordTrace tailWord_1291513 prefixEnd_1291513 442111293686873788765297 := by
  unfold tailWord_1291513
  simp only [CollatzResearch.WordTrace]
  refine ⟨47105348970076448704807193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31403565980050965803204795 47105348970076448704807193)
  ·
    refine ⟨35329011727557336528605395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47105348970076448704807193 35329011727557336528605395)
    ·
      refine ⟨52993517591336004792908093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35329011727557336528605395 52993517591336004792908093)
      ·
        refine ⟨19872569096751001797340535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52993517591336004792908093 19872569096751001797340535)
        ·
          refine ⟨29808853645126502696010803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19872569096751001797340535 29808853645126502696010803)
          ·
            refine ⟨44713280467689754044016205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29808853645126502696010803 44713280467689754044016205)
            ·
              refine ⟨16767480175383657766506077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44713280467689754044016205 16767480175383657766506077)
              ·
                refine ⟨6287805065768871662439779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16767480175383657766506077 6287805065768871662439779)
                ·
                  refine ⟨9431707598653307493659669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6287805065768871662439779 9431707598653307493659669)
                  ·
                    refine ⟨442111293686873788765297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9431707598653307493659669 442111293686873788765297)
                    ·
                      rfl

theorem cell22_1291513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_1291513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291513 prefixEnd_1291513 := by exact prefixLift 1291513
  have htrace : WordTrace (prefixWord ++ tailWord_1291513) baseStart_1291513 baseEnd_1291513 := by
    simpa [prefixWord, tailWord_1291513, baseEnd_1291513] using wordTrace_append hprefix tailTrace_1291513
  have hstable : (prefixWord ++ tailWord_1291513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291513).length < 2 ^ (prefixWord ++ tailWord_1291513).sum := by decide
  have hdescent : baseEnd_1291513 < baseStart_1291513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291534 : List Nat := [4, 1, 1, 2, 1, 4, 3, 2, 4]
def baseStart_1291534 : Nat := 118140960795 + 1291534 * 2 ^ 59
def prefixEnd_1291534 : Nat := 4983230072969 + 3 ^ 40 * 1291534 * 2
def baseEnd_1291534 : Nat := 147372827472012244663411

theorem tailTrace_1291534 : CollatzResearch.WordTrace tailWord_1291534 prefixEnd_1291534 147372827472012244663411 := by
  unfold tailWord_1291534
  simp only [CollatzResearch.WordTrace]
  refine ⟨5888264362875046161415207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31404076602000246194214437 5888264362875046161415207)
  ·
    refine ⟨8832396544312569242122811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5888264362875046161415207 8832396544312569242122811)
    ·
      refine ⟨13248594816468853863184217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8832396544312569242122811 13248594816468853863184217)
      ·
        refine ⟨9936446112351640397388163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13248594816468853863184217 9936446112351640397388163)
        ·
          refine ⟨14904669168527460596082245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9936446112351640397388163 14904669168527460596082245)
          ·
            refine ⟨2794625469098898861765421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14904669168527460596082245 2794625469098898861765421)
            ·
              refine ⟨1047984550912087073162033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2794625469098898861765421 1047984550912087073162033)
              ·
                refine ⟨785988413184065304871525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1047984550912087073162033 785988413184065304871525)
                ·
                  refine ⟨147372827472012244663411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 785988413184065304871525 147372827472012244663411)
                  ·
                    rfl

theorem cell22_1291534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_1291534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291534 prefixEnd_1291534 := by exact prefixLift 1291534
  have htrace : WordTrace (prefixWord ++ tailWord_1291534) baseStart_1291534 baseEnd_1291534 := by
    simpa [prefixWord, tailWord_1291534, baseEnd_1291534] using wordTrace_append hprefix tailTrace_1291534
  have hstable : (prefixWord ++ tailWord_1291534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291534).length < 2 ^ (prefixWord ++ tailWord_1291534).sum := by decide
  have hdescent : baseEnd_1291534 < baseStart_1291534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291549 : List Nat := [1, 4, 2, 3, 1, 2, 1, 3, 2, 3]
def baseStart_1291549 : Nat := 118140960795 + 1291549 * 2 ^ 59
def prefixEnd_1291549 : Nat := 4983230072969 + 3 ^ 40 * 1291549 * 2
def baseEnd_1291549 : Nat := 442123617222581694865187

theorem tailTrace_1291549 : CollatzResearch.WordTrace tailWord_1291549 prefixEnd_1291549 442123617222581694865187 := by
  unfold tailWord_1291549
  simp only [CollatzResearch.WordTrace]
  refine ⟨47106661997946026853117701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31404441331964017902078467 47106661997946026853117701)
  ·
    refine ⟨8832499124614880034959569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47106661997946026853117701 8832499124614880034959569)
    ·
      refine ⟨6624374343461160026219677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8832499124614880034959569 6624374343461160026219677)
      ·
        refine ⟨2484140378797935009832379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6624374343461160026219677 2484140378797935009832379)
        ·
          refine ⟨3726210568196902514748569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2484140378797935009832379 3726210568196902514748569)
          ·
            refine ⟨2794657926147676886061427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3726210568196902514748569 2794657926147676886061427)
            ·
              refine ⟨4191986889221515329092141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2794657926147676886061427 4191986889221515329092141)
              ·
                refine ⟨1571995083458068248409553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4191986889221515329092141 1571995083458068248409553)
                ·
                  refine ⟨1178996312593551186307165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1571995083458068248409553 1178996312593551186307165)
                  ·
                    refine ⟨442123617222581694865187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1178996312593551186307165 442123617222581694865187)
                    ·
                      rfl

theorem cell22_1291549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_1291549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291549 prefixEnd_1291549 := by exact prefixLift 1291549
  have htrace : WordTrace (prefixWord ++ tailWord_1291549) baseStart_1291549 baseEnd_1291549 := by
    simpa [prefixWord, tailWord_1291549, baseEnd_1291549] using wordTrace_append hprefix tailTrace_1291549
  have hstable : (prefixWord ++ tailWord_1291549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291549).length < 2 ^ (prefixWord ++ tailWord_1291549).sum := by decide
  have hdescent : baseEnd_1291549 < baseStart_1291549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291605 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 1, 7]
def baseStart_1291605 : Nat := 118140960795 + 1291605 * 2 ^ 59
def prefixEnd_1291605 : Nat := 4983230072969 + 3 ^ 40 * 1291605 * 2
def baseEnd_1291605 : Nat := 442142787167016215465015

theorem tailTrace_1291605 : CollatzResearch.WordTrace tailWord_1291605 prefixEnd_1291605 442142787167016215465015 := by
  unfold tailWord_1291605
  simp only [CollatzResearch.WordTrace]
  refine ⟨47108704485743148417156269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31405802990495432278104179 47108704485743148417156269)
  ·
    refine ⟨17665764182153680656433601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47108704485743148417156269 17665764182153680656433601)
    ·
      refine ⟨13249323136615260492325201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17665764182153680656433601 13249323136615260492325201)
      ·
        refine ⟨9936992352461445369243901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13249323136615260492325201 9936992352461445369243901)
        ·
          refine ⟨3726372132173042013466463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9936992352461445369243901 3726372132173042013466463)
          ·
            refine ⟨5589558198259563020199695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3726372132173042013466463 5589558198259563020199695)
            ·
              refine ⟨8384337297389344530299543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5589558198259563020199695 8384337297389344530299543)
              ·
                refine ⟨12576505946084016795449315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8384337297389344530299543 12576505946084016795449315)
                ·
                  refine ⟨18864758919126025193173973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12576505946084016795449315 18864758919126025193173973)
                  ·
                    refine ⟨442142787167016215465015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18864758919126025193173973 442142787167016215465015)
                    ·
                      rfl

theorem cell22_1291605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_1291605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291605 prefixEnd_1291605 := by exact prefixLift 1291605
  have htrace : WordTrace (prefixWord ++ tailWord_1291605) baseStart_1291605 baseEnd_1291605 := by
    simpa [prefixWord, tailWord_1291605, baseEnd_1291605] using wordTrace_append hprefix tailTrace_1291605
  have hstable : (prefixWord ++ tailWord_1291605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291605).length < 2 ^ (prefixWord ++ tailWord_1291605).sum := by decide
  have hdescent : baseEnd_1291605 < baseStart_1291605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291652 : List Nat := [2, 3, 2, 1, 1, 4, 2, 1, 6]
def baseStart_1291652 : Nat := 118140960795 + 1291652 * 2 ^ 59
def prefixEnd_1291652 : Nat := 4983230072969 + 3 ^ 40 * 1291652 * 2
def baseEnd_1291652 : Nat := 147386292075841253179957

theorem tailTrace_1291652 : CollatzResearch.WordTrace tailWord_1291652 prefixEnd_1291652 147386292075841253179957 := by
  unfold tailWord_1291652
  simp only [CollatzResearch.WordTrace]
  refine ⟨23555209358286437722058605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31406945811048583629411473 23555209358286437722058605)
  ·
    refine ⟨8833203509357414145771977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23555209358286437722058605 8833203509357414145771977)
    ·
      refine ⟨6624902632018060609328983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8833203509357414145771977 6624902632018060609328983)
      ·
        refine ⟨9937353948027090913993475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6624902632018060609328983 9937353948027090913993475)
        ·
          refine ⟨14906030922040636370990213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9937353948027090913993475 14906030922040636370990213)
          ·
            refine ⟨2794880797882619319560665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14906030922040636370990213 2794880797882619319560665)
            ·
              refine ⟨2096160598411964489670499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2794880797882619319560665 2096160598411964489670499)
              ·
                refine ⟨3144240897617946734505749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2096160598411964489670499 3144240897617946734505749)
                ·
                  refine ⟨147386292075841253179957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3144240897617946734505749 147386292075841253179957)
                  ·
                    rfl

theorem cell22_1291652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_1291652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291652 prefixEnd_1291652 := by exact prefixLift 1291652
  have htrace : WordTrace (prefixWord ++ tailWord_1291652) baseStart_1291652 baseEnd_1291652 := by
    simpa [prefixWord, tailWord_1291652, baseEnd_1291652] using wordTrace_append hprefix tailTrace_1291652
  have hstable : (prefixWord ++ tailWord_1291652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291652).length < 2 ^ (prefixWord ++ tailWord_1291652).sum := by decide
  have hdescent : baseEnd_1291652 < baseStart_1291652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291665 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 4, 4]
def baseStart_1291665 : Nat := 118140960795 + 1291665 * 2 ^ 59
def prefixEnd_1291665 : Nat := 4983230072969 + 3 ^ 40 * 1291665 * 2
def baseEnd_1291665 : Nat := 442163326393196058964831

theorem tailTrace_1291665 : CollatzResearch.WordTrace tailWord_1291665 prefixEnd_1291665 442163326393196058964831 := by
  unfold tailWord_1291665
  simp only [CollatzResearch.WordTrace]
  refine ⟨47110892865525778664340449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31407261910350519109560299 47110892865525778664340449)
  ·
    refine ⟨35333169649144333998255337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47110892865525778664340449 35333169649144333998255337)
    ·
      refine ⟨26499877236858250498691503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35333169649144333998255337 26499877236858250498691503)
      ·
        refine ⟨39749815855287375748037255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26499877236858250498691503 39749815855287375748037255)
        ·
          refine ⟨59624723782931063622055883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39749815855287375748037255 59624723782931063622055883)
          ·
            refine ⟨89437085674396595433083825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59624723782931063622055883 89437085674396595433083825)
            ·
              refine ⟨67077814255797446574812869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89437085674396595433083825 67077814255797446574812869)
              ·
                refine ⟨12577090172962021232777413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67077814255797446574812869 12577090172962021232777413)
                ·
                  refine ⟨2358204407430378981145765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12577090172962021232777413 2358204407430378981145765)
                  ·
                    refine ⟨442163326393196058964831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2358204407430378981145765 442163326393196058964831)
                    ·
                      rfl

theorem cell22_1291665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_1291665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291665 prefixEnd_1291665 := by exact prefixLift 1291665
  have htrace : WordTrace (prefixWord ++ tailWord_1291665) baseStart_1291665 baseEnd_1291665 := by
    simpa [prefixWord, tailWord_1291665, baseEnd_1291665] using wordTrace_append hprefix tailTrace_1291665
  have hstable : (prefixWord ++ tailWord_1291665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291665).length < 2 ^ (prefixWord ++ tailWord_1291665).sum := by decide
  have hdescent : baseEnd_1291665 < baseStart_1291665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291680 : List Nat := [2, 1, 1, 4, 1, 2, 3, 8]
def baseStart_1291680 : Nat := 118140960795 + 1291680 * 2 ^ 59
def prefixEnd_1291680 : Nat := 4983230072969 + 3 ^ 40 * 1291680 * 2
def baseEnd_1291680 : Nat := 49129829022193446648865

theorem tailTrace_1291680 : CollatzResearch.WordTrace tailWord_1291680 prefixEnd_1291680 49129829022193446648865 := by
  unfold tailWord_1291680
  simp only [CollatzResearch.WordTrace]
  refine ⟨23555719980235718113068247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31407626640314290817424329 23555719980235718113068247)
  ·
    refine ⟨35333579970353577169602371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23555719980235718113068247 35333579970353577169602371)
    ·
      refine ⟨53000369955530365754403557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35333579970353577169602371 53000369955530365754403557)
      ·
        refine ⟨9937569366661943578950667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53000369955530365754403557 9937569366661943578950667)
        ·
          refine ⟨14906354049992915368426001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9937569366661943578950667 14906354049992915368426001)
          ·
            refine ⟨11179765537494686526319501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14906354049992915368426001 11179765537494686526319501)
            ·
              refine ⟨4192412076560507447369813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11179765537494686526319501 4192412076560507447369813)
              ·
                refine ⟨49129829022193446648865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4192412076560507447369813 49129829022193446648865)
                ·
                  rfl

theorem cell22_1291680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 8].length) (baseStart_1291680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291680 prefixEnd_1291680 := by exact prefixLift 1291680
  have htrace : WordTrace (prefixWord ++ tailWord_1291680) baseStart_1291680 baseEnd_1291680 := by
    simpa [prefixWord, tailWord_1291680, baseEnd_1291680] using wordTrace_append hprefix tailTrace_1291680
  have hstable : (prefixWord ++ tailWord_1291680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291680).length < 2 ^ (prefixWord ++ tailWord_1291680).sum := by decide
  have hdescent : baseEnd_1291680 < baseStart_1291680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291682 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_1291682 : Nat := 118140960795 + 1291682 * 2 ^ 59
def prefixEnd_1291682 : Nat := 4983230072969 + 3 ^ 40 * 1291682 * 2
def baseEnd_1291682 : Nat := 442169145840613681289779

theorem tailTrace_1291682 : CollatzResearch.WordTrace tailWord_1291682 prefixEnd_1291682 442169145840613681289779 := by
  unfold tailWord_1291682
  simp only [CollatzResearch.WordTrace]
  refine ⟨11777878226616047641927325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31407675270976127045139533 11777878226616047641927325)
  ·
    refine ⟨4416704334981017865722747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11777878226616047641927325 4416704334981017865722747)
    ·
      refine ⟨6625056502471526798584121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4416704334981017865722747 6625056502471526798584121)
      ·
        refine ⟨4968792376853645098938091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6625056502471526798584121 4968792376853645098938091)
        ·
          refine ⟨7453188565280467648407137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4968792376853645098938091 7453188565280467648407137)
          ·
            refine ⟨5589891423960350736305353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7453188565280467648407137 5589891423960350736305353)
            ·
              refine ⟨4192418567970263052229015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5589891423960350736305353 4192418567970263052229015)
              ·
                refine ⟨6288627851955394578343523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4192418567970263052229015 6288627851955394578343523)
                ·
                  refine ⟨9432941777933091867515285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6288627851955394578343523 9432941777933091867515285)
                  ·
                    refine ⟨442169145840613681289779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9432941777933091867515285 442169145840613681289779)
                    ·
                      rfl

theorem cell22_1291682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_1291682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291682 prefixEnd_1291682 := by exact prefixLift 1291682
  have htrace : WordTrace (prefixWord ++ tailWord_1291682) baseStart_1291682 baseEnd_1291682 := by
    simpa [prefixWord, tailWord_1291682, baseEnd_1291682] using wordTrace_append hprefix tailTrace_1291682
  have hstable : (prefixWord ++ tailWord_1291682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291682).length < 2 ^ (prefixWord ++ tailWord_1291682).sum := by decide
  have hdescent : baseEnd_1291682 < baseStart_1291682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291772 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 3, 4]
def baseStart_1291772 : Nat := 118140960795 + 1291772 * 2 ^ 59
def prefixEnd_1291772 : Nat := 4983230072969 + 3 ^ 40 * 1291772 * 2
def baseEnd_1291772 : Nat := 442199954679883446539503

theorem tailTrace_1291772 : CollatzResearch.WordTrace tailWord_1291772 prefixEnd_1291772 442199954679883446539503 := by
  unfold tailWord_1291772
  simp only [CollatzResearch.WordTrace]
  refine ⟨23557397738069067969242785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31409863650758757292323713 23557397738069067969242785)
  ·
    refine ⟨17668048303551800976932089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23557397738069067969242785 17668048303551800976932089)
    ·
      refine ⟨13251036227663850732699067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17668048303551800976932089 13251036227663850732699067)
      ·
        refine ⟨19876554341495776099048601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13251036227663850732699067 19876554341495776099048601)
        ·
          refine ⟨14907415756121832074286451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19876554341495776099048601 14907415756121832074286451)
          ·
            refine ⟨22361123634182748111429677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14907415756121832074286451 22361123634182748111429677)
            ·
              refine ⟨8385421362818530541786129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22361123634182748111429677 8385421362818530541786129)
              ·
                refine ⟨6289066022113897906339597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8385421362818530541786129 6289066022113897906339597)
                ·
                  refine ⟨2358399758292711714877349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6289066022113897906339597 2358399758292711714877349)
                  ·
                    refine ⟨442199954679883446539503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2358399758292711714877349 442199954679883446539503)
                    ·
                      rfl

theorem cell22_1291772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_1291772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291772 prefixEnd_1291772 := by exact prefixLift 1291772
  have htrace : WordTrace (prefixWord ++ tailWord_1291772) baseStart_1291772 baseEnd_1291772 := by
    simpa [prefixWord, tailWord_1291772, baseEnd_1291772] using wordTrace_append hprefix tailTrace_1291772
  have hstable : (prefixWord ++ tailWord_1291772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291772).length < 2 ^ (prefixWord ++ tailWord_1291772).sum := by decide
  have hdescent : baseEnd_1291772 < baseStart_1291772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291836 : List Nat := [2, 2, 2, 2, 4, 2, 1, 1, 1, 5]
def baseStart_1291836 : Nat := 118140960795 + 1291836 * 2 ^ 59
def prefixEnd_1291836 : Nat := 4983230072969 + 3 ^ 40 * 1291836 * 2
def baseEnd_1291836 : Nat := 442221863187808612939307

theorem tailTrace_1291836 : CollatzResearch.WordTrace tailWord_1291836 prefixEnd_1291836 442221863187808612939307 := by
  unfold tailWord_1291836
  simp only [CollatzResearch.WordTrace]
  refine ⟨23558564873953137434407681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31411419831937516579210241 23558564873953137434407681)
  ·
    refine ⟨17668923655464853075805761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23558564873953137434407681 17668923655464853075805761)
    ·
      refine ⟨13251692741598639806854321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17668923655464853075805761 13251692741598639806854321)
      ·
        refine ⟨9938769556198979855140741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13251692741598639806854321 9938769556198979855140741)
        ·
          refine ⟨1863519291787308722838889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9938769556198979855140741 1863519291787308722838889)
          ·
            refine ⟨1397639468840481542129167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1863519291787308722838889 1397639468840481542129167)
            ·
              refine ⟨2096459203260722313193751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1397639468840481542129167 2096459203260722313193751)
              ·
                refine ⟨3144688804891083469790627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2096459203260722313193751 3144688804891083469790627)
                ·
                  refine ⟨4717033207336625204685941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3144688804891083469790627 4717033207336625204685941)
                  ·
                    refine ⟨442221863187808612939307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4717033207336625204685941 442221863187808612939307)
                    ·
                      rfl

theorem cell22_1291836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_1291836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291836 prefixEnd_1291836 := by exact prefixLift 1291836
  have htrace : WordTrace (prefixWord ++ tailWord_1291836) baseStart_1291836 baseEnd_1291836 := by
    simpa [prefixWord, tailWord_1291836, baseEnd_1291836] using wordTrace_append hprefix tailTrace_1291836
  have hstable : (prefixWord ++ tailWord_1291836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291836).length < 2 ^ (prefixWord ++ tailWord_1291836).sum := by decide
  have hdescent : baseEnd_1291836 < baseStart_1291836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291881 : List Nat := [1, 2, 1, 1, 1, 4, 2, 6, 1, 3]
def baseStart_1291881 : Nat := 118140960795 + 1291881 * 2 ^ 59
def prefixEnd_1291881 : Nat := 4983230072969 + 3 ^ 40 * 1291881 * 2
def baseEnd_1291881 : Nat := 442237267607443495564169

theorem tailTrace_1291881 : CollatzResearch.WordTrace tailWord_1291881 prefixEnd_1291881 442237267607443495564169 := by
  unfold tailWord_1291881
  simp only [CollatzResearch.WordTrace]
  refine ⟨47118771032743247554203497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31412514021828831702802331 47118771032743247554203497)
  ·
    refine ⟨35339078274557435665652623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47118771032743247554203497 35339078274557435665652623)
    ·
      refine ⟨53008617411836153498478935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35339078274557435665652623 53008617411836153498478935)
      ·
        refine ⟨79512926117754230247718403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53008617411836153498478935 79512926117754230247718403)
        ·
          refine ⟨119269389176631345371577605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79512926117754230247718403 119269389176631345371577605)
          ·
            refine ⟨22363010470618377257170801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119269389176631345371577605 22363010470618377257170801)
            ·
              refine ⟨16772257852963782942878101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22363010470618377257170801 16772257852963782942878101)
              ·
                refine ⟨786199586857677325447411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16772257852963782942878101 786199586857677325447411)
                ·
                  refine ⟨1179299380286515988171117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 786199586857677325447411 1179299380286515988171117)
                  ·
                    refine ⟨442237267607443495564169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1179299380286515988171117 442237267607443495564169)
                    ·
                      rfl

theorem cell22_1291881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 1, 3].length) (baseStart_1291881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291881 prefixEnd_1291881 := by exact prefixLift 1291881
  have htrace : WordTrace (prefixWord ++ tailWord_1291881) baseStart_1291881 baseEnd_1291881 := by
    simpa [prefixWord, tailWord_1291881, baseEnd_1291881] using wordTrace_append hprefix tailTrace_1291881
  have hstable : (prefixWord ++ tailWord_1291881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291881).length < 2 ^ (prefixWord ++ tailWord_1291881).sum := by decide
  have hdescent : baseEnd_1291881 < baseStart_1291881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291932 : List Nat := [2, 2, 3, 2, 3, 2, 2, 2, 1, 3]
def baseStart_1291932 : Nat := 118140960795 + 1291932 * 2 ^ 59
def prefixEnd_1291932 : Nat := 4983230072969 + 3 ^ 40 * 1291932 * 2
def baseEnd_1291932 : Nat := 442254725949696362539013

theorem tailTrace_1291932 : CollatzResearch.WordTrace tailWord_1291932 prefixEnd_1291932 442254725949696362539013 := by
  unfold tailWord_1291932
  simp only [CollatzResearch.WordTrace]
  refine ⟨23560315577779241632155025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31413754103705655509540033 23560315577779241632155025)
  ·
    refine ⟨17670236683334431224116269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23560315577779241632155025 17670236683334431224116269)
    ·
      refine ⟨6626338756250411709043601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17670236683334431224116269 6626338756250411709043601)
      ·
        refine ⟨4969754067187808781782701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6626338756250411709043601 4969754067187808781782701)
        ·
          refine ⟨1863657775195428293168513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4969754067187808781782701 1863657775195428293168513)
          ·
            refine ⟨1397743331396571219876385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1863657775195428293168513 1397743331396571219876385)
            ·
              refine ⟨1048307498547428414907289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1397743331396571219876385 1048307498547428414907289)
              ·
                refine ⟨786230623910571311180467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1048307498547428414907289 786230623910571311180467)
                ·
                  refine ⟨1179345935865856966770701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 786230623910571311180467 1179345935865856966770701)
                  ·
                    refine ⟨442254725949696362539013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1179345935865856966770701 442254725949696362539013)
                    ·
                      rfl

theorem cell22_1291932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_1291932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291932 prefixEnd_1291932 := by exact prefixLift 1291932
  have htrace : WordTrace (prefixWord ++ tailWord_1291932) baseStart_1291932 baseEnd_1291932 := by
    simpa [prefixWord, tailWord_1291932, baseEnd_1291932] using wordTrace_append hprefix tailTrace_1291932
  have hstable : (prefixWord ++ tailWord_1291932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291932).length < 2 ^ (prefixWord ++ tailWord_1291932).sum := by decide
  have hdescent : baseEnd_1291932 < baseStart_1291932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291954 : List Nat := [3, 2, 1, 1, 1, 2, 3, 3, 1, 5]
def baseStart_1291954 : Nat := 118140960795 + 1291954 * 2 ^ 59
def prefixEnd_1291954 : Nat := 4983230072969 + 3 ^ 40 * 1291954 * 2
def baseEnd_1291954 : Nat := 442262256999295638488945

theorem tailTrace_1291954 : CollatzResearch.WordTrace tailWord_1291954 prefixEnd_1291954 442262256999295638488945 := by
  unfold tailWord_1291954
  simp only [CollatzResearch.WordTrace]
  refine ⟨11780358390369695255402729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31414289040985854014407277 11780358390369695255402729)
  ·
    refine ⟨8835268792777271441552047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11780358390369695255402729 8835268792777271441552047)
    ·
      refine ⟨13252903189165907162328071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8835268792777271441552047 13252903189165907162328071)
      ·
        refine ⟨19879354783748860743492107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13252903189165907162328071 19879354783748860743492107)
        ·
          refine ⟨29819032175623291115238161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19879354783748860743492107 29819032175623291115238161)
          ·
            refine ⟨22364274131717468336428621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29819032175623291115238161 22364274131717468336428621)
            ·
              refine ⟨8386602799394050626160733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22364274131717468336428621 8386602799394050626160733)
              ·
                refine ⟨3144976049772768984810275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8386602799394050626160733 3144976049772768984810275)
                ·
                  refine ⟨4717464074659153477215413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3144976049772768984810275 4717464074659153477215413)
                  ·
                    refine ⟨442262256999295638488945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4717464074659153477215413 442262256999295638488945)
                    ·
                      rfl

theorem cell22_1291954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_1291954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291954 prefixEnd_1291954 := by exact prefixLift 1291954
  have htrace : WordTrace (prefixWord ++ tailWord_1291954) baseStart_1291954 baseEnd_1291954 := by
    simpa [prefixWord, tailWord_1291954, baseEnd_1291954] using wordTrace_append hprefix tailTrace_1291954
  have hstable : (prefixWord ++ tailWord_1291954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291954).length < 2 ^ (prefixWord ++ tailWord_1291954).sum := by decide
  have hdescent : baseEnd_1291954 < baseStart_1291954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291958 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_1291958 : Nat := 118140960795 + 1291958 * 2 ^ 59
def prefixEnd_1291958 : Nat := 4983230072969 + 3 ^ 40 * 1291958 * 2
def baseEnd_1291958 : Nat := 442263626281040961388933

theorem tailTrace_1291958 : CollatzResearch.WordTrace tailWord_1291958 prefixEnd_1291958 442263626281040961388933 := by
  unfold tailWord_1291958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2945098715841518106547283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31414386302309526469837685 2945098715841518106547283)
  ·
    refine ⟨4417648073762277159820925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2945098715841518106547283 4417648073762277159820925)
    ·
      refine ⟨1656618027660853934932847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4417648073762277159820925 1656618027660853934932847)
      ·
        refine ⟨2484927041491280902399271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1656618027660853934932847 2484927041491280902399271)
        ·
          refine ⟨3727390562236921353598907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2484927041491280902399271 3727390562236921353598907)
          ·
            refine ⟨5591085843355382030398361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3727390562236921353598907 5591085843355382030398361)
            ·
              refine ⟨4193314382516536522798771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5591085843355382030398361 4193314382516536522798771)
              ·
                refine ⟨6289971573774804784198157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4193314382516536522798771 6289971573774804784198157)
                ·
                  refine ⟨2358739340165551794074309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6289971573774804784198157 2358739340165551794074309)
                  ·
                    refine ⟨442263626281040961388933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2358739340165551794074309 442263626281040961388933)
                    ·
                      rfl

theorem cell22_1291958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_1291958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291958 prefixEnd_1291958 := by exact prefixLift 1291958
  have htrace : WordTrace (prefixWord ++ tailWord_1291958) baseStart_1291958 baseEnd_1291958 := by
    simpa [prefixWord, tailWord_1291958, baseEnd_1291958] using wordTrace_append hprefix tailTrace_1291958
  have hstable : (prefixWord ++ tailWord_1291958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291958).length < 2 ^ (prefixWord ++ tailWord_1291958).sum := by decide
  have hdescent : baseEnd_1291958 < baseStart_1291958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291988 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 4, 3]
def baseStart_1291988 : Nat := 118140960795 + 1291988 * 2 ^ 59
def prefixEnd_1291988 : Nat := 4983230072969 + 3 ^ 40 * 1291988 * 2
def baseEnd_1291988 : Nat := 442273895894130883138841

theorem tailTrace_1291988 : CollatzResearch.WordTrace tailWord_1291988 prefixEnd_1291988 442273895894130883138841 := by
  unfold tailWord_1291988
  simp only [CollatzResearch.WordTrace]
  refine ⟨23561336821677802414174309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31415115762237069885565745 23561336821677802414174309)
  ·
    refine ⟨4417750654064587952657683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23561336821677802414174309 4417750654064587952657683)
    ·
      refine ⟨6626625981096881928986525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4417750654064587952657683 6626625981096881928986525)
      ·
        refine ⟨2484984742911330723369947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6626625981096881928986525 2484984742911330723369947)
        ·
          refine ⟨3727477114366996085054921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2484984742911330723369947 3727477114366996085054921)
          ·
            refine ⟨2795607835775247063791191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3727477114366996085054921 2795607835775247063791191)
            ·
              refine ⟨4193411753662870595686787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2795607835775247063791191 4193411753662870595686787)
              ·
                refine ⟨6290117630494305893530181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4193411753662870595686787 6290117630494305893530181)
                ·
                  refine ⟨1179397055717682355036909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6290117630494305893530181 1179397055717682355036909)
                  ·
                    refine ⟨442273895894130883138841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1179397055717682355036909 442273895894130883138841)
                    ·
                      rfl

theorem cell22_1291988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_1291988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291988 prefixEnd_1291988 := by exact prefixLift 1291988
  have htrace : WordTrace (prefixWord ++ tailWord_1291988) baseStart_1291988 baseEnd_1291988 := by
    simpa [prefixWord, tailWord_1291988, baseEnd_1291988] using wordTrace_append hprefix tailTrace_1291988
  have hstable : (prefixWord ++ tailWord_1291988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291988).length < 2 ^ (prefixWord ++ tailWord_1291988).sum := by decide
  have hdescent : baseEnd_1291988 < baseStart_1291988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291990 : List Nat := [5, 2, 1, 3, 1, 1, 2, 1, 6]
def baseStart_1291990 : Nat := 118140960795 + 1291990 * 2 ^ 59
def prefixEnd_1291990 : Nat := 4983230072969 + 3 ^ 40 * 1291990 * 2
def baseEnd_1291990 : Nat := 147424860178334514862945

theorem tailTrace_1291990 : CollatzResearch.WordTrace tailWord_1291990 prefixEnd_1291990 147424860178334514862945 := by
  unfold tailWord_1291990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2945171661834272448120089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31415164392898906113280949 2945171661834272448120089)
  ·
    refine ⟨2208878746375704336090067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2945171661834272448120089 2208878746375704336090067)
    ·
      refine ⟨3313318119563556504135101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2208878746375704336090067 3313318119563556504135101)
      ·
        refine ⟨1242494294836333689050663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3313318119563556504135101 1242494294836333689050663)
        ·
          refine ⟨1863741442254500533575995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1242494294836333689050663 1863741442254500533575995)
          ·
            refine ⟨2795612163381750800363993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1863741442254500533575995 2795612163381750800363993)
            ·
              refine ⟨2096709122536313100272995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2795612163381750800363993 2096709122536313100272995)
              ·
                refine ⟨3145063683804469650409493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2096709122536313100272995 3145063683804469650409493)
                ·
                  refine ⟨147424860178334514862945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3145063683804469650409493 147424860178334514862945)
                  ·
                    rfl

theorem cell22_1291990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_1291990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1291990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1291990 prefixEnd_1291990 := by exact prefixLift 1291990
  have htrace : WordTrace (prefixWord ++ tailWord_1291990) baseStart_1291990 baseEnd_1291990 := by
    simpa [prefixWord, tailWord_1291990, baseEnd_1291990] using wordTrace_append hprefix tailTrace_1291990
  have hstable : (prefixWord ++ tailWord_1291990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291990).length < 2 ^ (prefixWord ++ tailWord_1291990).sum := by decide
  have hdescent : baseEnd_1291990 < baseStart_1291990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292044 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 4, 5]
def baseStart_1292044 : Nat := 118140960795 + 1292044 * 2 ^ 59
def prefixEnd_1292044 : Nat := 4983230072969 + 3 ^ 40 * 1292044 * 2
def baseEnd_1292044 : Nat := 442293065838565403738669

theorem tailTrace_1292044 : CollatzResearch.WordTrace tailWord_1292044 prefixEnd_1292044 442293065838565403738669 := by
  unfold tailWord_1292044
  simp only [CollatzResearch.WordTrace]
  refine ⟨23562358065576363196193593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31416477420768484261591457 23562358065576363196193593)
  ·
    refine ⟨17671768549182272397145195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23562358065576363196193593 17671768549182272397145195)
    ·
      refine ⟨26507652823773408595717793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17671768549182272397145195 26507652823773408595717793)
      ·
        refine ⟨19880739617830056446788345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26507652823773408595717793 19880739617830056446788345)
        ·
          refine ⟨14910554713372542335091259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19880739617830056446788345 14910554713372542335091259)
          ·
            refine ⟨22365832070058813502636889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14910554713372542335091259 22365832070058813502636889)
            ·
              refine ⟨16774374052544110126977667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22365832070058813502636889 16774374052544110126977667)
              ·
                refine ⟨25161561078816165190466501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16774374052544110126977667 25161561078816165190466501)
                ·
                  refine ⟨4717792702278030973212469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25161561078816165190466501 4717792702278030973212469)
                  ·
                    refine ⟨442293065838565403738669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4717792702278030973212469 442293065838565403738669)
                    ·
                      rfl

theorem cell22_1292044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_1292044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292044 prefixEnd_1292044 := by exact prefixLift 1292044
  have htrace : WordTrace (prefixWord ++ tailWord_1292044) baseStart_1292044 baseEnd_1292044 := by
    simpa [prefixWord, tailWord_1292044, baseEnd_1292044] using wordTrace_append hprefix tailTrace_1292044
  have hstable : (prefixWord ++ tailWord_1292044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292044).length < 2 ^ (prefixWord ++ tailWord_1292044).sum := by decide
  have hdescent : baseEnd_1292044 < baseStart_1292044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292050 : List Nat := [3, 2, 4, 1, 1, 1, 3, 1, 3, 3]
def baseStart_1292050 : Nat := 118140960795 + 1292050 * 2 ^ 59
def prefixEnd_1292050 : Nat := 4983230072969 + 3 ^ 40 * 1292050 * 2
def baseEnd_1292050 : Nat := 442295119761183388088651

theorem tailTrace_1292050 : CollatzResearch.WordTrace tailWord_1292050 prefixEnd_1292050 442295119761183388088651 := by
  unfold tailWord_1292050
  simp only [CollatzResearch.WordTrace]
  refine ⟨11781233742282747354276401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31416623312753992944737069 11781233742282747354276401)
  ·
    refine ⟨8835925306712060515707301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11781233742282747354276401 8835925306712060515707301)
    ·
      refine ⟨1656735995008511346695119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8835925306712060515707301 1656735995008511346695119)
      ·
        refine ⟨2485103992512767020042679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1656735995008511346695119 2485103992512767020042679)
        ·
          refine ⟨3727655988769150530064019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2485103992512767020042679 3727655988769150530064019)
          ·
            refine ⟨5591483983153725795096029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3727655988769150530064019 5591483983153725795096029)
            ·
              refine ⟨2096806493682647173161011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5591483983153725795096029 2096806493682647173161011)
              ·
                refine ⟨3145209740523970759741517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2096806493682647173161011 3145209740523970759741517)
                ·
                  refine ⟨1179453652696489034903069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3145209740523970759741517 1179453652696489034903069)
                  ·
                    refine ⟨442295119761183388088651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1179453652696489034903069 442295119761183388088651)
                    ·
                      rfl

theorem cell22_1292050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_1292050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292050 prefixEnd_1292050 := by exact prefixLift 1292050
  have htrace : WordTrace (prefixWord ++ tailWord_1292050) baseStart_1292050 baseEnd_1292050 := by
    simpa [prefixWord, tailWord_1292050, baseEnd_1292050] using wordTrace_append hprefix tailTrace_1292050
  have hstable : (prefixWord ++ tailWord_1292050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292050).length < 2 ^ (prefixWord ++ tailWord_1292050).sum := by decide
  have hdescent : baseEnd_1292050 < baseStart_1292050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292059 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 5, 4]
def baseStart_1292059 : Nat := 118140960795 + 1292059 * 2 ^ 59
def prefixEnd_1292059 : Nat := 4983230072969 + 3 ^ 40 * 1292059 * 2
def baseEnd_1292059 : Nat := 442298200645110364613623

theorem tailTrace_1292059 : CollatzResearch.WordTrace tailWord_1292059 prefixEnd_1292059 442298200645110364613623 := by
  unfold tailWord_1292059
  simp only [CollatzResearch.WordTrace]
  refine ⟨47125263226098383954183231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31416842150732255969455487 47125263226098383954183231)
  ·
    refine ⟨70687894839147575931274847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47125263226098383954183231 70687894839147575931274847)
    ·
      refine ⟨106031842258721363896912271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70687894839147575931274847 106031842258721363896912271)
      ·
        refine ⟨159047763388082045845368407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106031842258721363896912271 159047763388082045845368407)
        ·
          refine ⟨238571645082123068768052611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159047763388082045845368407 238571645082123068768052611)
          ·
            refine ⟨357857467623184603152078917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238571645082123068768052611 357857467623184603152078917)
            ·
              refine ⟨67098275179347113091014797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 357857467623184603152078917 67098275179347113091014797)
              ·
                refine ⟨25161853192255167409130549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67098275179347113091014797 25161853192255167409130549)
                ·
                  refine ⟨2358923736773921944605989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25161853192255167409130549 2358923736773921944605989)
                  ·
                    refine ⟨442298200645110364613623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2358923736773921944605989 442298200645110364613623)
                    ·
                      rfl

theorem cell22_1292059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 4].length) (baseStart_1292059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292059 prefixEnd_1292059 := by exact prefixLift 1292059
  have htrace : WordTrace (prefixWord ++ tailWord_1292059) baseStart_1292059 baseEnd_1292059 := by
    simpa [prefixWord, tailWord_1292059, baseEnd_1292059] using wordTrace_append hprefix tailTrace_1292059
  have hstable : (prefixWord ++ tailWord_1292059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292059).length < 2 ^ (prefixWord ++ tailWord_1292059).sum := by decide
  have hdescent : baseEnd_1292059 < baseStart_1292059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292076 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 3, 4]
def baseStart_1292076 : Nat := 118140960795 + 1292076 * 2 ^ 59
def prefixEnd_1292076 : Nat := 4983230072969 + 3 ^ 40 * 1292076 * 2
def baseEnd_1292076 : Nat := 442304020092527986938571

theorem tailTrace_1292076 : CollatzResearch.WordTrace tailWord_1292076 prefixEnd_1292076 442304020092527986938571 := by
  unfold tailWord_1292076
  simp only [CollatzResearch.WordTrace]
  refine ⟨23562941633518397928776041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31417255511357863905034721 23562941633518397928776041)
  ·
    refine ⟨17672206225138798446582031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23562941633518397928776041 17672206225138798446582031)
    ·
      refine ⟨26508309337708197669873047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17672206225138798446582031 26508309337708197669873047)
      ·
        refine ⟨39762464006562296504809571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26508309337708197669873047 39762464006562296504809571)
        ·
          refine ⟨59643696009843444757214357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39762464006562296504809571 59643696009843444757214357)
          ·
            refine ⟨2795798250461411472994423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 59643696009843444757214357 2795798250461411472994423)
            ·
              refine ⟨4193697375692117209491635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2795798250461411472994423 4193697375692117209491635)
              ·
                refine ⟨6290546063538175814237453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4193697375692117209491635 6290546063538175814237453)
                ·
                  refine ⟨2358954773826815930339045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6290546063538175814237453 2358954773826815930339045)
                  ·
                    refine ⟨442304020092527986938571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2358954773826815930339045 442304020092527986938571)
                    ·
                      rfl

theorem cell22_1292076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_1292076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292076 prefixEnd_1292076 := by exact prefixLift 1292076
  have htrace : WordTrace (prefixWord ++ tailWord_1292076) baseStart_1292076 baseEnd_1292076 := by
    simpa [prefixWord, tailWord_1292076, baseEnd_1292076] using wordTrace_append hprefix tailTrace_1292076
  have hstable : (prefixWord ++ tailWord_1292076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292076).length < 2 ^ (prefixWord ++ tailWord_1292076).sum := by decide
  have hdescent : baseEnd_1292076 < baseStart_1292076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292174 : List Nat := [4, 1, 1, 5, 1, 1, 3, 1, 2, 3]
def baseStart_1292174 : Nat := 118140960795 + 1292174 * 2 ^ 59
def prefixEnd_1292174 : Nat := 4983230072969 + 3 ^ 40 * 1292174 * 2
def baseEnd_1292174 : Nat := 442337567495288397988271

theorem tailTrace_1292174 : CollatzResearch.WordTrace tailWord_1292174 prefixEnd_1292174 442337567495288397988271 := by
  unfold tailWord_1292174
  simp only [CollatzResearch.WordTrace]
  refine ⟨5891182202585219824327447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31419638413787839063079717 5891182202585219824327447)
  ·
    refine ⟨8836773303877829736491171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5891182202585219824327447 8836773303877829736491171)
    ·
      refine ⟨13255159955816744604736757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8836773303877829736491171 13255159955816744604736757)
      ·
        refine ⟨1242671245857819806694071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13255159955816744604736757 1242671245857819806694071)
        ·
          refine ⟨1864006868786729710041107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1242671245857819806694071 1864006868786729710041107)
          ·
            refine ⟨2796010303180094565061661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1864006868786729710041107 2796010303180094565061661)
            ·
              refine ⟨1048503863692535461898123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2796010303180094565061661 1048503863692535461898123)
              ·
                refine ⟨1572755795538803192847185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1048503863692535461898123 1572755795538803192847185)
                ·
                  refine ⟨1179566846654102394635389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1572755795538803192847185 1179566846654102394635389)
                  ·
                    refine ⟨442337567495288397988271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1179566846654102394635389 442337567495288397988271)
                    ·
                      rfl

theorem cell22_1292174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_1292174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292174 prefixEnd_1292174 := by exact prefixLift 1292174
  have htrace : WordTrace (prefixWord ++ tailWord_1292174) baseStart_1292174 baseEnd_1292174 := by
    simpa [prefixWord, tailWord_1292174, baseEnd_1292174] using wordTrace_append hprefix tailTrace_1292174
  have hstable : (prefixWord ++ tailWord_1292174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292174).length < 2 ^ (prefixWord ++ tailWord_1292174).sum := by decide
  have hdescent : baseEnd_1292174 < baseStart_1292174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292245 : List Nat := [1, 3, 2, 3, 2, 1, 3, 2, 1, 4]
def baseStart_1292245 : Nat := 118140960795 + 1292245 * 2 ^ 59
def prefixEnd_1292245 : Nat := 4983230072969 + 3 ^ 40 * 1292245 * 2
def baseEnd_1292245 : Nat := 442361872246267879463053

theorem tailTrace_1292245 : CollatzResearch.WordTrace tailWord_1292245 prefixEnd_1292245 442361872246267879463053 := by
  unfold tailWord_1292245
  simp only [CollatzResearch.WordTrace]
  refine ⟨47132047203424537720454189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31421364802283025146969459 47132047203424537720454189)
  ·
    refine ⟨17674517701284201645170321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47132047203424537720454189 17674517701284201645170321)
    ·
      refine ⟨13255888275963151233877741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17674517701284201645170321 13255888275963151233877741)
      ·
        refine ⟨4970958103486181712704153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13255888275963151233877741 4970958103486181712704153)
        ·
          refine ⟨3728218577614636284528115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4970958103486181712704153 3728218577614636284528115)
          ·
            refine ⟨5592327866421954426792173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3728218577614636284528115 5592327866421954426792173)
            ·
              refine ⟨2097122949908232910047065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5592327866421954426792173 2097122949908232910047065)
              ·
                refine ⟨1572842212431174682535299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2097122949908232910047065 1572842212431174682535299)
                ·
                  refine ⟨2359263318646762023802949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1572842212431174682535299 2359263318646762023802949)
                  ·
                    refine ⟨442361872246267879463053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2359263318646762023802949 442361872246267879463053)
                    ·
                      rfl

theorem cell22_1292245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_1292245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292245 prefixEnd_1292245 := by exact prefixLift 1292245
  have htrace : WordTrace (prefixWord ++ tailWord_1292245) baseStart_1292245 baseEnd_1292245 := by
    simpa [prefixWord, tailWord_1292245, baseEnd_1292245] using wordTrace_append hprefix tailTrace_1292245
  have hstable : (prefixWord ++ tailWord_1292245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292245).length < 2 ^ (prefixWord ++ tailWord_1292245).sum := by decide
  have hdescent : baseEnd_1292245 < baseStart_1292245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292256 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 1, 6]
def baseStart_1292256 : Nat := 118140960795 + 1292256 * 2 ^ 59
def prefixEnd_1292256 : Nat := 4983230072969 + 3 ^ 40 * 1292256 * 2
def baseEnd_1292256 : Nat := 442365637771067517438019

theorem tailTrace_1292256 : CollatzResearch.WordTrace tailWord_1292256 prefixEnd_1292256 442365637771067517438019 := by
  unfold tailWord_1292256
  simp only [CollatzResearch.WordTrace]
  refine ⟨23566224203192343299552311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31421632270923124399403081 23566224203192343299552311)
  ·
    refine ⟨35349336304788514949328467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23566224203192343299552311 35349336304788514949328467)
    ·
      refine ⟨53024004457182772423992701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35349336304788514949328467 53024004457182772423992701)
      ·
        refine ⟨19884001671443539658997263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53024004457182772423992701 19884001671443539658997263)
        ·
          refine ⟨29826002507165309488495895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19884001671443539658997263 29826002507165309488495895)
          ·
            refine ⟨44739003760747964232743843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29826002507165309488495895 44739003760747964232743843)
            ·
              refine ⟨67108505641121946349115765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44739003760747964232743843 67108505641121946349115765)
              ·
                refine ⟨6291422403855182470229603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67108505641121946349115765 6291422403855182470229603)
                ·
                  refine ⟨9437133605782773705344405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6291422403855182470229603 9437133605782773705344405)
                  ·
                    refine ⟨442365637771067517438019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9437133605782773705344405 442365637771067517438019)
                    ·
                      rfl

theorem cell22_1292256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_1292256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292256 prefixEnd_1292256 := by exact prefixLift 1292256
  have htrace : WordTrace (prefixWord ++ tailWord_1292256) baseStart_1292256 baseEnd_1292256 := by
    simpa [prefixWord, tailWord_1292256, baseEnd_1292256] using wordTrace_append hprefix tailTrace_1292256
  have hstable : (prefixWord ++ tailWord_1292256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292256).length < 2 ^ (prefixWord ++ tailWord_1292256).sum := by decide
  have hdescent : baseEnd_1292256 < baseStart_1292256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292292 : List Nat := [2, 3, 2, 4, 1, 1, 2, 1, 1, 5]
def baseStart_1292292 : Nat := 118140960795 + 1292292 * 2 ^ 59
def prefixEnd_1292292 : Nat := 4983230072969 + 3 ^ 40 * 1292292 * 2
def baseEnd_1292292 : Nat := 442377961306775423537909

theorem tailTrace_1292292 : CollatzResearch.WordTrace tailWord_1292292 prefixEnd_1292292 442377961306775423537909 := by
  unfold tailWord_1292292
  simp only [CollatzResearch.WordTrace]
  refine ⟨23566880717127132373707565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31422507622836176498276753 23566880717127132373707565)
  ·
    refine ⟨8837580268922674640140337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23566880717127132373707565 8837580268922674640140337)
    ·
      refine ⟨6628185201692005980105253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8837580268922674640140337 6628185201692005980105253)
      ·
        refine ⟨1242784725317251121269735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6628185201692005980105253 1242784725317251121269735)
        ·
          refine ⟨1864177087975876681904603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1242784725317251121269735 1864177087975876681904603)
          ·
            refine ⟨2796265631963815022856905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1864177087975876681904603 2796265631963815022856905)
            ·
              refine ⟨2097199223972861267142679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2796265631963815022856905 2097199223972861267142679)
              ·
                refine ⟨3145798835959291900714019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2097199223972861267142679 3145798835959291900714019)
                ·
                  refine ⟨4718698253938937851071029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3145798835959291900714019 4718698253938937851071029)
                  ·
                    refine ⟨442377961306775423537909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4718698253938937851071029 442377961306775423537909)
                    ·
                      rfl

theorem cell22_1292292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_1292292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292292 prefixEnd_1292292 := by exact prefixLift 1292292
  have htrace : WordTrace (prefixWord ++ tailWord_1292292) baseStart_1292292 baseEnd_1292292 := by
    simpa [prefixWord, tailWord_1292292, baseEnd_1292292] using wordTrace_append hprefix tailTrace_1292292
  have hstable : (prefixWord ++ tailWord_1292292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292292).length < 2 ^ (prefixWord ++ tailWord_1292292).sum := by decide
  have hdescent : baseEnd_1292292 < baseStart_1292292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292337 : List Nat := [1, 2, 2, 3, 1, 3, 2, 4, 1, 3]
def baseStart_1292337 : Nat := 118140960795 + 1292337 * 2 ^ 59
def prefixEnd_1292337 : Nat := 4983230072969 + 3 ^ 40 * 1292337 * 2
def baseEnd_1292337 : Nat := 442393365726410306162771

theorem tailTrace_1292337 : CollatzResearch.WordTrace tailWord_1292337 prefixEnd_1292337 442393365726410306162771 := by
  unfold tailWord_1292337
  simp only [CollatzResearch.WordTrace]
  refine ⟨47135402719091237432803265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31423601812727491621868843 47135402719091237432803265)
  ·
    refine ⟨35351552039318428074602449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47135402719091237432803265 35351552039318428074602449)
    ·
      refine ⟨26513664029488821055951837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35351552039318428074602449 26513664029488821055951837)
      ·
        refine ⟨9942624011058307895981939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26513664029488821055951837 9942624011058307895981939)
        ·
          refine ⟨14913936016587461843972909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9942624011058307895981939 14913936016587461843972909)
          ·
            refine ⟨5592726006220298191489841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14913936016587461843972909 5592726006220298191489841)
            ·
              refine ⟨4194544504665223643617381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5592726006220298191489841 4194544504665223643617381)
              ·
                refine ⟨786477094624729433178259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4194544504665223643617381 786477094624729433178259)
                ·
                  refine ⟨1179715641937094149767389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 786477094624729433178259 1179715641937094149767389)
                  ·
                    refine ⟨442393365726410306162771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1179715641937094149767389 442393365726410306162771)
                    ·
                      rfl

theorem cell22_1292337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 1, 3].length) (baseStart_1292337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292337 prefixEnd_1292337 := by exact prefixLift 1292337
  have htrace : WordTrace (prefixWord ++ tailWord_1292337) baseStart_1292337 baseEnd_1292337 := by
    simpa [prefixWord, tailWord_1292337, baseEnd_1292337] using wordTrace_append hprefix tailTrace_1292337
  have hstable : (prefixWord ++ tailWord_1292337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292337).length < 2 ^ (prefixWord ++ tailWord_1292337).sum := by decide
  have hdescent : baseEnd_1292337 < baseStart_1292337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292348 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 2, 5]
def baseStart_1292348 : Nat := 118140960795 + 1292348 * 2 ^ 59
def prefixEnd_1292348 : Nat := 4983230072969 + 3 ^ 40 * 1292348 * 2
def baseEnd_1292348 : Nat := 442397131251209944137737

theorem tailTrace_1292348 : CollatzResearch.WordTrace tailWord_1292348 prefixEnd_1292348 442397131251209944137737 := by
  unfold tailWord_1292348
  simp only [CollatzResearch.WordTrace]
  refine ⟨23567901961025693155726849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31423869281367590874302465 23567901961025693155726849)
  ·
    refine ⟨17675926470769269866795137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23567901961025693155726849 17675926470769269866795137)
    ·
      refine ⟨13256944853076952400096353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17675926470769269866795137 13256944853076952400096353)
      ·
        refine ⟨9942708639807714300072265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13256944853076952400096353 9942708639807714300072265)
        ·
          refine ⟨7457031479855785725054199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9942708639807714300072265 7457031479855785725054199)
          ·
            refine ⟨11185547219783678587581299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7457031479855785725054199 11185547219783678587581299)
            ·
              refine ⟨16778320829675517881371949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11185547219783678587581299 16778320829675517881371949)
              ·
                refine ⟨6291870311128319205514481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16778320829675517881371949 6291870311128319205514481)
                ·
                  refine ⟨4718902733346239404135861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6291870311128319205514481 4718902733346239404135861)
                  ·
                    refine ⟨442397131251209944137737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4718902733346239404135861 442397131251209944137737)
                    ·
                      rfl

theorem cell22_1292348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_1292348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292348 prefixEnd_1292348 := by exact prefixLift 1292348
  have htrace : WordTrace (prefixWord ++ tailWord_1292348) baseStart_1292348 baseEnd_1292348 := by
    simpa [prefixWord, tailWord_1292348, baseEnd_1292348] using wordTrace_append hprefix tailTrace_1292348
  have hstable : (prefixWord ++ tailWord_1292348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292348).length < 2 ^ (prefixWord ++ tailWord_1292348).sum := by decide
  have hdescent : baseEnd_1292348 < baseStart_1292348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292408 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 6, 4]
def baseStart_1292408 : Nat := 118140960795 + 1292408 * 2 ^ 59
def prefixEnd_1292408 : Nat := 4983230072969 + 3 ^ 40 * 1292408 * 2
def baseEnd_1292408 : Nat := 442417670477389787637553

theorem tailTrace_1292408 : CollatzResearch.WordTrace tailWord_1292408 prefixEnd_1292408 442417670477389787637553 := by
  unfold tailWord_1292408
  simp only [CollatzResearch.WordTrace]
  refine ⟨23568996150917008279318939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31425328201222677705758585 23568996150917008279318939)
  ·
    refine ⟨35353494226375512418978409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23568996150917008279318939 35353494226375512418978409)
    ·
      refine ⟨26515120669781634314233807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35353494226375512418978409 26515120669781634314233807)
      ·
        refine ⟨39772681004672451471350711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26515120669781634314233807 39772681004672451471350711)
        ·
          refine ⟨59659021507008677207026067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39772681004672451471350711 59659021507008677207026067)
          ·
            refine ⟨89488532260513015810539101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59659021507008677207026067 89488532260513015810539101)
            ·
              refine ⟨33558199597692380928952163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89488532260513015810539101 33558199597692380928952163)
              ·
                refine ⟨50337299396538571393428245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33558199597692380928952163 50337299396538571393428245)
                ·
                  refine ⟨2359560909212745534066949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50337299396538571393428245 2359560909212745534066949)
                  ·
                    refine ⟨442417670477389787637553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2359560909212745534066949 442417670477389787637553)
                    ·
                      rfl

theorem cell22_1292408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_1292408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292408 prefixEnd_1292408 := by exact prefixLift 1292408
  have htrace : WordTrace (prefixWord ++ tailWord_1292408) baseStart_1292408 baseEnd_1292408 := by
    simpa [prefixWord, tailWord_1292408, baseEnd_1292408] using wordTrace_append hprefix tailTrace_1292408
  have hstable : (prefixWord ++ tailWord_1292408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292408).length < 2 ^ (prefixWord ++ tailWord_1292408).sum := by decide
  have hdescent : baseEnd_1292408 < baseStart_1292408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292423 : List Nat := [1, 1, 4, 2, 1, 1, 4, 8]
def baseStart_1292423 : Nat := 118140960795 + 1292423 * 2 ^ 59
def prefixEnd_1292423 : Nat := 4983230072969 + 3 ^ 40 * 1292423 * 2
def baseEnd_1292423 : Nat := 49158089475992749834723

theorem tailTrace_1292423 : CollatzResearch.WordTrace tailWord_1292423 prefixEnd_1292423 49158089475992749834723 := by
  unfold tailWord_1292423
  simp only [CollatzResearch.WordTrace]
  refine ⟨47138539396779674120433923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31425692931186449413622615 47138539396779674120433923)
  ·
    refine ⟨70707809095169511180650885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47138539396779674120433923 70707809095169511180650885)
    ·
      refine ⟨13257714205344283346372041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70707809095169511180650885 13257714205344283346372041)
      ·
        refine ⟨9943285654008212509779031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13257714205344283346372041 9943285654008212509779031)
        ·
          refine ⟨14914928481012318764668547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9943285654008212509779031 14914928481012318764668547)
          ·
            refine ⟨22372392721518478147002821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14914928481012318764668547 22372392721518478147002821)
            ·
              refine ⟨4194823635284714652563029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22372392721518478147002821 4194823635284714652563029)
              ·
                refine ⟨49158089475992749834723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4194823635284714652563029 49158089475992749834723)
                ·
                  rfl

theorem cell22_1292423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 8].length) (baseStart_1292423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292423 prefixEnd_1292423 := by exact prefixLift 1292423
  have htrace : WordTrace (prefixWord ++ tailWord_1292423) baseStart_1292423 baseEnd_1292423 := by
    simpa [prefixWord, tailWord_1292423, baseEnd_1292423] using wordTrace_append hprefix tailTrace_1292423
  have hstable : (prefixWord ++ tailWord_1292423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292423).length < 2 ^ (prefixWord ++ tailWord_1292423).sum := by decide
  have hdescent : baseEnd_1292423 < baseStart_1292423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292425 : List Nat := [1, 2, 1, 1, 4, 2, 4, 1, 2, 4]
def baseStart_1292425 : Nat := 118140960795 + 1292425 * 2 ^ 59
def prefixEnd_1292425 : Nat := 4983230072969 + 3 ^ 40 * 1292425 * 2
def baseEnd_1292425 : Nat := 442423489924807409962501

theorem tailTrace_1292425 : CollatzResearch.WordTrace tailWord_1292425 prefixEnd_1292425 442423489924807409962501 := by
  unfold tailWord_1292425
  simp only [CollatzResearch.WordTrace]
  refine ⟨47138612342772428462006729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31425741561848285641337819 47138612342772428462006729)
  ·
    refine ⟨35353959257079321346505047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47138612342772428462006729 35353959257079321346505047)
    ·
      refine ⟨53030938885618982019757571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35353959257079321346505047 53030938885618982019757571)
      ·
        refine ⟨79546408328428473029636357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53030938885618982019757571 79546408328428473029636357)
        ·
          refine ⟨14914951561580338693056817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79546408328428473029636357 14914951561580338693056817)
          ·
            refine ⟨11186213671185254019792613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14914951561580338693056817 11186213671185254019792613)
            ·
              refine ⟨2097415063347235128711115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11186213671185254019792613 2097415063347235128711115)
              ·
                refine ⟨3146122595020852693066673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2097415063347235128711115 3146122595020852693066673)
                ·
                  refine ⟨2359591946265639519800005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3146122595020852693066673 2359591946265639519800005)
                  ·
                    refine ⟨442423489924807409962501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2359591946265639519800005 442423489924807409962501)
                    ·
                      rfl

theorem cell22_1292425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 4].length) (baseStart_1292425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292425 prefixEnd_1292425 := by exact prefixLift 1292425
  have htrace : WordTrace (prefixWord ++ tailWord_1292425) baseStart_1292425 baseEnd_1292425 := by
    simpa [prefixWord, tailWord_1292425, baseEnd_1292425] using wordTrace_append hprefix tailTrace_1292425
  have hstable : (prefixWord ++ tailWord_1292425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292425).length < 2 ^ (prefixWord ++ tailWord_1292425).sum := by decide
  have hdescent : baseEnd_1292425 < baseStart_1292425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292440 : List Nat := [2, 1, 2, 4, 4, 9]
def baseStart_1292440 : Nat := 118140960795 + 1292440 * 2 ^ 59
def prefixEnd_1292440 : Nat := 4983230072969 + 3 ^ 40 * 1292440 * 2
def baseEnd_1292440 : Nat := 5462081786806819393055

theorem tailTrace_1292440 : CollatzResearch.WordTrace tailWord_1292440 prefixEnd_1292440 5462081786806819393055 := by
  unfold tailWord_1292440
  simp only [CollatzResearch.WordTrace]
  refine ⟨23569579718859043011901387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31426106291812057349201849 23569579718859043011901387)
  ·
    refine ⟨35354369578288564517852081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23569579718859043011901387 35354369578288564517852081)
    ·
      refine ⟨26515777183716423388389061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35354369578288564517852081 26515777183716423388389061)
      ·
        refine ⟨4971708221946829385322949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26515777183716423388389061 4971708221946829385322949)
        ·
          refine ⟨932195291615030509748053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4971708221946829385322949 932195291615030509748053)
          ·
            refine ⟨5462081786806819393055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 932195291615030509748053 5462081786806819393055)
            ·
              rfl

theorem cell22_1292440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 9].length) (baseStart_1292440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292440 prefixEnd_1292440 := by exact prefixLift 1292440
  have htrace : WordTrace (prefixWord ++ tailWord_1292440) baseStart_1292440 baseEnd_1292440 := by
    simpa [prefixWord, tailWord_1292440, baseEnd_1292440] using wordTrace_append hprefix tailTrace_1292440
  have hstable : (prefixWord ++ tailWord_1292440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292440).length < 2 ^ (prefixWord ++ tailWord_1292440).sum := by decide
  have hdescent : baseEnd_1292440 < baseStart_1292440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292453 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 1, 8]
def baseStart_1292453 : Nat := 118140960795 + 1292453 * 2 ^ 59
def prefixEnd_1292453 : Nat := 4983230072969 + 3 ^ 40 * 1292453 * 2
def baseEnd_1292453 : Nat := 442433074897024670262415

theorem tailTrace_1292453 : CollatzResearch.WordTrace tailWord_1292453 prefixEnd_1292453 442433074897024670262415 := by
  unfold tailWord_1292453
  simp only [CollatzResearch.WordTrace]
  refine ⟨47139633586670989244026013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31426422391113992829350675 47139633586670989244026013)
  ·
    refine ⟨17677362595001620966509755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47139633586670989244026013 17677362595001620966509755)
    ·
      refine ⟨26516043892502431449764633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17677362595001620966509755 26516043892502431449764633)
      ·
        refine ⟨19887032919376823587323475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26516043892502431449764633 19887032919376823587323475)
        ·
          refine ⟨29830549379065235380985213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19887032919376823587323475 29830549379065235380985213)
          ·
            refine ⟨11186456017149463267869455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29830549379065235380985213 11186456017149463267869455)
            ·
              refine ⟨16779684025724194901804183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11186456017149463267869455 16779684025724194901804183)
              ·
                refine ⟨25169526038586292352706275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16779684025724194901804183 25169526038586292352706275)
                ·
                  refine ⟨37754289057879438529059413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25169526038586292352706275 37754289057879438529059413)
                  ·
                    refine ⟨442433074897024670262415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37754289057879438529059413 442433074897024670262415)
                    ·
                      rfl

theorem cell22_1292453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_1292453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292453 prefixEnd_1292453 := by exact prefixLift 1292453
  have htrace : WordTrace (prefixWord ++ tailWord_1292453) baseStart_1292453 baseEnd_1292453 := by
    simpa [prefixWord, tailWord_1292453, baseEnd_1292453] using wordTrace_append hprefix tailTrace_1292453
  have hstable : (prefixWord ++ tailWord_1292453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292453).length < 2 ^ (prefixWord ++ tailWord_1292453).sum := by decide
  have hdescent : baseEnd_1292453 < baseStart_1292453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292519 : List Nat := [1, 1, 5, 3, 1, 2, 3, 1, 5]
def baseStart_1292519 : Nat := 118140960795 + 1292519 * 2 ^ 59
def prefixEnd_1292519 : Nat := 4983230072969 + 3 ^ 40 * 1292519 * 2
def baseEnd_1292519 : Nat := 147485222681940832704071

theorem tailTrace_1292519 : CollatzResearch.WordTrace tailWord_1292519 prefixEnd_1292519 147485222681940832704071 := by
  unfold tailWord_1292519
  simp only [CollatzResearch.WordTrace]
  refine ⟨47142040804431882515928611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31428027202954588343952407 47142040804431882515928611)
  ·
    refine ⟨70713061206647823773892917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47142040804431882515928611 70713061206647823773892917)
    ·
      refine ⟨6629349488123233478802461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70713061206647823773892917 6629349488123233478802461)
      ·
        refine ⟨2486006058046212554550923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6629349488123233478802461 2486006058046212554550923)
        ·
          refine ⟨3729009087069318831826385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2486006058046212554550923 3729009087069318831826385)
          ·
            refine ⟨2796756815301989123869789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3729009087069318831826385 2796756815301989123869789)
            ·
              refine ⟨1048783805738245921451171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2796756815301989123869789 1048783805738245921451171)
              ·
                refine ⟨1573175708607368882176757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1048783805738245921451171 1573175708607368882176757)
                ·
                  refine ⟨147485222681940832704071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1573175708607368882176757 147485222681940832704071)
                  ·
                    rfl

theorem cell22_1292519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 5].length) (baseStart_1292519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292519 prefixEnd_1292519 := by exact prefixLift 1292519
  have htrace : WordTrace (prefixWord ++ tailWord_1292519) baseStart_1292519 baseEnd_1292519 := by
    simpa [prefixWord, tailWord_1292519, baseEnd_1292519] using wordTrace_append hprefix tailTrace_1292519
  have hstable : (prefixWord ++ tailWord_1292519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292519).length < 2 ^ (prefixWord ++ tailWord_1292519).sum := by decide
  have hdescent : baseEnd_1292519 < baseStart_1292519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292545 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 3, 5]
def baseStart_1292545 : Nat := 118140960795 + 1292545 * 2 ^ 59
def prefixEnd_1292545 : Nat := 4983230072969 + 3 ^ 40 * 1292545 * 2
def baseEnd_1292545 : Nat := 442464568377167096962133

theorem tailTrace_1292545 : CollatzResearch.WordTrace tailWord_1292545 prefixEnd_1292545 442464568377167096962133 := by
  unfold tailWord_1292545
  simp only [CollatzResearch.WordTrace]
  refine ⟨47142989102337688956375089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31428659401558459304250059 47142989102337688956375089)
  ·
    refine ⟨35357241826753266717281317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47142989102337688956375089 35357241826753266717281317)
    ·
      refine ⟨6629482842516237509490247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35357241826753266717281317 6629482842516237509490247)
      ·
        refine ⟨9944224263774356264235371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6629482842516237509490247 9944224263774356264235371)
        ·
          refine ⟨14916336395661534396353057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9944224263774356264235371 14916336395661534396353057)
          ·
            refine ⟨11187252296746150797264793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14916336395661534396353057 11187252296746150797264793)
            ·
              refine ⟨8390439222559613097948595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11187252296746150797264793 8390439222559613097948595)
              ·
                refine ⟨12585658833839419646922893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8390439222559613097948595 12585658833839419646922893)
                ·
                  refine ⟨4719622062689782367596085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12585658833839419646922893 4719622062689782367596085)
                  ·
                    refine ⟨442464568377167096962133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4719622062689782367596085 442464568377167096962133)
                    ·
                      rfl

theorem cell22_1292545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_1292545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292545 prefixEnd_1292545 := by exact prefixLift 1292545
  have htrace : WordTrace (prefixWord ++ tailWord_1292545) baseStart_1292545 baseEnd_1292545 := by
    simpa [prefixWord, tailWord_1292545, baseEnd_1292545] using wordTrace_append hprefix tailTrace_1292545
  have hstable : (prefixWord ++ tailWord_1292545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292545).length < 2 ^ (prefixWord ++ tailWord_1292545).sum := by decide
  have hdescent : baseEnd_1292545 < baseStart_1292545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292575 : List Nat := [1, 1, 2, 4, 3, 1, 1, 9]
def baseStart_1292575 : Nat := 118140960795 + 1292575 * 2 ^ 59
def prefixEnd_1292575 : Nat := 4983230072969 + 3 ^ 40 * 1292575 * 2
def baseEnd_1292575 : Nat := 49163870887806335412449

theorem tailTrace_1292575 : CollatzResearch.WordTrace tailWord_1292575 prefixEnd_1292575 49163870887806335412449 := by
  unfold tailWord_1292575
  simp only [CollatzResearch.WordTrace]
  refine ⟨47144083292229004079967179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31429388861486002719978119 47144083292229004079967179)
  ·
    refine ⟨70716124938343506119950769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47144083292229004079967179 70716124938343506119950769)
    ·
      refine ⟨53037093703757629589963077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70716124938343506119950769 53037093703757629589963077)
      ·
        refine ⟨9944455069454555548118077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53037093703757629589963077 9944455069454555548118077)
        ·
          refine ⟨3729170651045458330544279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9944455069454555548118077 3729170651045458330544279)
          ·
            refine ⟨5593755976568187495816419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3729170651045458330544279 5593755976568187495816419)
            ·
              refine ⟨8390633964852281243724629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5593755976568187495816419 8390633964852281243724629)
              ·
                refine ⟨49163870887806335412449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8390633964852281243724629 49163870887806335412449)
                ·
                  rfl

theorem cell22_1292575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 9].length) (baseStart_1292575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292575 prefixEnd_1292575 := by exact prefixLift 1292575
  have htrace : WordTrace (prefixWord ++ tailWord_1292575) baseStart_1292575 baseEnd_1292575 := by
    simpa [prefixWord, tailWord_1292575, baseEnd_1292575] using wordTrace_append hprefix tailTrace_1292575
  have hstable : (prefixWord ++ tailWord_1292575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292575).length < 2 ^ (prefixWord ++ tailWord_1292575).sum := by decide
  have hdescent : baseEnd_1292575 < baseStart_1292575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292594 : List Nat := [3, 2, 1, 1, 5, 1, 2, 1, 2, 4]
def baseStart_1292594 : Nat := 118140960795 + 1292594 * 2 ^ 59
def prefixEnd_1292594 : Nat := 4983230072969 + 3 ^ 40 * 1292594 * 2
def baseEnd_1292594 : Nat := 442481342078547302486983

theorem tailTrace_1292594 : CollatzResearch.WordTrace tailWord_1292594 prefixEnd_1292594 442481342078547302486983 := by
  unfold tailWord_1292594
  simp only [CollatzResearch.WordTrace]
  refine ⟨11786194069790042581227209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31429850852773446883272557 11786194069790042581227209)
  ·
    refine ⟨8839645552342531935920407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11786194069790042581227209 8839645552342531935920407)
    ·
      refine ⟨13259468328513797903880611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8839645552342531935920407 13259468328513797903880611)
      ·
        refine ⟨19889202492770696855820917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13259468328513797903880611 19889202492770696855820917)
        ·
          refine ⟨1864612733697252830233211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19889202492770696855820917 1864612733697252830233211)
          ·
            refine ⟨2796919100545879245349817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1864612733697252830233211 2796919100545879245349817)
            ·
              refine ⟨2097689325409409434012363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2796919100545879245349817 2097689325409409434012363)
              ·
                refine ⟨3146533988114114151018545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2097689325409409434012363 3146533988114114151018545)
                ·
                  refine ⟨2359900491085585613263909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3146533988114114151018545 2359900491085585613263909)
                  ·
                    refine ⟨442481342078547302486983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2359900491085585613263909 442481342078547302486983)
                    ·
                      rfl

theorem cell22_1292594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_1292594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292594 prefixEnd_1292594 := by exact prefixLift 1292594
  have htrace : WordTrace (prefixWord ++ tailWord_1292594) baseStart_1292594 baseEnd_1292594 := by
    simpa [prefixWord, tailWord_1292594, baseEnd_1292594] using wordTrace_append hprefix tailTrace_1292594
  have hstable : (prefixWord ++ tailWord_1292594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292594).length < 2 ^ (prefixWord ++ tailWord_1292594).sum := by decide
  have hdescent : baseEnd_1292594 < baseStart_1292594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292665 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 10]
def baseStart_1292665 : Nat := 118140960795 + 1292665 * 2 ^ 59
def prefixEnd_1292665 : Nat := 4983230072969 + 3 ^ 40 * 1292665 * 2
def baseEnd_1292665 : Nat := 147501882276508927987255

theorem tailTrace_1292665 : CollatzResearch.WordTrace tailWord_1292665 prefixEnd_1292665 147501882276508927987255 := by
  unfold tailWord_1292665
  simp only [CollatzResearch.WordTrace]
  refine ⟨47147365861902949450743449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31431577241268632967162299 47147365861902949450743449)
  ·
    refine ⟨35360524396427212088057587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47147365861902949450743449 35360524396427212088057587)
    ·
      refine ⟨53040786594640818132086381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35360524396427212088057587 53040786594640818132086381)
      ·
        refine ⟨19890294972990306799532393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53040786594640818132086381 19890294972990306799532393)
        ·
          refine ⟨14917721229742730099649295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19890294972990306799532393 14917721229742730099649295)
          ·
            refine ⟨22376581844614095149473943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14917721229742730099649295 22376581844614095149473943)
            ·
              refine ⟨33564872766921142724210915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22376581844614095149473943 33564872766921142724210915)
              ·
                refine ⟨50347309150381714086316373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33564872766921142724210915 50347309150381714086316373)
                ·
                  refine ⟨147501882276508927987255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 50347309150381714086316373 147501882276508927987255)
                  ·
                    rfl

theorem cell22_1292665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 10].length) (baseStart_1292665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292665 prefixEnd_1292665 := by exact prefixLift 1292665
  have htrace : WordTrace (prefixWord ++ tailWord_1292665) baseStart_1292665 baseEnd_1292665 := by
    simpa [prefixWord, tailWord_1292665, baseEnd_1292665] using wordTrace_append hprefix tailTrace_1292665
  have hstable : (prefixWord ++ tailWord_1292665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292665).length < 2 ^ (prefixWord ++ tailWord_1292665).sum := by decide
  have hdescent : baseEnd_1292665 < baseStart_1292665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292701 : List Nat := [1, 4, 2, 1, 4, 1, 2, 2, 1, 4]
def baseStart_1292701 : Nat := 118140960795 + 1292701 * 2 ^ 59
def prefixEnd_1292701 : Nat := 4983230072969 + 3 ^ 40 * 1292701 * 2
def baseEnd_1292701 : Nat := 442517970365234690061655

theorem tailTrace_1292701 : CollatzResearch.WordTrace tailWord_1292701 prefixEnd_1292701 442517970365234690061655 := by
  unfold tailWord_1292701
  simp only [CollatzResearch.WordTrace]
  refine ⟨47148678889772527599053957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31432452593181685066035971 47148678889772527599053957)
  ·
    refine ⟨8840377291832348924822617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47148678889772527599053957 8840377291832348924822617)
    ·
      refine ⟨6630282968874261693616963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8840377291832348924822617 6630282968874261693616963)
      ·
        refine ⟨9945424453311392540425445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6630282968874261693616963 9945424453311392540425445)
        ·
          refine ⟨1864767084995886101329771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9945424453311392540425445 1864767084995886101329771)
          ·
            refine ⟨2797150627493829151994657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1864767084995886101329771 2797150627493829151994657)
            ·
              refine ⟨2097862970620371863995993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2797150627493829151994657 2097862970620371863995993)
              ·
                refine ⟨1573397227965278897996995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2097862970620371863995993 1573397227965278897996995)
                ·
                  refine ⟨2360095841947918346995493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1573397227965278897996995 2360095841947918346995493)
                  ·
                    refine ⟨442517970365234690061655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2360095841947918346995493 442517970365234690061655)
                    ·
                      rfl

theorem cell22_1292701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_1292701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292701 prefixEnd_1292701 := by exact prefixLift 1292701
  have htrace : WordTrace (prefixWord ++ tailWord_1292701) baseStart_1292701 baseEnd_1292701 := by
    simpa [prefixWord, tailWord_1292701, baseEnd_1292701] using wordTrace_append hprefix tailTrace_1292701
  have hstable : (prefixWord ++ tailWord_1292701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292701).length < 2 ^ (prefixWord ++ tailWord_1292701).sum := by decide
  have hdescent : baseEnd_1292701 < baseStart_1292701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292727 : List Nat := [1, 1, 3, 1, 3, 5, 8]
def baseStart_1292727 : Nat := 118140960795 + 1292727 * 2 ^ 59
def prefixEnd_1292727 : Nat := 4983230072969 + 3 ^ 40 * 1292727 * 2
def baseEnd_1292727 : Nat := 16389884099873306996725

theorem tailTrace_1292727 : CollatzResearch.WordTrace tailWord_1292727 prefixEnd_1292727 16389884099873306996725 := by
  unfold tailWord_1292727
  simp only [CollatzResearch.WordTrace]
  refine ⟨47149627187678334039500435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31433084791785556026333623 47149627187678334039500435)
  ·
    refine ⟨70724440781517501059250653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47149627187678334039500435 70724440781517501059250653)
    ·
      refine ⟨26521665293069062897218995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70724440781517501059250653 26521665293069062897218995)
      ·
        refine ⟨39782497939603594345828493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26521665293069062897218995 39782497939603594345828493)
        ·
          refine ⟨14918436727351347879685685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39782497939603594345828493 14918436727351347879685685)
          ·
            refine ⟨1398603443189188863720533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14918436727351347879685685 1398603443189188863720533)
            ·
              refine ⟨16389884099873306996725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1398603443189188863720533 16389884099873306996725)
              ·
                rfl

theorem cell22_1292727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 8].length) (baseStart_1292727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292727 prefixEnd_1292727 := by exact prefixLift 1292727
  have htrace : WordTrace (prefixWord ++ tailWord_1292727) baseStart_1292727 baseEnd_1292727 := by
    simpa [prefixWord, tailWord_1292727, baseEnd_1292727] using wordTrace_append hprefix tailTrace_1292727
  have hstable : (prefixWord ++ tailWord_1292727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292727).length < 2 ^ (prefixWord ++ tailWord_1292727).sum := by decide
  have hdescent : baseEnd_1292727 < baseStart_1292727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292729 : List Nat := [1, 2, 1, 4, 3, 2, 1, 2, 2, 4]
def baseStart_1292729 : Nat := 118140960795 + 1292729 * 2 ^ 59
def prefixEnd_1292729 : Nat := 4983230072969 + 3 ^ 40 * 1292729 * 2
def baseEnd_1292729 : Nat := 442527555337451950361569

theorem tailTrace_1292729 : CollatzResearch.WordTrace tailWord_1292729 prefixEnd_1292729 442527555337451950361569 := by
  unfold tailWord_1292729
  simp only [CollatzResearch.WordTrace]
  refine ⟨47149700133671088381073241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31433133422447392254048827 47149700133671088381073241)
  ·
    refine ⟨35362275100253316285804931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47149700133671088381073241 35362275100253316285804931)
    ·
      refine ⟨53043412650379974428707397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35362275100253316285804931 53043412650379974428707397)
      ·
        refine ⟨9945639871946245205382637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53043412650379974428707397 9945639871946245205382637)
        ·
          refine ⟨3729614951979841952018489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9945639871946245205382637 3729614951979841952018489)
          ·
            refine ⟨2797211213984881464013867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3729614951979841952018489 2797211213984881464013867)
            ·
              refine ⟨4195816820977322196020801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2797211213984881464013867 4195816820977322196020801)
              ·
                refine ⟨3146862615732991647015601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4195816820977322196020801 3146862615732991647015601)
                ·
                  refine ⟨2360146961799743735261701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3146862615732991647015601 2360146961799743735261701)
                  ·
                    refine ⟨442527555337451950361569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2360146961799743735261701 442527555337451950361569)
                    ·
                      rfl

theorem cell22_1292729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 4].length) (baseStart_1292729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292729 prefixEnd_1292729 := by exact prefixLift 1292729
  have htrace : WordTrace (prefixWord ++ tailWord_1292729) baseStart_1292729 baseEnd_1292729 := by
    simpa [prefixWord, tailWord_1292729, baseEnd_1292729] using wordTrace_append hprefix tailTrace_1292729
  have hstable : (prefixWord ++ tailWord_1292729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292729).length < 2 ^ (prefixWord ++ tailWord_1292729).sum := by decide
  have hdescent : baseEnd_1292729 < baseStart_1292729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292787 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 2, 5]
def baseStart_1292787 : Nat := 118140960795 + 1292787 * 2 ^ 59
def prefixEnd_1292787 : Nat := 4983230072969 + 3 ^ 40 * 1292787 * 2
def baseEnd_1292787 : Nat := 442547409922759132411391

theorem tailTrace_1292787 : CollatzResearch.WordTrace tailWord_1292787 prefixEnd_1292787 442547409922759132411391 := by
  unfold tailWord_1292787
  simp only [CollatzResearch.WordTrace]
  refine ⟨47151815567460964286684615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31434543711640642857789743 47151815567460964286684615)
  ·
    refine ⟨70727723351191446430026923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47151815567460964286684615 70727723351191446430026923)
    ·
      refine ⟨106091585026787169645040385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70727723351191446430026923 106091585026787169645040385)
      ·
        refine ⟨79568688770090377233780289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106091585026787169645040385 79568688770090377233780289)
        ·
          refine ⟨59676516577567782925335217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79568688770090377233780289 59676516577567782925335217)
          ·
            refine ⟨44757387433175837194001413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59676516577567782925335217 44757387433175837194001413)
            ·
              refine ⟨8392010143720469473875265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44757387433175837194001413 8392010143720469473875265)
              ·
                refine ⟨6294007607790352105406449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8392010143720469473875265 6294007607790352105406449)
                ·
                  refine ⟨4720505705842764079054837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6294007607790352105406449 4720505705842764079054837)
                  ·
                    refine ⟨442547409922759132411391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4720505705842764079054837 442547409922759132411391)
                    ·
                      rfl

theorem cell22_1292787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 5].length) (baseStart_1292787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292787 prefixEnd_1292787 := by exact prefixLift 1292787
  have htrace : WordTrace (prefixWord ++ tailWord_1292787) baseStart_1292787 baseEnd_1292787 := by
    simpa [prefixWord, tailWord_1292787, baseEnd_1292787] using wordTrace_append hprefix tailTrace_1292787
  have hstable : (prefixWord ++ tailWord_1292787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292787).length < 2 ^ (prefixWord ++ tailWord_1292787).sum := by decide
  have hdescent : baseEnd_1292787 < baseStart_1292787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292793 : List Nat := [1, 2, 1, 3, 1, 2, 6, 2, 1, 3]
def baseStart_1292793 : Nat := 118140960795 + 1292793 * 2 ^ 59
def prefixEnd_1292793 : Nat := 4983230072969 + 3 ^ 40 * 1292793 * 2
def baseEnd_1292793 : Nat := 442549463845377116761373

theorem tailTrace_1292793 : CollatzResearch.WordTrace tailWord_1292793 prefixEnd_1292793 442549463845377116761373 := by
  unfold tailWord_1292793
  simp only [CollatzResearch.WordTrace]
  refine ⟨47152034405439227311403033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31434689603626151540935355 47152034405439227311403033)
  ·
    refine ⟨35364025804079420483552275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47152034405439227311403033 35364025804079420483552275)
    ·
      refine ⟨53046038706119130725328413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35364025804079420483552275 53046038706119130725328413)
      ·
        refine ⟨19892264514794674021998155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53046038706119130725328413 19892264514794674021998155)
        ·
          refine ⟨29838396772192011032997233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19892264514794674021998155 29838396772192011032997233)
          ·
            refine ⟨22378797579144008274747925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29838396772192011032997233 22378797579144008274747925)
            ·
              refine ⟨1049006136522375387878809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22378797579144008274747925 1049006136522375387878809)
              ·
                refine ⟨786754602391781540909107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1049006136522375387878809 786754602391781540909107)
                ·
                  refine ⟨1180131903587672311363661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 786754602391781540909107 1180131903587672311363661)
                  ·
                    refine ⟨442549463845377116761373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1180131903587672311363661 442549463845377116761373)
                    ·
                      rfl

theorem cell22_1292793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 1, 3].length) (baseStart_1292793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292793 prefixEnd_1292793 := by exact prefixLift 1292793
  have htrace : WordTrace (prefixWord ++ tailWord_1292793) baseStart_1292793 baseEnd_1292793 := by
    simpa [prefixWord, tailWord_1292793, baseEnd_1292793] using wordTrace_append hprefix tailTrace_1292793
  have hstable : (prefixWord ++ tailWord_1292793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292793).length < 2 ^ (prefixWord ++ tailWord_1292793).sum := by decide
  have hdescent : baseEnd_1292793 < baseStart_1292793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292804 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 1, 7]
def baseStart_1292804 : Nat := 118140960795 + 1292804 * 2 ^ 59
def prefixEnd_1292804 : Nat := 4983230072969 + 3 ^ 40 * 1292804 * 2
def baseEnd_1292804 : Nat := 442553229370176754736339

theorem tailTrace_1292804 : CollatzResearch.WordTrace tailWord_1292804 prefixEnd_1292804 442553229370176754736339 := by
  unfold tailWord_1292804
  simp only [CollatzResearch.WordTrace]
  refine ⟨23576217804199688095026733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31434957072266250793368977 23576217804199688095026733)
  ·
    refine ⟨8841081676574883035635025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23576217804199688095026733 8841081676574883035635025)
    ·
      refine ⟨6630811257431162276726269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8841081676574883035635025 6630811257431162276726269)
      ·
        refine ⟨2486554221536685853772351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6630811257431162276726269 2486554221536685853772351)
        ·
          refine ⟨3729831332305028780658527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2486554221536685853772351 3729831332305028780658527)
          ·
            refine ⟨5594746998457543170987791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3729831332305028780658527 5594746998457543170987791)
            ·
              refine ⟨8392120497686314756481687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5594746998457543170987791 8392120497686314756481687)
              ·
                refine ⟨12588180746529472134722531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8392120497686314756481687 12588180746529472134722531)
                ·
                  refine ⟨18882271119794208202083797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12588180746529472134722531 18882271119794208202083797)
                  ·
                    refine ⟨442553229370176754736339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18882271119794208202083797 442553229370176754736339)
                    ·
                      rfl

theorem cell22_1292804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_1292804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292804 prefixEnd_1292804 := by exact prefixLift 1292804
  have htrace : WordTrace (prefixWord ++ tailWord_1292804) baseStart_1292804 baseEnd_1292804 := by
    simpa [prefixWord, tailWord_1292804, baseEnd_1292804] using wordTrace_append hprefix tailTrace_1292804
  have hstable : (prefixWord ++ tailWord_1292804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292804).length < 2 ^ (prefixWord ++ tailWord_1292804).sum := by decide
  have hdescent : baseEnd_1292804 < baseStart_1292804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292819 : List Nat := [1, 1, 1, 2, 1, 5, 2, 4, 1, 4]
def baseStart_1292819 : Nat := 118140960795 + 1292819 * 2 ^ 59
def prefixEnd_1292819 : Nat := 4983230072969 + 3 ^ 40 * 1292819 * 2
def baseEnd_1292819 : Nat := 442558364176721715611293

theorem tailTrace_1292819 : CollatzResearch.WordTrace tailWord_1292819 prefixEnd_1292819 442558364176721715611293 := by
  unfold tailWord_1292819
  simp only [CollatzResearch.WordTrace]
  refine ⟨47152982703345033751849511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31435321802230022501233007 47152982703345033751849511)
  ·
    refine ⟨70729474055017550627774267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47152982703345033751849511 70729474055017550627774267)
    ·
      refine ⟨106094211082526325941661401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70729474055017550627774267 106094211082526325941661401)
      ·
        refine ⟨79570658311894744456246051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106094211082526325941661401 79570658311894744456246051)
        ·
          refine ⟨119355987467842116684369077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79570658311894744456246051 119355987467842116684369077)
          ·
            refine ⟨11189623825110198439159601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 119355987467842116684369077 11189623825110198439159601)
            ·
              refine ⟨8392217868832648829369701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11189623825110198439159601 8392217868832648829369701)
              ·
                refine ⟨1573540850406121655506819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8392217868832648829369701 1573540850406121655506819)
                ·
                  refine ⟨2360311275609182483260229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1573540850406121655506819 2360311275609182483260229)
                  ·
                    refine ⟨442558364176721715611293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2360311275609182483260229 442558364176721715611293)
                    ·
                      rfl

theorem cell22_1292819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 4].length) (baseStart_1292819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292819 prefixEnd_1292819 := by exact prefixLift 1292819
  have htrace : WordTrace (prefixWord ++ tailWord_1292819) baseStart_1292819 baseEnd_1292819 := by
    simpa [prefixWord, tailWord_1292819, baseEnd_1292819] using wordTrace_append hprefix tailTrace_1292819
  have hstable : (prefixWord ++ tailWord_1292819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292819).length < 2 ^ (prefixWord ++ tailWord_1292819).sum := by decide
  have hdescent : baseEnd_1292819 < baseStart_1292819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292870 : List Nat := [6, 1, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_1292870 : Nat := 118140960795 + 1292870 * 2 ^ 59
def prefixEnd_1292870 : Nat := 4983230072969 + 3 ^ 40 * 1292870 * 2
def baseEnd_1292870 : Nat := 442575822518974582586137

theorem tailTrace_1292870 : CollatzResearch.WordTrace tailWord_1292870 prefixEnd_1292870 442575822518974582586137 := by
  unfold tailWord_1292870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1473588838317508420686127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31436561884106846307970709 1473588838317508420686127)
  ·
    refine ⟨2210383257476262631029191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1473588838317508420686127 2210383257476262631029191)
    ·
      refine ⟨3315574886214393946543787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2210383257476262631029191 3315574886214393946543787)
      ·
        refine ⟨4973362329321590919815681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3315574886214393946543787 4973362329321590919815681)
        ·
          refine ⟨3730021746991193189861761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4973362329321590919815681 3730021746991193189861761)
          ·
            refine ⟨2797516310243394892396321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3730021746991193189861761 2797516310243394892396321)
            ·
              refine ⟨2098137232682546169297241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2797516310243394892396321 2098137232682546169297241)
              ·
                refine ⟨1573602924511909626972931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2098137232682546169297241 1573602924511909626972931)
                ·
                  refine ⟨2360404386767864440459397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1573602924511909626972931 2360404386767864440459397)
                  ·
                    refine ⟨442575822518974582586137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2360404386767864440459397 442575822518974582586137)
                    ·
                      rfl

theorem cell22_1292870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_1292870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292870 prefixEnd_1292870 := by exact prefixLift 1292870
  have htrace : WordTrace (prefixWord ++ tailWord_1292870) baseStart_1292870 baseEnd_1292870 := by
    simpa [prefixWord, tailWord_1292870, baseEnd_1292870] using wordTrace_append hprefix tailTrace_1292870
  have hstable : (prefixWord ++ tailWord_1292870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292870).length < 2 ^ (prefixWord ++ tailWord_1292870).sum := by decide
  have hdescent : baseEnd_1292870 < baseStart_1292870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292879 : List Nat := [1, 1, 2, 1, 1, 2, 8, 6]
def baseStart_1292879 : Nat := 118140960795 + 1292879 * 2 ^ 59
def prefixEnd_1292879 : Nat := 4983230072969 + 3 ^ 40 * 1292879 * 2
def baseEnd_1292879 : Nat := 49175433711433506567901

theorem tailTrace_1292879 : CollatzResearch.WordTrace tailWord_1292879 prefixEnd_1292879 49175433711433506567901 := by
  unfold tailWord_1292879
  simp only [CollatzResearch.WordTrace]
  refine ⟨47155171083127663999033691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31436780722085109332689127 47155171083127663999033691)
  ·
    refine ⟨70732756624691495998550537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47155171083127663999033691 70732756624691495998550537)
    ·
      refine ⟨53049567468518621998912903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70732756624691495998550537 53049567468518621998912903)
      ·
        refine ⟨79574351202777932998369355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53049567468518621998912903 79574351202777932998369355)
        ·
          refine ⟨119361526804166899497554033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79574351202777932998369355 119361526804166899497554033)
          ·
            refine ⟨89521145103125174623165525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119361526804166899497554033 89521145103125174623165525)
            ·
              refine ⟨1049075919177248140115221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 89521145103125174623165525 1049075919177248140115221)
              ·
                refine ⟨49175433711433506567901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1049075919177248140115221 49175433711433506567901)
                ·
                  rfl

theorem cell22_1292879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 6].length) (baseStart_1292879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292879 prefixEnd_1292879 := by exact prefixLift 1292879
  have htrace : WordTrace (prefixWord ++ tailWord_1292879) baseStart_1292879 baseEnd_1292879 := by
    simpa [prefixWord, tailWord_1292879, baseEnd_1292879] using wordTrace_append hprefix tailTrace_1292879
  have hstable : (prefixWord ++ tailWord_1292879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292879).length < 2 ^ (prefixWord ++ tailWord_1292879).sum := by decide
  have hdescent : baseEnd_1292879 < baseStart_1292879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292911 : List Nat := [1, 1, 2, 1, 3, 2, 5, 1, 3, 3]
def baseStart_1292911 : Nat := 118140960795 + 1292911 * 2 ^ 59
def prefixEnd_1292911 : Nat := 4983230072969 + 3 ^ 40 * 1292911 * 2
def baseEnd_1292911 : Nat := 442589857656864142311011

theorem tailTrace_1292911 : CollatzResearch.WordTrace tailWord_1292911 prefixEnd_1292911 442589857656864142311011 := by
  unfold tailWord_1292911
  simp only [CollatzResearch.WordTrace]
  refine ⟨47156338219011733464198587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31437558812674488976132391 47156338219011733464198587)
  ·
    refine ⟨70734507328517600196297881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47156338219011733464198587 70734507328517600196297881)
    ·
      refine ⟨53050880496388200147223411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70734507328517600196297881 53050880496388200147223411)
      ·
        refine ⟨79576320744582300220835117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53050880496388200147223411 79576320744582300220835117)
        ·
          refine ⟨29841120279218362582813169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79576320744582300220835117 29841120279218362582813169)
          ·
            refine ⟨22380840209413771937109877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29841120279218362582813169 22380840209413771937109877)
            ·
              refine ⟨2098203769632541119104051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22380840209413771937109877 2098203769632541119104051)
              ·
                refine ⟨3147305654448811678656077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2098203769632541119104051 3147305654448811678656077)
                ·
                  refine ⟨1180239620418304379496029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3147305654448811678656077 1180239620418304379496029)
                  ·
                    refine ⟨442589857656864142311011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1180239620418304379496029 442589857656864142311011)
                    ·
                      rfl

theorem cell22_1292911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 3].length) (baseStart_1292911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292911 prefixEnd_1292911 := by exact prefixLift 1292911
  have htrace : WordTrace (prefixWord ++ tailWord_1292911) baseStart_1292911 baseEnd_1292911 := by
    simpa [prefixWord, tailWord_1292911, baseEnd_1292911] using wordTrace_append hprefix tailTrace_1292911
  have hstable : (prefixWord ++ tailWord_1292911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292911).length < 2 ^ (prefixWord ++ tailWord_1292911).sum := by decide
  have hdescent : baseEnd_1292911 < baseStart_1292911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292917 : List Nat := [1, 3, 4, 2, 2, 2, 2, 1, 2, 3]
def baseStart_1292917 : Nat := 118140960795 + 1292917 * 2 ^ 59
def prefixEnd_1292917 : Nat := 4983230072969 + 3 ^ 40 * 1292917 * 2
def baseEnd_1292917 : Nat := 442591911579482126660993

theorem tailTrace_1292917 : CollatzResearch.WordTrace tailWord_1292917 prefixEnd_1292917 442591911579482126660993 := by
  unfold tailWord_1292917
  simp only [CollatzResearch.WordTrace]
  refine ⟨47156557056989996488917005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31437704704659997659278003 47156557056989996488917005)
  ·
    refine ⟨17683708896371248683343877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47156557056989996488917005 17683708896371248683343877)
    ·
      refine ⟨3315695418069609128126977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17683708896371248683343877 3315695418069609128126977)
      ·
        refine ⟨2486771563552206846095233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3315695418069609128126977 2486771563552206846095233)
        ·
          refine ⟨1865078672664155134571425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2486771563552206846095233 1865078672664155134571425)
          ·
            refine ⟨1398809004498116350928569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1865078672664155134571425 1398809004498116350928569)
            ·
              refine ⟨1049106753373587263196427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1398809004498116350928569 1049106753373587263196427)
              ·
                refine ⟨1573660130060380894794641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1049106753373587263196427 1573660130060380894794641)
                ·
                  refine ⟨1180245097545285671095981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1573660130060380894794641 1180245097545285671095981)
                  ·
                    refine ⟨442591911579482126660993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1180245097545285671095981 442591911579482126660993)
                    ·
                      rfl

theorem cell22_1292917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_1292917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292917 prefixEnd_1292917 := by exact prefixLift 1292917
  have htrace : WordTrace (prefixWord ++ tailWord_1292917) baseStart_1292917 baseEnd_1292917 := by
    simpa [prefixWord, tailWord_1292917, baseEnd_1292917] using wordTrace_append hprefix tailTrace_1292917
  have hstable : (prefixWord ++ tailWord_1292917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292917).length < 2 ^ (prefixWord ++ tailWord_1292917).sum := by decide
  have hdescent : baseEnd_1292917 < baseStart_1292917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292958 : List Nat := [4, 3, 1, 1, 1, 1, 4, 2, 5]
def baseStart_1292958 : Nat := 118140960795 + 1292958 * 2 ^ 59
def prefixEnd_1292958 : Nat := 4983230072969 + 3 ^ 40 * 1292958 * 2
def baseEnd_1292958 : Nat := 147535315572457228795289

theorem tailTrace_1292958 : CollatzResearch.WordTrace tailWord_1292958 prefixEnd_1292958 147535315572457228795289 := by
  unfold tailWord_1292958
  simp only [CollatzResearch.WordTrace]
  refine ⟨5894756556230182561394941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31438701633227640327439685 5894756556230182561394941)
  ·
    refine ⟨2210533708586318460523103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5894756556230182561394941 2210533708586318460523103)
    ·
      refine ⟨3315800562879477690784655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2210533708586318460523103 3315800562879477690784655)
      ·
        refine ⟨4973700844319216536176983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3315800562879477690784655 4973700844319216536176983)
        ·
          refine ⟨7460551266478824804265475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4973700844319216536176983 7460551266478824804265475)
          ·
            refine ⟨11190826899718237206398213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7460551266478824804265475 11190826899718237206398213)
            ·
              refine ⟨2098280043697169476199665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11190826899718237206398213 2098280043697169476199665)
              ·
                refine ⟨1573710032772877107149749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2098280043697169476199665 1573710032772877107149749)
                ·
                  refine ⟨147535315572457228795289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1573710032772877107149749 147535315572457228795289)
                  ·
                    rfl

theorem cell22_1292958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_1292958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1292958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1292958 prefixEnd_1292958 := by exact prefixLift 1292958
  have htrace : WordTrace (prefixWord ++ tailWord_1292958) baseStart_1292958 baseEnd_1292958 := by
    simpa [prefixWord, tailWord_1292958, baseEnd_1292958] using wordTrace_append hprefix tailTrace_1292958
  have hstable : (prefixWord ++ tailWord_1292958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292958).length < 2 ^ (prefixWord ++ tailWord_1292958).sum := by decide
  have hdescent : baseEnd_1292958 < baseStart_1292958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293020 : List Nat := [2, 2, 5, 1, 1, 1, 2, 4, 4]
def baseStart_1293020 : Nat := 118140960795 + 1293020 * 2 ^ 59
def prefixEnd_1293020 : Nat := 4983230072969 + 3 ^ 40 * 1293020 * 2
def baseEnd_1293020 : Nat := 147542390194808063778559

theorem tailTrace_1293020 : CollatzResearch.WordTrace tailWord_1293020 prefixEnd_1293020 147542390194808063778559 := by
  unfold tailWord_1293020
  simp only [CollatzResearch.WordTrace]
  refine ⟨23580156887808422539958257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31440209183744563386611009 23580156887808422539958257)
  ·
    refine ⟨17685117665856316904968693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23580156887808422539958257 17685117665856316904968693)
    ·
      refine ⟨1657979781174029709840815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17685117665856316904968693 1657979781174029709840815)
      ·
        refine ⟨2486969671761044564761223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1657979781174029709840815 2486969671761044564761223)
        ·
          refine ⟨3730454507641566847141835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2486969671761044564761223 3730454507641566847141835)
          ·
            refine ⟨5595681761462350270712753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3730454507641566847141835 5595681761462350270712753)
            ·
              refine ⟨4196761321096762703034565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5595681761462350270712753 4196761321096762703034565)
              ·
                refine ⟨786892747705643006818981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4196761321096762703034565 786892747705643006818981)
                ·
                  refine ⟨147542390194808063778559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 786892747705643006818981 147542390194808063778559)
                  ·
                    rfl

theorem cell22_1293020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 4].length) (baseStart_1293020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293020 prefixEnd_1293020 := by exact prefixLift 1293020
  have htrace : WordTrace (prefixWord ++ tailWord_1293020) baseStart_1293020 baseEnd_1293020 := by
    simpa [prefixWord, tailWord_1293020, baseEnd_1293020] using wordTrace_append hprefix tailTrace_1293020
  have hstable : (prefixWord ++ tailWord_1293020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293020).length < 2 ^ (prefixWord ++ tailWord_1293020).sum := by decide
  have hdescent : baseEnd_1293020 < baseStart_1293020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293046 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_1293046 : Nat := 118140960795 + 1293046 * 2 ^ 59
def prefixEnd_1293046 : Nat := 4983230072969 + 3 ^ 40 * 1293046 * 2
def baseEnd_1293046 : Nat := 442636070915768790185597

theorem tailTrace_1293046 : CollatzResearch.WordTrace tailWord_1293046 prefixEnd_1293046 442636070915768790185597 := by
  unfold tailWord_1293046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2947578879595165720022687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31440841382348434346908661 2947578879595165720022687)
  ·
    refine ⟨4421368319392748580034031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2947578879595165720022687 4421368319392748580034031)
    ·
      refine ⟨6632052479089122870051047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4421368319392748580034031 6632052479089122870051047)
      ·
        refine ⟨9948078718633684305076571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6632052479089122870051047 9948078718633684305076571)
        ·
          refine ⟨14922118077950526457614857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9948078718633684305076571 14922118077950526457614857)
          ·
            refine ⟨11191588558462894843211143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14922118077950526457614857 11191588558462894843211143)
            ·
              refine ⟨16787382837694342264816715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11191588558462894843211143 16787382837694342264816715)
              ·
                refine ⟨25181074256541513397225073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16787382837694342264816715 25181074256541513397225073)
                ·
                  refine ⟨18885805692406135047918805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25181074256541513397225073 18885805692406135047918805)
                  ·
                    refine ⟨442636070915768790185597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18885805692406135047918805 442636070915768790185597)
                    ·
                      rfl

theorem cell22_1293046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_1293046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293046 prefixEnd_1293046 := by exact prefixLift 1293046
  have htrace : WordTrace (prefixWord ++ tailWord_1293046) baseStart_1293046 baseEnd_1293046 := by
    simpa [prefixWord, tailWord_1293046, baseEnd_1293046] using wordTrace_append hprefix tailTrace_1293046
  have hstable : (prefixWord ++ tailWord_1293046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293046).length < 2 ^ (prefixWord ++ tailWord_1293046).sum := by decide
  have hdescent : baseEnd_1293046 < baseStart_1293046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293151 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 1, 6]
def baseStart_1293151 : Nat := 118140960795 + 1293151 * 2 ^ 59
def prefixEnd_1293151 : Nat := 4983230072969 + 3 ^ 40 * 1293151 * 2
def baseEnd_1293151 : Nat := 442672014561583516310275

theorem tailTrace_1293151 : CollatzResearch.WordTrace tailWord_1293151 prefixEnd_1293151 442672014561583516310275 := by
  unfold tailWord_1293151
  simp only [CollatzResearch.WordTrace]
  refine ⟨47165091738142254452935307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31443394492094836301956871 47165091738142254452935307)
  ·
    refine ⟨70747637607213381679402961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47165091738142254452935307 70747637607213381679402961)
    ·
      refine ⟨53060728205410036259552221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70747637607213381679402961 53060728205410036259552221)
      ·
        refine ⟨19897773077028763597332083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53060728205410036259552221 19897773077028763597332083)
        ·
          refine ⟨29846659615543145395998125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19897773077028763597332083 29846659615543145395998125)
          ·
            refine ⟨11192497355828679523499297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29846659615543145395998125 11192497355828679523499297)
            ·
              refine ⟨8394373016871509642624473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11192497355828679523499297 8394373016871509642624473)
              ·
                refine ⟨6295779762653632231968355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8394373016871509642624473 6295779762653632231968355)
                ·
                  refine ⟨9443669643980448347952533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6295779762653632231968355 9443669643980448347952533)
                  ·
                    refine ⟨442672014561583516310275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9443669643980448347952533 442672014561583516310275)
                    ·
                      rfl

theorem cell22_1293151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_1293151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293151 prefixEnd_1293151 := by exact prefixLift 1293151
  have htrace : WordTrace (prefixWord ++ tailWord_1293151) baseStart_1293151 baseEnd_1293151 := by
    simpa [prefixWord, tailWord_1293151, baseEnd_1293151] using wordTrace_append hprefix tailTrace_1293151
  have hstable : (prefixWord ++ tailWord_1293151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293151).length < 2 ^ (prefixWord ++ tailWord_1293151).sum := by decide
  have hdescent : baseEnd_1293151 < baseStart_1293151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293168 : List Nat := [2, 1, 1, 1, 4, 1, 5, 1, 2, 4]
def baseStart_1293168 : Nat := 118140960795 + 1293168 * 2 ^ 59
def prefixEnd_1293168 : Nat := 4983230072969 + 3 ^ 40 * 1293168 * 2
def baseEnd_1293168 : Nat := 442677834009001138635223

theorem tailTrace_1293168 : CollatzResearch.WordTrace tailWord_1293168 prefixEnd_1293168 442677834009001138635223 := by
  unfold tailWord_1293168
  simp only [CollatzResearch.WordTrace]
  refine ⟨23582855889540333178152079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31443807852720444237536105 23582855889540333178152079)
  ·
    refine ⟨35374283834310499767228119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23582855889540333178152079 35374283834310499767228119)
    ·
      refine ⟨53061425751465749650842179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35374283834310499767228119 53061425751465749650842179)
      ·
        refine ⟨79592138627198624476263269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53061425751465749650842179 79592138627198624476263269)
        ·
          refine ⟨14923525992599742089299363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79592138627198624476263269 14923525992599742089299363)
          ·
            refine ⟨22385288988899613133949045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14923525992599742089299363 22385288988899613133949045)
            ·
              refine ⟨2098620842709338731307723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22385288988899613133949045 2098620842709338731307723)
              ·
                refine ⟨3147931264064008096961585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2098620842709338731307723 3147931264064008096961585)
                ·
                  refine ⟨2360948448048006072721189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3147931264064008096961585 2360948448048006072721189)
                  ·
                    refine ⟨442677834009001138635223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2360948448048006072721189 442677834009001138635223)
                    ·
                      rfl

theorem cell22_1293168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 2, 4].length) (baseStart_1293168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293168 prefixEnd_1293168 := by exact prefixLift 1293168
  have htrace : WordTrace (prefixWord ++ tailWord_1293168) baseStart_1293168 baseEnd_1293168 := by
    simpa [prefixWord, tailWord_1293168, baseEnd_1293168] using wordTrace_append hprefix tailTrace_1293168
  have hstable : (prefixWord ++ tailWord_1293168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293168).length < 2 ^ (prefixWord ++ tailWord_1293168).sum := by decide
  have hdescent : baseEnd_1293168 < baseStart_1293168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293174 : List Nat := [5, 1, 1, 3, 1, 3, 2, 1, 1, 4]
def baseStart_1293174 : Nat := 118140960795 + 1293174 * 2 ^ 59
def prefixEnd_1293174 : Nat := 4983230072969 + 3 ^ 40 * 1293174 * 2
def baseEnd_1293174 : Nat := 442679887931619122985205

theorem tailTrace_1293174 : CollatzResearch.WordTrace tailWord_1293174 prefixEnd_1293174 442679887931619122985205 := by
  unfold tailWord_1293174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2947870663566183086313911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31443953744705952920681717 2947870663566183086313911)
  ·
    refine ⟨4421805995349274629470867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2947870663566183086313911 4421805995349274629470867)
    ·
      refine ⟨6632708993023911944206301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4421805995349274629470867 6632708993023911944206301)
      ·
        refine ⟨2487265872383966979077363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6632708993023911944206301 2487265872383966979077363)
        ·
          refine ⟨3730898808575950468616045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2487265872383966979077363 3730898808575950468616045)
          ·
            refine ⟨1399087053215981425731017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3730898808575950468616045 1399087053215981425731017)
            ·
              refine ⟨1049315289911986069298263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1399087053215981425731017 1049315289911986069298263)
              ·
                refine ⟨1573972934867979103947395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1049315289911986069298263 1573972934867979103947395)
                ·
                  refine ⟨2360959402301968655921093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1573972934867979103947395 2360959402301968655921093)
                  ·
                    refine ⟨442679887931619122985205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2360959402301968655921093 442679887931619122985205)
                    ·
                      rfl

theorem cell22_1293174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_1293174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293174 prefixEnd_1293174 := by exact prefixLift 1293174
  have htrace : WordTrace (prefixWord ++ tailWord_1293174) baseStart_1293174 baseEnd_1293174 := by
    simpa [prefixWord, tailWord_1293174, baseEnd_1293174] using wordTrace_append hprefix tailTrace_1293174
  have hstable : (prefixWord ++ tailWord_1293174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293174).length < 2 ^ (prefixWord ++ tailWord_1293174).sum := by decide
  have hdescent : baseEnd_1293174 < baseStart_1293174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293196 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 1, 8]
def baseStart_1293196 : Nat := 118140960795 + 1293196 * 2 ^ 59
def prefixEnd_1293196 : Nat := 4983230072969 + 3 ^ 40 * 1293196 * 2
def baseEnd_1293196 : Nat := 442687418981218398935137

theorem tailTrace_1293196 : CollatzResearch.WordTrace tailWord_1293196 prefixEnd_1293196 442687418981218398935137 := by
  unfold tailWord_1293196
  simp only [CollatzResearch.WordTrace]
  refine ⟨23583366511489613569161721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31444488681986151425548961 23583366511489613569161721)
  ·
    refine ⟨17687524883617210176871291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23583366511489613569161721 17687524883617210176871291)
    ·
      refine ⟨26531287325425815265306937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17687524883617210176871291 26531287325425815265306937)
      ·
        refine ⟨19898465494069361448980203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26531287325425815265306937 19898465494069361448980203)
        ·
          refine ⟨29847698241104042173470305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19898465494069361448980203 29847698241104042173470305)
          ·
            refine ⟨22385773680828031630102729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29847698241104042173470305 22385773680828031630102729)
            ·
              refine ⟨16789330260621023722577047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22385773680828031630102729 16789330260621023722577047)
              ·
                refine ⟨25183995390931535583865571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16789330260621023722577047 25183995390931535583865571)
                ·
                  refine ⟨37775993086397303375798357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25183995390931535583865571 37775993086397303375798357)
                  ·
                    refine ⟨442687418981218398935137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37775993086397303375798357 442687418981218398935137)
                    ·
                      rfl

theorem cell22_1293196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_1293196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293196 prefixEnd_1293196 := by exact prefixLift 1293196
  have htrace : WordTrace (prefixWord ++ tailWord_1293196) baseStart_1293196 baseEnd_1293196 := by
    simpa [prefixWord, tailWord_1293196, baseEnd_1293196] using wordTrace_append hprefix tailTrace_1293196
  have hstable : (prefixWord ++ tailWord_1293196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293196).length < 2 ^ (prefixWord ++ tailWord_1293196).sum := by decide
  have hdescent : baseEnd_1293196 < baseStart_1293196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293215 : List Nat := [1, 1, 2, 5, 2, 1, 2, 2, 3, 3]
def baseStart_1293215 : Nat := 118140960795 + 1293215 * 2 ^ 59
def prefixEnd_1293215 : Nat := 4983230072969 + 3 ^ 40 * 1293215 * 2
def baseEnd_1293215 : Nat := 442693923069508682710079

theorem tailTrace_1293215 : CollatzResearch.WordTrace tailWord_1293215 prefixEnd_1293215 442693923069508682710079 := by
  unfold tailWord_1293215
  simp only [CollatzResearch.WordTrace]
  refine ⟨47167426009910393383265099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31444950673273595588843399 47167426009910393383265099)
  ·
    refine ⟨70751139014865590074897649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47167426009910393383265099 70751139014865590074897649)
    ·
      refine ⟨53063354261149192556173237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70751139014865590074897649 53063354261149192556173237)
      ·
        refine ⟨4974689461982736802141241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53063354261149192556173237 4974689461982736802141241)
        ·
          refine ⟨3731017096487052601605931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4974689461982736802141241 3731017096487052601605931)
          ·
            refine ⟨5596525644730578902408897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3731017096487052601605931 5596525644730578902408897)
            ·
              refine ⟨4197394233547934176806673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5596525644730578902408897 4197394233547934176806673)
              ·
                refine ⟨3148045675160950632605005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4197394233547934176806673 3148045675160950632605005)
                ·
                  refine ⟨1180517128185356487226877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3148045675160950632605005 1180517128185356487226877)
                  ·
                    refine ⟨442693923069508682710079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1180517128185356487226877 442693923069508682710079)
                    ·
                      rfl

theorem cell22_1293215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 3].length) (baseStart_1293215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293215 prefixEnd_1293215 := by exact prefixLift 1293215
  have htrace : WordTrace (prefixWord ++ tailWord_1293215) baseStart_1293215 baseEnd_1293215 := by
    simpa [prefixWord, tailWord_1293215, baseEnd_1293215] using wordTrace_append hprefix tailTrace_1293215
  have hstable : (prefixWord ++ tailWord_1293215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293215).length < 2 ^ (prefixWord ++ tailWord_1293215).sum := by decide
  have hdescent : baseEnd_1293215 < baseStart_1293215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293258 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 3, 4]
def baseStart_1293258 : Nat := 118140960795 + 1293258 * 2 ^ 59
def prefixEnd_1293258 : Nat := 4983230072969 + 3 ^ 40 * 1293258 * 2
def baseEnd_1293258 : Nat := 442708642848270903884947

theorem tailTrace_1293258 : CollatzResearch.WordTrace tailWord_1293258 prefixEnd_1293258 442708642848270903884947 := by
  unfold tailWord_1293258
  simp only [CollatzResearch.WordTrace]
  refine ⟨11792248587188652931770107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31445996232503074484720285 11792248587188652931770107)
  ·
    refine ⟨17688372880782979397655161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11792248587188652931770107 17688372880782979397655161)
    ·
      refine ⟨13266279660587234548241371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17688372880782979397655161 13266279660587234548241371)
      ·
        refine ⟨19899419490880851822362057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13266279660587234548241371 19899419490880851822362057)
        ·
          refine ⟨14924564618160638866771543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19899419490880851822362057 14924564618160638866771543)
          ·
            refine ⟨22386846927240958300157315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14924564618160638866771543 22386846927240958300157315)
            ·
              refine ⟨33580270390861437450235973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22386846927240958300157315 33580270390861437450235973)
              ·
                refine ⟨6296300698286519521919245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33580270390861437450235973 6296300698286519521919245)
                ·
                  refine ⟨2361112761857444820719717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6296300698286519521919245 2361112761857444820719717)
                  ·
                    refine ⟨442708642848270903884947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2361112761857444820719717 442708642848270903884947)
                    ·
                      rfl

theorem cell22_1293258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_1293258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293258 prefixEnd_1293258 := by exact prefixLift 1293258
  have htrace : WordTrace (prefixWord ++ tailWord_1293258) baseStart_1293258 baseEnd_1293258 := by
    simpa [prefixWord, tailWord_1293258, baseEnd_1293258] using wordTrace_append hprefix tailTrace_1293258
  have hstable : (prefixWord ++ tailWord_1293258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293258).length < 2 ^ (prefixWord ++ tailWord_1293258).sum := by decide
  have hdescent : baseEnd_1293258 < baseStart_1293258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293262 : List Nat := [4, 1, 1, 1, 2, 5, 2, 1, 5]
def baseStart_1293262 : Nat := 118140960795 + 1293262 * 2 ^ 59
def prefixEnd_1293262 : Nat := 4983230072969 + 3 ^ 40 * 1293262 * 2
def baseEnd_1293262 : Nat := 147570004043338742261645

theorem tailTrace_1293262 : CollatzResearch.WordTrace tailWord_1293262 prefixEnd_1293262 147570004043338742261645 := by
  unfold tailWord_1293262
  simp only [CollatzResearch.WordTrace]
  refine ⟨5896142530092515051278255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31446093493826746940150693 5896142530092515051278255)
  ·
    refine ⟨8844213795138772576917383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5896142530092515051278255 8844213795138772576917383)
    ·
      refine ⟨13266320692708158865376075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8844213795138772576917383 13266320692708158865376075)
      ·
        refine ⟨19899481039062238298064113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13266320692708158865376075 19899481039062238298064113)
        ·
          refine ⟨14924610779296678723548085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19899481039062238298064113 14924610779296678723548085)
          ·
            refine ⟨1399182260559063630332633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14924610779296678723548085 1399182260559063630332633)
            ·
              refine ⟨1049386695419297722749475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1399182260559063630332633 1049386695419297722749475)
              ·
                refine ⟨1574080043128946584124213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1049386695419297722749475 1574080043128946584124213)
                ·
                  refine ⟨147570004043338742261645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1574080043128946584124213 147570004043338742261645)
                  ·
                    rfl

theorem cell22_1293262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_1293262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293262 prefixEnd_1293262 := by exact prefixLift 1293262
  have htrace : WordTrace (prefixWord ++ tailWord_1293262) baseStart_1293262 baseEnd_1293262 := by
    simpa [prefixWord, tailWord_1293262, baseEnd_1293262] using wordTrace_append hprefix tailTrace_1293262
  have hstable : (prefixWord ++ tailWord_1293262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293262).length < 2 ^ (prefixWord ++ tailWord_1293262).sum := by decide
  have hdescent : baseEnd_1293262 < baseStart_1293262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293288 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 3, 5]
def baseStart_1293288 : Nat := 118140960795 + 1293288 * 2 ^ 59
def prefixEnd_1293288 : Nat := 4983230072969 + 3 ^ 40 * 1293288 * 2
def baseEnd_1293288 : Nat := 442718912461360825634855

theorem tailTrace_1293288 : CollatzResearch.WordTrace tailWord_1293288 prefixEnd_1293288 442718912461360825634855 := by
  unfold tailWord_1293288
  simp only [CollatzResearch.WordTrace]
  refine ⟨23585044269322963425336259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31446725692430617900448345 23585044269322963425336259)
  ·
    refine ⟨35377566403984445138004389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23585044269322963425336259 35377566403984445138004389)
    ·
      refine ⟨6633293700747083463375823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35377566403984445138004389 6633293700747083463375823)
      ·
        refine ⟨9949940551120625195063735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6633293700747083463375823 9949940551120625195063735)
        ·
          refine ⟨14924910826680937792595603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9949940551120625195063735 14924910826680937792595603)
          ·
            refine ⟨22387366240021406688893405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14924910826680937792595603 22387366240021406688893405)
            ·
              refine ⟨8395262340008027508335027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22387366240021406688893405 8395262340008027508335027)
              ·
                refine ⟨12592893510012041262502541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8395262340008027508335027 12592893510012041262502541)
                ·
                  refine ⟨4722335066254515473438453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12592893510012041262502541 4722335066254515473438453)
                  ·
                    refine ⟨442718912461360825634855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4722335066254515473438453 442718912461360825634855)
                    ·
                      rfl

theorem cell22_1293288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_1293288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293288 prefixEnd_1293288 := by exact prefixLift 1293288
  have htrace : WordTrace (prefixWord ++ tailWord_1293288) baseStart_1293288 baseEnd_1293288 := by
    simpa [prefixWord, tailWord_1293288, baseEnd_1293288] using wordTrace_append hprefix tailTrace_1293288
  have hstable : (prefixWord ++ tailWord_1293288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293288).length < 2 ^ (prefixWord ++ tailWord_1293288).sum := by decide
  have hdescent : baseEnd_1293288 < baseStart_1293288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293300 : List Nat := [2, 6, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_1293300 : Nat := 118140960795 + 1293300 * 2 ^ 59
def prefixEnd_1293300 : Nat := 4983230072969 + 3 ^ 40 * 1293300 * 2
def baseEnd_1293300 : Nat := 442723020306596794334819

theorem tailTrace_1293300 : CollatzResearch.WordTrace tailWord_1293300 prefixEnd_1293300 442723020306596794334819 := by
  unfold tailWord_1293300
  simp only [CollatzResearch.WordTrace]
  refine ⟨23585263107301226450054677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31447017476401635266739569 23585263107301226450054677)
  ·
    refine ⟨1105559208154744989846313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23585263107301226450054677 1105559208154744989846313)
    ·
      refine ⟨829169406116058742384735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1105559208154744989846313 829169406116058742384735)
      ·
        refine ⟨1243754109174088113577103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 829169406116058742384735 1243754109174088113577103)
        ·
          refine ⟨1865631163761132170365655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1243754109174088113577103 1865631163761132170365655)
          ·
            refine ⟨2798446745641698255548483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1865631163761132170365655 2798446745641698255548483)
            ·
              refine ⟨4197670118462547383322725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2798446745641698255548483 4197670118462547383322725)
              ·
                refine ⟨787063147211727634373011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4197670118462547383322725 787063147211727634373011)
                ·
                  refine ⟨1180594720817591451559517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 787063147211727634373011 1180594720817591451559517)
                  ·
                    refine ⟨442723020306596794334819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1180594720817591451559517 442723020306596794334819)
                    ·
                      rfl

theorem cell22_1293300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_1293300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293300 prefixEnd_1293300 := by exact prefixLift 1293300
  have htrace : WordTrace (prefixWord ++ tailWord_1293300) baseStart_1293300 baseEnd_1293300 := by
    simpa [prefixWord, tailWord_1293300, baseEnd_1293300] using wordTrace_append hprefix tailTrace_1293300
  have hstable : (prefixWord ++ tailWord_1293300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293300).length < 2 ^ (prefixWord ++ tailWord_1293300).sum := by decide
  have hdescent : baseEnd_1293300 < baseStart_1293300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293322 : List Nat := [3, 1, 2, 2, 3, 1, 2, 3, 2, 3]
def baseStart_1293322 : Nat := 118140960795 + 1293322 * 2 ^ 59
def prefixEnd_1293322 : Nat := 4983230072969 + 3 ^ 40 * 1293322 * 2
def baseEnd_1293322 : Nat := 442730551356196070284751

theorem tailTrace_1293322 : CollatzResearch.WordTrace tailWord_1293322 prefixEnd_1293322 442730551356196070284751 := by
  unfold tailWord_1293322
  simp only [CollatzResearch.WordTrace]
  refine ⟨11792832155130687664352555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31447552413681833771606813 11792832155130687664352555)
  ·
    refine ⟨17689248232696031496528833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11792832155130687664352555 17689248232696031496528833)
    ·
      refine ⟨13266936174522023622396625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17689248232696031496528833 13266936174522023622396625)
      ·
        refine ⟨9950202130891517716797469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13266936174522023622396625 9950202130891517716797469)
        ·
          refine ⟨3731325799084319143799051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9950202130891517716797469 3731325799084319143799051)
          ·
            refine ⟨5596988698626478715698577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3731325799084319143799051 5596988698626478715698577)
            ·
              refine ⟨4197741523969859036773933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5596988698626478715698577 4197741523969859036773933)
              ·
                refine ⟨1574153071488697138790225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4197741523969859036773933 1574153071488697138790225)
                ·
                  refine ⟨1180614803616522854092669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1574153071488697138790225 1180614803616522854092669)
                  ·
                    refine ⟨442730551356196070284751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1180614803616522854092669 442730551356196070284751)
                    ·
                      rfl

theorem cell22_1293322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_1293322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293322 prefixEnd_1293322 := by exact prefixLift 1293322
  have htrace : WordTrace (prefixWord ++ tailWord_1293322) baseStart_1293322 baseEnd_1293322 := by
    simpa [prefixWord, tailWord_1293322, baseEnd_1293322] using wordTrace_append hprefix tailTrace_1293322
  have hstable : (prefixWord ++ tailWord_1293322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293322).length < 2 ^ (prefixWord ++ tailWord_1293322).sum := by decide
  have hdescent : baseEnd_1293322 < baseStart_1293322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293444 : List Nat := [2, 3, 2, 1, 2, 4, 1, 2, 1, 4]
def baseStart_1293444 : Nat := 118140960795 + 1293444 * 2 ^ 59
def prefixEnd_1293444 : Nat := 4983230072969 + 3 ^ 40 * 1293444 * 2
def baseEnd_1293444 : Nat := 442772314449428418734377

theorem tailTrace_1293444 : CollatzResearch.WordTrace tailWord_1293444 prefixEnd_1293444 442772314449428418734377 := by
  unfold tailWord_1293444
  simp only [CollatzResearch.WordTrace]
  refine ⟨23587889163040382746675693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31450518884053843662234257 23587889163040382746675693)
  ·
    refine ⟨8845458436140143530003385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23587889163040382746675693 8845458436140143530003385)
    ·
      refine ⟨6634093827105107647502539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8845458436140143530003385 6634093827105107647502539)
      ·
        refine ⟨9951140740657661471253809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6634093827105107647502539 9951140740657661471253809)
        ·
          refine ⟨7463355555493246103440357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9951140740657661471253809 7463355555493246103440357)
          ·
            refine ⟨1399379166654983644395067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7463355555493246103440357 1399379166654983644395067)
            ·
              refine ⟨2099068749982475466592601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1399379166654983644395067 2099068749982475466592601)
              ·
                refine ⟨1574301562486856599944451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2099068749982475466592601 1574301562486856599944451)
                ·
                  refine ⟨2361452343730284899916677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1574301562486856599944451 2361452343730284899916677)
                  ·
                    refine ⟨442772314449428418734377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2361452343730284899916677 442772314449428418734377)
                    ·
                      rfl

theorem cell22_1293444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_1293444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293444 prefixEnd_1293444 := by exact prefixLift 1293444
  have htrace : WordTrace (prefixWord ++ tailWord_1293444) baseStart_1293444 baseEnd_1293444 := by
    simpa [prefixWord, tailWord_1293444, baseEnd_1293444] using wordTrace_append hprefix tailTrace_1293444
  have hstable : (prefixWord ++ tailWord_1293444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293444).length < 2 ^ (prefixWord ++ tailWord_1293444).sum := by decide
  have hdescent : baseEnd_1293444 < baseStart_1293444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293476 : List Nat := [2, 3, 1, 2, 3, 3, 2, 2, 4]
def baseStart_1293476 : Nat := 118140960795 + 1293476 * 2 ^ 59
def prefixEnd_1293476 : Nat := 4983230072969 + 3 ^ 40 * 1293476 * 2
def baseEnd_1293476 : Nat := 147594422901130333978093

theorem tailTrace_1293476 : CollatzResearch.WordTrace tailWord_1293476 prefixEnd_1293476 147594422901130333978093 := by
  unfold tailWord_1293476
  simp only [CollatzResearch.WordTrace]
  refine ⟨23588472730982417479258141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31451296974643223305677521 23588472730982417479258141)
  ·
    refine ⟨8845677274118406554721803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23588472730982417479258141 8845677274118406554721803)
    ·
      refine ⟨13268515911177609832082705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8845677274118406554721803 13268515911177609832082705)
      ·
        refine ⟨9951386933383207374062029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13268515911177609832082705 9951386933383207374062029)
        ·
          refine ⟨3731770100018702765273261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9951386933383207374062029 3731770100018702765273261)
          ·
            refine ⟨1399413787507013536977473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3731770100018702765273261 1399413787507013536977473)
            ·
              refine ⟨1049560340630260152733105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1399413787507013536977473 1049560340630260152733105)
              ·
                refine ⟨787170255472695114549829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1049560340630260152733105 787170255472695114549829)
                ·
                  refine ⟨147594422901130333978093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 787170255472695114549829 147594422901130333978093)
                  ·
                    rfl

theorem cell22_1293476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_1293476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293476 prefixEnd_1293476 := by exact prefixLift 1293476
  have htrace : WordTrace (prefixWord ++ tailWord_1293476) baseStart_1293476 baseEnd_1293476 := by
    simpa [prefixWord, tailWord_1293476, baseEnd_1293476] using wordTrace_append hprefix tailTrace_1293476
  have hstable : (prefixWord ++ tailWord_1293476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293476).length < 2 ^ (prefixWord ++ tailWord_1293476).sum := by decide
  have hdescent : baseEnd_1293476 < baseStart_1293476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293506 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_1293506 : Nat := 118140960795 + 1293506 * 2 ^ 59
def prefixEnd_1293506 : Nat := 4983230072969 + 3 ^ 40 * 1293506 * 2
def baseEnd_1293506 : Nat := 442793538316480923684187

theorem tailTrace_1293506 : CollatzResearch.WordTrace tailWord_1293506 prefixEnd_1293506 442793538316480923684187 := by
  unfold tailWord_1293506
  simp only [CollatzResearch.WordTrace]
  refine ⟨11794509912964037520527093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31452026434570766721405581 11794509912964037520527093)
  ·
    refine ⟨1105735304340378517549415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11794509912964037520527093 1105735304340378517549415)
    ·
      refine ⟨1658602956510567776324123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1105735304340378517549415 1658602956510567776324123)
      ·
        refine ⟨2487904434765851664486185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1658602956510567776324123 2487904434765851664486185)
        ·
          refine ⟨1865928326074388748364639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2487904434765851664486185 1865928326074388748364639)
          ·
            refine ⟨2798892489111583122546959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1865928326074388748364639 2798892489111583122546959)
            ·
              refine ⟨4198338733667374683820439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2798892489111583122546959 4198338733667374683820439)
              ·
                refine ⟨6297508100501062025730659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4198338733667374683820439 6297508100501062025730659)
                ·
                  refine ⟨9446262150751593038595989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6297508100501062025730659 9446262150751593038595989)
                  ·
                    refine ⟨442793538316480923684187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9446262150751593038595989 442793538316480923684187)
                    ·
                      rfl

theorem cell22_1293506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_1293506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293506 prefixEnd_1293506 := by exact prefixLift 1293506
  have htrace : WordTrace (prefixWord ++ tailWord_1293506) baseStart_1293506 baseEnd_1293506 := by
    simpa [prefixWord, tailWord_1293506, baseEnd_1293506] using wordTrace_append hprefix tailTrace_1293506
  have hstable : (prefixWord ++ tailWord_1293506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293506).length < 2 ^ (prefixWord ++ tailWord_1293506).sum := by decide
  have hdescent : baseEnd_1293506 < baseStart_1293506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293510 : List Nat := [6, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_1293510 : Nat := 118140960795 + 1293510 * 2 ^ 59
def prefixEnd_1293510 : Nat := 4983230072969 + 3 ^ 40 * 1293510 * 2
def baseEnd_1293510 : Nat := 147598302532742082194725

theorem tailTrace_1293510 : CollatzResearch.WordTrace tailWord_1293510 prefixEnd_1293510 147598302532742082194725 := by
  unfold tailWord_1293510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1474318298245051836414187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31452123695894439176835989 1474318298245051836414187)
  ·
    refine ⟨2211477447367577754621281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1474318298245051836414187 2211477447367577754621281)
    ·
      refine ⟨1658608085525683315965961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2211477447367577754621281 1658608085525683315965961)
      ·
        refine ⟨1243956064144262486974471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1658608085525683315965961 1243956064144262486974471)
        ·
          refine ⟨1865934096216393730461707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1243956064144262486974471 1865934096216393730461707)
          ·
            refine ⟨2798901144324590595692561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1865934096216393730461707 2798901144324590595692561)
            ·
              refine ⟨2099175858243442946769421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2798901144324590595692561 2099175858243442946769421)
              ·
                refine ⟨787190946841291105038533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2099175858243442946769421 787190946841291105038533)
                ·
                  refine ⟨147598302532742082194725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 787190946841291105038533 147598302532742082194725)
                  ·
                    rfl

theorem cell22_1293510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_1293510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293510 prefixEnd_1293510 := by exact prefixLift 1293510
  have htrace : WordTrace (prefixWord ++ tailWord_1293510) baseStart_1293510 baseEnd_1293510 := by
    simpa [prefixWord, tailWord_1293510, baseEnd_1293510] using wordTrace_append hprefix tailTrace_1293510
  have hstable : (prefixWord ++ tailWord_1293510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293510).length < 2 ^ (prefixWord ++ tailWord_1293510).sum := by decide
  have hdescent : baseEnd_1293510 < baseStart_1293510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293570 : List Nat := [3, 4, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_1293570 : Nat := 118140960795 + 1293570 * 2 ^ 59
def prefixEnd_1293570 : Nat := 4983230072969 + 3 ^ 40 * 1293570 * 2
def baseEnd_1293570 : Nat := 442815446824406090083991

theorem tailTrace_1293570 : CollatzResearch.WordTrace tailWord_1293570 prefixEnd_1293570 442815446824406090083991 := by
  unfold tailWord_1293570
  simp only [CollatzResearch.WordTrace]
  refine ⟨11795093480906072253109541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31453582615749526008292109 11795093480906072253109541)
  ·
    refine ⟨2211580027669888547458039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11795093480906072253109541 2211580027669888547458039)
    ·
      refine ⟨3317370041504832821187059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2211580027669888547458039 3317370041504832821187059)
      ·
        refine ⟨4976055062257249231780589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3317370041504832821187059 4976055062257249231780589)
        ·
          refine ⟨1866020648346468461917721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4976055062257249231780589 1866020648346468461917721)
          ·
            refine ⟨1399515486259851346438291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1866020648346468461917721 1399515486259851346438291)
            ·
              refine ⟨2099273229389777019657437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1399515486259851346438291 2099273229389777019657437)
              ·
                refine ⟨787227461021166382371539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2099273229389777019657437 787227461021166382371539)
                ·
                  refine ⟨1180841191531749573557309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 787227461021166382371539 1180841191531749573557309)
                  ·
                    refine ⟨442815446824406090083991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1180841191531749573557309 442815446824406090083991)
                    ·
                      rfl

theorem cell22_1293570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_1293570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293570 prefixEnd_1293570 := by exact prefixLift 1293570
  have htrace : WordTrace (prefixWord ++ tailWord_1293570) baseStart_1293570 baseEnd_1293570 := by
    simpa [prefixWord, tailWord_1293570, baseEnd_1293570] using wordTrace_append hprefix tailTrace_1293570
  have hstable : (prefixWord ++ tailWord_1293570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293570).length < 2 ^ (prefixWord ++ tailWord_1293570).sum := by decide
  have hdescent : baseEnd_1293570 < baseStart_1293570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293594 : List Nat := [3, 1, 1, 3, 3, 3, 1, 1, 6]
def baseStart_1293594 : Nat := 118140960795 + 1293594 * 2 ^ 59
def prefixEnd_1293594 : Nat := 4983230072969 + 3 ^ 40 * 1293594 * 2
def baseEnd_1293594 : Nat := 147607887504959342494639

theorem tailTrace_1293594 : CollatzResearch.WordTrace tailWord_1293594 prefixEnd_1293594 147607887504959342494639 := by
  unfold tailWord_1293594
  simp only [CollatzResearch.WordTrace]
  refine ⟨11795312318884335277827959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31454166183691560740874557 11795312318884335277827959)
  ·
    refine ⟨17692968478326502916741939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11795312318884335277827959 17692968478326502916741939)
    ·
      refine ⟨26539452717489754375112909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17692968478326502916741939 26539452717489754375112909)
      ·
        refine ⟨9952294769058657890667341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26539452717489754375112909 9952294769058657890667341)
        ·
          refine ⟨3732110538396996709000253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9952294769058657890667341 3732110538396996709000253)
          ·
            refine ⟨1399541451898873765875095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3732110538396996709000253 1399541451898873765875095)
            ·
              refine ⟨2099312177848310648812643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1399541451898873765875095 2099312177848310648812643)
              ·
                refine ⟨3148968266772465973218965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2099312177848310648812643 3148968266772465973218965)
                ·
                  refine ⟨147607887504959342494639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3148968266772465973218965 147607887504959342494639)
                  ·
                    rfl

theorem cell22_1293594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 6].length) (baseStart_1293594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293594 prefixEnd_1293594 := by exact prefixLift 1293594
  have htrace : WordTrace (prefixWord ++ tailWord_1293594) baseStart_1293594 baseEnd_1293594 := by
    simpa [prefixWord, tailWord_1293594, baseEnd_1293594] using wordTrace_append hprefix tailTrace_1293594
  have hstable : (prefixWord ++ tailWord_1293594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293594).length < 2 ^ (prefixWord ++ tailWord_1293594).sum := by decide
  have hdescent : baseEnd_1293594 < baseStart_1293594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293613 : List Nat := [1, 5, 3, 1, 1, 3, 1, 2, 1, 4]
def baseStart_1293613 : Nat := 118140960795 + 1293613 * 2 ^ 59
def prefixEnd_1293613 : Nat := 4983230072969 + 3 ^ 40 * 1293613 * 2
def baseEnd_1293613 : Nat := 442830166603168311258859

theorem tailTrace_1293613 : CollatzResearch.WordTrace tailWord_1293613 prefixEnd_1293613 442830166603168311258859 := by
  unfold tailWord_1293613
  simp only [CollatzResearch.WordTrace]
  refine ⟨47181942262468507356253493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31454628174979004904168995 47181942262468507356253493)
  ·
    refine ⟨4423307087106422564648765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47181942262468507356253493 4423307087106422564648765)
    ·
      refine ⟨1658740157664908461743287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4423307087106422564648765 1658740157664908461743287)
      ·
        refine ⟨2488110236497362692614931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1658740157664908461743287 2488110236497362692614931)
        ·
          refine ⟨3732165354746044038922397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2488110236497362692614931 3732165354746044038922397)
          ·
            refine ⟨1399562008029766514595899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3732165354746044038922397 1399562008029766514595899)
            ·
              refine ⟨2099343012044649771893849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1399562008029766514595899 2099343012044649771893849)
              ·
                refine ⟨1574507259033487328920387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2099343012044649771893849 1574507259033487328920387)
                ·
                  refine ⟨2361760888550230993380581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1574507259033487328920387 2361760888550230993380581)
                  ·
                    refine ⟨442830166603168311258859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2361760888550230993380581 442830166603168311258859)
                    ·
                      rfl

theorem cell22_1293613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_1293613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293613 prefixEnd_1293613 := by exact prefixLift 1293613
  have htrace : WordTrace (prefixWord ++ tailWord_1293613) baseStart_1293613 baseEnd_1293613 := by
    simpa [prefixWord, tailWord_1293613, baseEnd_1293613] using wordTrace_append hprefix tailTrace_1293613
  have hstable : (prefixWord ++ tailWord_1293613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293613).length < 2 ^ (prefixWord ++ tailWord_1293613).sum := by decide
  have hdescent : baseEnd_1293613 < baseStart_1293613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293652 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_1293652 : Nat := 118140960795 + 1293652 * 2 ^ 59
def prefixEnd_1293652 : Nat := 4983230072969 + 3 ^ 40 * 1293652 * 2
def baseEnd_1293652 : Nat := 442843517100185209533739

theorem tailTrace_1293652 : CollatzResearch.WordTrace tailWord_1293652 prefixEnd_1293652 442843517100185209533739 := by
  unfold tailWord_1293652
  simp only [CollatzResearch.WordTrace]
  refine ⟨23591682354663608508461605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31455576472884811344615473 23591682354663608508461605)
  ·
    refine ⟨4423440441499426595336551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23591682354663608508461605 4423440441499426595336551)
    ·
      refine ⟨6635160662249139893004827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4423440441499426595336551 6635160662249139893004827)
      ·
        refine ⟨9952740993373709839507241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6635160662249139893004827 9952740993373709839507241)
        ·
          refine ⟨7464555745030282379630431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9952740993373709839507241 7464555745030282379630431)
          ·
            refine ⟨11196833617545423569445647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7464555745030282379630431 11196833617545423569445647)
            ·
              refine ⟨16795250426318135354168471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11196833617545423569445647 16795250426318135354168471)
              ·
                refine ⟨25192875639477203031252707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16795250426318135354168471 25192875639477203031252707)
                ·
                  refine ⟨37789313459215804546879061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25192875639477203031252707 37789313459215804546879061)
                  ·
                    refine ⟨442843517100185209533739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37789313459215804546879061 442843517100185209533739)
                    ·
                      rfl

theorem cell22_1293652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_1293652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293652 prefixEnd_1293652 := by exact prefixLift 1293652
  have htrace : WordTrace (prefixWord ++ tailWord_1293652) baseStart_1293652 baseEnd_1293652 := by
    simpa [prefixWord, tailWord_1293652, baseEnd_1293652] using wordTrace_append hprefix tailTrace_1293652
  have hstable : (prefixWord ++ tailWord_1293652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293652).length < 2 ^ (prefixWord ++ tailWord_1293652).sum := by decide
  have hdescent : baseEnd_1293652 < baseStart_1293652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293671 : List Nat := [1, 1, 5, 1, 4, 1, 1, 2, 3, 3]
def baseStart_1293671 : Nat := 118140960795 + 1293671 * 2 ^ 59
def prefixEnd_1293671 : Nat := 4983230072969 + 3 ^ 40 * 1293671 * 2
def baseEnd_1293671 : Nat := 442850021188475493308681

theorem tailTrace_1293671 : CollatzResearch.WordTrace tailWord_1293671 prefixEnd_1293671 442850021188475493308681 := by
  unfold tailWord_1293671
  simp only [CollatzResearch.WordTrace]
  refine ⟨47184057696258383261864867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31456038464172255507909911 47184057696258383261864867)
  ·
    refine ⟨70776086544387574892797301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47184057696258383261864867 70776086544387574892797301)
    ·
      refine ⟨6635258113536335146199747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70776086544387574892797301 6635258113536335146199747)
      ·
        refine ⟨9952887170304502719299621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6635258113536335146199747 9952887170304502719299621)
        ·
          refine ⟨1866166344432094259868679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9952887170304502719299621 1866166344432094259868679)
          ·
            refine ⟨2799249516648141389803019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1866166344432094259868679 2799249516648141389803019)
            ·
              refine ⟨4198874274972212084704529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2799249516648141389803019 4198874274972212084704529)
              ·
                refine ⟨3149155706229159063528397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4198874274972212084704529 3149155706229159063528397)
                ·
                  refine ⟨1180933389835934648823149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3149155706229159063528397 1180933389835934648823149)
                  ·
                    refine ⟨442850021188475493308681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1180933389835934648823149 442850021188475493308681)
                    ·
                      rfl

theorem cell22_1293671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_1293671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293671 prefixEnd_1293671 := by exact prefixLift 1293671
  have htrace : WordTrace (prefixWord ++ tailWord_1293671) baseStart_1293671 baseEnd_1293671 := by
    simpa [prefixWord, tailWord_1293671, baseEnd_1293671] using wordTrace_append hprefix tailTrace_1293671
  have hstable : (prefixWord ++ tailWord_1293671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293671).length < 2 ^ (prefixWord ++ tailWord_1293671).sum := by decide
  have hdescent : baseEnd_1293671 < baseStart_1293671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293682 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 1, 7]
def baseStart_1293682 : Nat := 118140960795 + 1293682 * 2 ^ 59
def prefixEnd_1293682 : Nat := 4983230072969 + 3 ^ 40 * 1293682 * 2
def baseEnd_1293682 : Nat := 442853786713275131283647

theorem tailTrace_1293682 : CollatzResearch.WordTrace tailWord_1293682 prefixEnd_1293682 442853786713275131283647 := by
  unfold tailWord_1293682
  simp only [CollatzResearch.WordTrace]
  refine ⟨11796114724804633035128825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31456305932812354760343533 11796114724804633035128825)
  ·
    refine ⟨8847086043603474776346619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11796114724804633035128825 8847086043603474776346619)
    ·
      refine ⟨13270629065405212164519929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8847086043603474776346619 13270629065405212164519929)
      ·
        refine ⟨9952971799053909123389947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13270629065405212164519929 9952971799053909123389947)
        ·
          refine ⟨14929457698580863685084921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9952971799053909123389947 14929457698580863685084921)
          ·
            refine ⟨11197093273935647763813691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14929457698580863685084921 11197093273935647763813691)
            ·
              refine ⟨16795639910903471645720537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11197093273935647763813691 16795639910903471645720537)
              ·
                refine ⟨12596729933177603734290403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16795639910903471645720537 12596729933177603734290403)
                ·
                  refine ⟨18895094899766405601435605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12596729933177603734290403 18895094899766405601435605)
                  ·
                    refine ⟨442853786713275131283647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18895094899766405601435605 442853786713275131283647)
                    ·
                      rfl

theorem cell22_1293682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_1293682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293682 prefixEnd_1293682 := by exact prefixLift 1293682
  have htrace : WordTrace (prefixWord ++ tailWord_1293682) baseStart_1293682 baseEnd_1293682 := by
    simpa [prefixWord, tailWord_1293682, baseEnd_1293682] using wordTrace_append hprefix tailTrace_1293682
  have hstable : (prefixWord ++ tailWord_1293682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293682).length < 2 ^ (prefixWord ++ tailWord_1293682).sum := by decide
  have hdescent : baseEnd_1293682 < baseStart_1293682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293834 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 1, 7]
def baseStart_1293834 : Nat := 118140960795 + 1293834 * 2 ^ 59
def prefixEnd_1293834 : Nat := 4983230072969 + 3 ^ 40 * 1293834 * 2
def baseEnd_1293834 : Nat := 442905819419597401483181

theorem tailTrace_1293834 : CollatzResearch.WordTrace tailWord_1293834 prefixEnd_1293834 442905819419597401483181 := by
  unfold tailWord_1293834
  simp only [CollatzResearch.WordTrace]
  refine ⟨11797500698666965525012139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31460001863111908066699037 11797500698666965525012139)
  ·
    refine ⟨17696251048000448287518209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11797500698666965525012139 17696251048000448287518209)
    ·
      refine ⟨13272188286000336215638657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17696251048000448287518209 13272188286000336215638657)
      ·
        refine ⟨9954141214500252161728993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13272188286000336215638657 9954141214500252161728993)
        ·
          refine ⟨7465605910875189121296745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9954141214500252161728993 7465605910875189121296745)
          ·
            refine ⟨5599204433156391840972559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7465605910875189121296745 5599204433156391840972559)
            ·
              refine ⟨8398806649734587761458839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5599204433156391840972559 8398806649734587761458839)
              ·
                refine ⟨12598209974601881642188259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8398806649734587761458839 12598209974601881642188259)
                ·
                  refine ⟨18897314961902822463282389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12598209974601881642188259 18897314961902822463282389)
                  ·
                    refine ⟨442905819419597401483181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18897314961902822463282389 442905819419597401483181)
                    ·
                      rfl

theorem cell22_1293834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_1293834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293834 prefixEnd_1293834 := by exact prefixLift 1293834
  have htrace : WordTrace (prefixWord ++ tailWord_1293834) baseStart_1293834 baseEnd_1293834 := by
    simpa [prefixWord, tailWord_1293834, baseEnd_1293834] using wordTrace_append hprefix tailTrace_1293834
  have hstable : (prefixWord ++ tailWord_1293834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293834).length < 2 ^ (prefixWord ++ tailWord_1293834).sum := by decide
  have hdescent : baseEnd_1293834 < baseStart_1293834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293881 : List Nat := [1, 2, 1, 5, 1, 3, 2, 1, 6]
def baseStart_1293881 : Nat := 118140960795 + 1293881 * 2 ^ 59
def prefixEnd_1293881 : Nat := 4983230072969 + 3 ^ 40 * 1293881 * 2
def baseEnd_1293881 : Nat := 147640636160034981852679

theorem tailTrace_1293881 : CollatzResearch.WordTrace tailWord_1293881 prefixEnd_1293881 147640636160034981852679 := by
  unfold tailWord_1293881
  simp only [CollatzResearch.WordTrace]
  refine ⟨47191717025497589127009497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31461144683665059418006331 47191717025497589127009497)
  ·
    refine ⟨35393787769123191845257123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47191717025497589127009497 35393787769123191845257123)
    ·
      refine ⟨53090681653684787767885685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35393787769123191845257123 53090681653684787767885685)
      ·
        refine ⟨4977251405032948853239283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53090681653684787767885685 4977251405032948853239283)
        ·
          refine ⟨7465877107549423279858925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4977251405032948853239283 7465877107549423279858925)
          ·
            refine ⟨2799703915331033729947097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7465877107549423279858925 2799703915331033729947097)
            ·
              refine ⟨2099777936498275297460323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2799703915331033729947097 2099777936498275297460323)
              ·
                refine ⟨3149666904747412946190485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2099777936498275297460323 3149666904747412946190485)
                ·
                  refine ⟨147640636160034981852679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3149666904747412946190485 147640636160034981852679)
                  ·
                    rfl

theorem cell22_1293881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 6].length) (baseStart_1293881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293881 prefixEnd_1293881 := by exact prefixLift 1293881
  have htrace : WordTrace (prefixWord ++ tailWord_1293881) baseStart_1293881 baseEnd_1293881 := by
    simpa [prefixWord, tailWord_1293881, baseEnd_1293881] using wordTrace_append hprefix tailTrace_1293881
  have hstable : (prefixWord ++ tailWord_1293881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293881).length < 2 ^ (prefixWord ++ tailWord_1293881).sum := by decide
  have hdescent : baseEnd_1293881 < baseStart_1293881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293928 : List Nat := [2, 1, 4, 3, 1, 2, 1, 2, 2, 4]
def baseStart_1293928 : Nat := 118140960795 + 1293928 * 2 ^ 59
def prefixEnd_1293928 : Nat := 4983230072969 + 3 ^ 40 * 1293928 * 2
def baseEnd_1293928 : Nat := 442937997540612489632893

theorem tailTrace_1293928 : CollatzResearch.WordTrace tailWord_1293928 prefixEnd_1293928 442937997540612489632893 := by
  unfold tailWord_1293928
  simp only [CollatzResearch.WordTrace]
  refine ⟨23596715628163658076985219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31462287504218210769313625 23596715628163658076985219)
  ·
    refine ⟨35395073442245487115477829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23596715628163658076985219 35395073442245487115477829)
    ·
      refine ⟨6636576270421028834152093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35395073442245487115477829 6636576270421028834152093)
      ·
        refine ⟨2488716101407885812807035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6636576270421028834152093 2488716101407885812807035)
        ·
          refine ⟨3733074152111828719210553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2488716101407885812807035 3733074152111828719210553)
          ·
            refine ⟨2799805614083871539407915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3733074152111828719210553 2799805614083871539407915)
            ·
              refine ⟨4199708421125807309111873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2799805614083871539407915 4199708421125807309111873)
              ·
                refine ⟨3149781315844355481833905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4199708421125807309111873 3149781315844355481833905)
                ·
                  refine ⟨2362335986883266611375429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3149781315844355481833905 2362335986883266611375429)
                  ·
                    refine ⟨442937997540612489632893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2362335986883266611375429 442937997540612489632893)
                    ·
                      rfl

theorem cell22_1293928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_1293928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293928 prefixEnd_1293928 := by exact prefixLift 1293928
  have htrace : WordTrace (prefixWord ++ tailWord_1293928) baseStart_1293928 baseEnd_1293928 := by
    simpa [prefixWord, tailWord_1293928, baseEnd_1293928] using wordTrace_append hprefix tailTrace_1293928
  have hstable : (prefixWord ++ tailWord_1293928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293928).length < 2 ^ (prefixWord ++ tailWord_1293928).sum := by decide
  have hdescent : baseEnd_1293928 < baseStart_1293928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293969 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 3, 7]
def baseStart_1293969 : Nat := 118140960795 + 1293969 * 2 ^ 59
def prefixEnd_1293969 : Nat := 4983230072969 + 3 ^ 40 * 1293969 * 2
def baseEnd_1293969 : Nat := 442952032678502049357767

theorem tailTrace_1293969 : CollatzResearch.WordTrace tailWord_1293969 prefixEnd_1293969 442952032678502049357767 := by
  unfold tailWord_1293969
  simp only [CollatzResearch.WordTrace]
  refine ⟨47194926649178780156212961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31463284432785853437475307 47194926649178780156212961)
  ·
    refine ⟨35396194986884085117159721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47194926649178780156212961 35396194986884085117159721)
    ·
      refine ⟨26547146240163063837869791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35396194986884085117159721 26547146240163063837869791)
      ·
        refine ⟨39820719360244595756804687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26547146240163063837869791 39820719360244595756804687)
        ·
          refine ⟨59731079040366893635207031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39820719360244595756804687 59731079040366893635207031)
          ·
            refine ⟨89596618560550340452810547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59731079040366893635207031 89596618560550340452810547)
            ·
              refine ⟨134394927840825510679215821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89596618560550340452810547 134394927840825510679215821)
              ·
                refine ⟨50398097940309566504705933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134394927840825510679215821 50398097940309566504705933)
                ·
                  refine ⟨18899286727616087439264725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50398097940309566504705933 18899286727616087439264725)
                  ·
                    refine ⟨442952032678502049357767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18899286727616087439264725 442952032678502049357767)
                    ·
                      rfl

theorem cell22_1293969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_1293969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293969 prefixEnd_1293969 := by exact prefixLift 1293969
  have htrace : WordTrace (prefixWord ++ tailWord_1293969) baseStart_1293969 baseEnd_1293969 := by
    simpa [prefixWord, tailWord_1293969, baseEnd_1293969] using wordTrace_append hprefix tailTrace_1293969
  have hstable : (prefixWord ++ tailWord_1293969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293969).length < 2 ^ (prefixWord ++ tailWord_1293969).sum := by decide
  have hdescent : baseEnd_1293969 < baseStart_1293969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293988 : List Nat := [2, 3, 1, 2, 2, 3, 2, 2, 5]
def baseStart_1293988 : Nat := 118140960795 + 1293988 * 2 ^ 59
def prefixEnd_1293988 : Nat := 4983230072969 + 3 ^ 40 * 1293988 * 2
def baseEnd_1293988 : Nat := 147652845588930777710903

theorem tailTrace_1293988 : CollatzResearch.WordTrace tailWord_1293988 prefixEnd_1293988 147652845588930777710903 := by
  unfold tailWord_1293988
  simp only [CollatzResearch.WordTrace]
  refine ⟨23597809818054973200577309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31463746424073297600769745 23597809818054973200577309)
  ·
    refine ⟨8849178681770614950216491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23597809818054973200577309 8849178681770614950216491)
    ·
      refine ⟨13273768022655922425324737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8849178681770614950216491 13273768022655922425324737)
      ·
        refine ⟨9955326016991941818993553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13273768022655922425324737 9955326016991941818993553)
        ·
          refine ⟨7466494512743956364245165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9955326016991941818993553 7466494512743956364245165)
          ·
            refine ⟨2799935442278983636591937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7466494512743956364245165 2799935442278983636591937)
            ·
              refine ⟨2099951581709237727443953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2799935442278983636591937 2099951581709237727443953)
              ·
                refine ⟨1574963686281928295582965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2099951581709237727443953 1574963686281928295582965)
                ·
                  refine ⟨147652845588930777710903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1574963686281928295582965 147652845588930777710903)
                  ·
                    rfl

theorem cell22_1293988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_1293988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1293988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1293988 prefixEnd_1293988 := by exact prefixLift 1293988
  have htrace : WordTrace (prefixWord ++ tailWord_1293988) baseStart_1293988 baseEnd_1293988 := by
    simpa [prefixWord, tailWord_1293988, baseEnd_1293988] using wordTrace_append hprefix tailTrace_1293988
  have hstable : (prefixWord ++ tailWord_1293988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293988).length < 2 ^ (prefixWord ++ tailWord_1293988).sum := by decide
  have hdescent : baseEnd_1293988 < baseStart_1293988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294016 : List Nat := [2, 1, 1, 2, 4, 1, 3, 2, 6]
def baseStart_1294016 : Nat := 118140960795 + 1294016 * 2 ^ 59
def prefixEnd_1294016 : Nat := 4983230072969 + 3 ^ 40 * 1294016 * 2
def baseEnd_1294016 : Nat := 147656040579669864477541

theorem tailTrace_1294016 : CollatzResearch.WordTrace tailWord_1294016 prefixEnd_1294016 147656040579669864477541 := by
  unfold tailWord_1294016
  simp only [CollatzResearch.WordTrace]
  refine ⟨23598320440004253591586951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31464427253339004788782601 23598320440004253591586951)
  ·
    refine ⟨35397480660006380387380427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23598320440004253591586951 35397480660006380387380427)
    ·
      refine ⟨53096220990009570581070641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35397480660006380387380427 53096220990009570581070641)
      ·
        refine ⟨39822165742507177935802981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53096220990009570581070641 39822165742507177935802981)
        ·
          refine ⟨7466656076720095862963059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39822165742507177935802981 7466656076720095862963059)
          ·
            refine ⟨11199984115080143794444589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7466656076720095862963059 11199984115080143794444589)
            ·
              refine ⟨4199994043155053922916721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11199984115080143794444589 4199994043155053922916721)
              ·
                refine ⟨3149995532366290442187541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4199994043155053922916721 3149995532366290442187541)
                ·
                  refine ⟨147656040579669864477541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3149995532366290442187541 147656040579669864477541)
                  ·
                    rfl

theorem cell22_1294016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 6].length) (baseStart_1294016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294016 prefixEnd_1294016 := by exact prefixLift 1294016
  have htrace : WordTrace (prefixWord ++ tailWord_1294016) baseStart_1294016 baseEnd_1294016 := by
    simpa [prefixWord, tailWord_1294016, baseEnd_1294016] using wordTrace_append hprefix tailTrace_1294016
  have hstable : (prefixWord ++ tailWord_1294016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294016).length < 2 ^ (prefixWord ++ tailWord_1294016).sum := by decide
  have hdescent : baseEnd_1294016 < baseStart_1294016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294033 : List Nat := [1, 2, 2, 1, 2, 4, 1, 5, 4]
def baseStart_1294033 : Nat := 118140960795 + 1294033 * 2 ^ 59
def prefixEnd_1294033 : Nat := 4983230072969 + 3 ^ 40 * 1294033 * 2
def baseEnd_1294033 : Nat := 147657980395475738585857

theorem tailTrace_1294033 : CollatzResearch.WordTrace tailWord_1294033 prefixEnd_1294033 147657980395475738585857 := by
  unfold tailWord_1294033
  simp only [CollatzResearch.WordTrace]
  refine ⟨47197260920946919086542753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31464840613964612724361835 47197260920946919086542753)
  ·
    refine ⟨35397945690710189314907065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47197260920946919086542753 35397945690710189314907065)
    ·
      refine ⟨26548459268032641986180299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35397945690710189314907065 26548459268032641986180299)
      ·
        refine ⟨39822688902048962979270449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26548459268032641986180299 39822688902048962979270449)
        ·
          refine ⟨29867016676536722234452837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39822688902048962979270449 29867016676536722234452837)
          ·
            refine ⟨5600065626850635418959907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29867016676536722234452837 5600065626850635418959907)
            ·
              refine ⟨8400098440275953128439861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5600065626850635418959907 8400098440275953128439861)
              ·
                refine ⟨787509228775870605791237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8400098440275953128439861 787509228775870605791237)
                ·
                  refine ⟨147657980395475738585857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 787509228775870605791237 147657980395475738585857)
                  ·
                    rfl

theorem cell22_1294033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 4].length) (baseStart_1294033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294033 prefixEnd_1294033 := by exact prefixLift 1294033
  have htrace : WordTrace (prefixWord ++ tailWord_1294033) baseStart_1294033 baseEnd_1294033 := by
    simpa [prefixWord, tailWord_1294033, baseEnd_1294033] using wordTrace_append hprefix tailTrace_1294033
  have hstable : (prefixWord ++ tailWord_1294033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294033).length < 2 ^ (prefixWord ++ tailWord_1294033).sum := by decide
  have hdescent : baseEnd_1294033 < baseStart_1294033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294076 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 2, 7]
def baseStart_1294076 : Nat := 118140960795 + 1294076 * 2 ^ 59
def prefixEnd_1294076 : Nat := 4983230072969 + 3 ^ 40 * 1294076 * 2
def baseEnd_1294076 : Nat := 442988660965189436932439

theorem tailTrace_1294076 : CollatzResearch.WordTrace tailWord_1294076 prefixEnd_1294076 442988660965189436932439 := by
  unfold tailWord_1294076
  simp only [CollatzResearch.WordTrace]
  refine ⟨23599414629895568715179041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31465886173194091620238721 23599414629895568715179041)
  ·
    refine ⟨17699560972421676536384281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23599414629895568715179041 17699560972421676536384281)
    ·
      refine ⟨13274670729316257402288211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17699560972421676536384281 13274670729316257402288211)
      ·
        refine ⟨19912006093974386103432317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13274670729316257402288211 19912006093974386103432317)
        ·
          refine ⟨7467002285240394788787119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19912006093974386103432317 7467002285240394788787119)
          ·
            refine ⟨11200503427860592183180679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7467002285240394788787119 11200503427860592183180679)
            ·
              refine ⟨16800755141790888274771019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11200503427860592183180679 16800755141790888274771019)
              ·
                refine ⟨25201132712686332412156529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16800755141790888274771019 25201132712686332412156529)
                ·
                  refine ⟨18900849534514749309117397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25201132712686332412156529 18900849534514749309117397)
                  ·
                    refine ⟨442988660965189436932439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18900849534514749309117397 442988660965189436932439)
                    ·
                      rfl

theorem cell22_1294076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_1294076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294076 prefixEnd_1294076 := by exact prefixLift 1294076
  have htrace : WordTrace (prefixWord ++ tailWord_1294076) baseStart_1294076 baseEnd_1294076 := by
    simpa [prefixWord, tailWord_1294076, baseEnd_1294076] using wordTrace_append hprefix tailTrace_1294076
  have hstable : (prefixWord ++ tailWord_1294076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294076).length < 2 ^ (prefixWord ++ tailWord_1294076).sum := by decide
  have hdescent : baseEnd_1294076 < baseStart_1294076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294157 : List Nat := [1, 6, 1, 2, 1, 2, 2, 2, 5]
def baseStart_1294157 : Nat := 118140960795 + 1294157 * 2 ^ 59
def prefixEnd_1294157 : Nat := 4983230072969 + 3 ^ 40 * 1294157 * 2
def baseEnd_1294157 : Nat := 147672129640177408552397

theorem tailTrace_1294157 : CollatzResearch.WordTrace tailWord_1294157 prefixEnd_1294157 147672129640177408552397 := by
  unfold tailWord_1294157
  simp only [CollatzResearch.WordTrace]
  refine ⟨47201783572497688264056725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31467855714998458842704483 47201783572497688264056725)
  ·
    refine ⟨2212583604960829137377659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47201783572497688264056725 2212583604960829137377659)
    ·
      refine ⟨3318875407441243706066489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2212583604960829137377659 3318875407441243706066489)
      ·
        refine ⟨2489156555580932779549867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3318875407441243706066489 2489156555580932779549867)
        ·
          refine ⟨3733734833371399169324801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2489156555580932779549867 3733734833371399169324801)
          ·
            refine ⟨2800301125028549376993601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3733734833371399169324801 2800301125028549376993601)
            ·
              refine ⟨2100225843771412032745201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2800301125028549376993601 2100225843771412032745201)
              ·
                refine ⟨1575169382828559024558901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2100225843771412032745201 1575169382828559024558901)
                ·
                  refine ⟨147672129640177408552397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1575169382828559024558901 147672129640177408552397)
                  ·
                    rfl

theorem cell22_1294157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_1294157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294157 prefixEnd_1294157 := by exact prefixLift 1294157
  have htrace : WordTrace (prefixWord ++ tailWord_1294157) baseStart_1294157 baseEnd_1294157 := by
    simpa [prefixWord, tailWord_1294157, baseEnd_1294157] using wordTrace_append hprefix tailTrace_1294157
  have hstable : (prefixWord ++ tailWord_1294157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294157).length < 2 ^ (prefixWord ++ tailWord_1294157).sum := by decide
  have hdescent : baseEnd_1294157 < baseStart_1294157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294234 : List Nat := [3, 1, 1, 4, 2, 2, 3, 1, 2, 3]
def baseStart_1294234 : Nat := 118140960795 + 1294234 * 2 ^ 59
def prefixEnd_1294234 : Nat := 4983230072969 + 3 ^ 40 * 1294234 * 2
def baseEnd_1294234 : Nat := 443042747594129691481955

theorem tailTrace_1294234 : CollatzResearch.WordTrace tailWord_1294234 prefixEnd_1294234 443042747594129691481955 := by
  unfold tailWord_1294234
  simp only [CollatzResearch.WordTrace]
  refine ⟨11801147998304682603652439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31469727995479153609739837 11801147998304682603652439)
  ·
    refine ⟨17701721997457023905478659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11801147998304682603652439 17701721997457023905478659)
    ·
      refine ⟨26552582996185535858217989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17701721997457023905478659 26552582996185535858217989)
      ·
        refine ⟨4978609311784787973415873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26552582996185535858217989 4978609311784787973415873)
        ·
          refine ⟨3733956983838590980061905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4978609311784787973415873 3733956983838590980061905)
          ·
            refine ⟨2800467737878943235046429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3733956983838590980061905 2800467737878943235046429)
            ·
              refine ⟨1050175401704603713142411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2800467737878943235046429 1050175401704603713142411)
              ·
                refine ⟨1575263102556905569713617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1050175401704603713142411 1575263102556905569713617)
                ·
                  refine ⟨1181447326917679177285213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1575263102556905569713617 1181447326917679177285213)
                  ·
                    refine ⟨443042747594129691481955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1181447326917679177285213 443042747594129691481955)
                    ·
                      rfl

theorem cell22_1294234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 2, 3].length) (baseStart_1294234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294234 prefixEnd_1294234 := by exact prefixLift 1294234
  have htrace : WordTrace (prefixWord ++ tailWord_1294234) baseStart_1294234 baseEnd_1294234 := by
    simpa [prefixWord, tailWord_1294234, baseEnd_1294234] using wordTrace_append hprefix tailTrace_1294234
  have hstable : (prefixWord ++ tailWord_1294234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294234).length < 2 ^ (prefixWord ++ tailWord_1294234).sum := by decide
  have hdescent : baseEnd_1294234 < baseStart_1294234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294247 : List Nat := [1, 1, 6, 1, 2, 3, 2, 6]
def baseStart_1294247 : Nat := 118140960795 + 1294247 * 2 ^ 59
def prefixEnd_1294247 : Nat := 4983230072969 + 3 ^ 40 * 1294247 * 2
def baseEnd_1294247 : Nat := 49227466417755776767435

theorem tailTrace_1294247 : CollatzResearch.WordTrace tailWord_1294247 prefixEnd_1294247 49227466417755776767435 := by
  unfold tailWord_1294247
  simp only [CollatzResearch.WordTrace]
  refine ⟨47205066142171633634832995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31470044094781089089888663 47205066142171633634832995)
  ·
    refine ⟨70807599213257450452249493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47205066142171633634832995 70807599213257450452249493)
    ·
      refine ⟨3319106213121442989949195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 70807599213257450452249493 3319106213121442989949195)
      ·
        refine ⟨4978659319682164484923793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3319106213121442989949195 4978659319682164484923793)
        ·
          refine ⟨3733994489761623363692845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4978659319682164484923793 3733994489761623363692845)
          ·
            refine ⟨1400247933660608761384817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3733994489761623363692845 1400247933660608761384817)
            ·
              refine ⟨1050185950245456571038613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1400247933660608761384817 1050185950245456571038613)
              ·
                refine ⟨49227466417755776767435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1050185950245456571038613 49227466417755776767435)
                ·
                  rfl

theorem cell22_1294247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 6].length) (baseStart_1294247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294247 prefixEnd_1294247 := by exact prefixLift 1294247
  have htrace : WordTrace (prefixWord ++ tailWord_1294247) baseStart_1294247 baseEnd_1294247 := by
    simpa [prefixWord, tailWord_1294247, baseEnd_1294247] using wordTrace_append hprefix tailTrace_1294247
  have hstable : (prefixWord ++ tailWord_1294247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294247).length < 2 ^ (prefixWord ++ tailWord_1294247).sum := by decide
  have hdescent : baseEnd_1294247 < baseStart_1294247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294335 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 4, 3]
def baseStart_1294335 : Nat := 118140960795 + 1294335 * 2 ^ 59
def prefixEnd_1294335 : Nat := 4983230072969 + 3 ^ 40 * 1294335 * 2
def baseEnd_1294335 : Nat := 443077321958199094706645

theorem tailTrace_1294335 : CollatzResearch.WordTrace tailWord_1294335 prefixEnd_1294335 443077321958199094706645 := by
  unfold tailWord_1294335
  simp only [CollatzResearch.WordTrace]
  refine ⟨47208275765852824664036459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31472183843901883109357639 47208275765852824664036459)
  ·
    refine ⟨70812413648779236996054689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47208275765852824664036459 70812413648779236996054689)
    ·
      refine ⟨53109310236584427747041017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70812413648779236996054689 53109310236584427747041017)
      ·
        refine ⟨39831982677438320810280763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53109310236584427747041017 39831982677438320810280763)
        ·
          refine ⟨59747974016157481215421145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39831982677438320810280763 59747974016157481215421145)
          ·
            refine ⟨44810980512118110911565859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59747974016157481215421145 44810980512118110911565859)
            ·
              refine ⟨67216470768177166367348789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44810980512118110911565859 67216470768177166367348789)
              ·
                refine ⟨6301544134516609346938949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67216470768177166367348789 6301544134516609346938949)
                ·
                  refine ⟨1181539525221864252551053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6301544134516609346938949 1181539525221864252551053)
                  ·
                    refine ⟨443077321958199094706645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1181539525221864252551053 443077321958199094706645)
                    ·
                      rfl

theorem cell22_1294335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 3].length) (baseStart_1294335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294335 prefixEnd_1294335 := by exact prefixLift 1294335
  have htrace : WordTrace (prefixWord ++ tailWord_1294335) baseStart_1294335 baseEnd_1294335 := by
    simpa [prefixWord, tailWord_1294335, baseEnd_1294335] using wordTrace_append hprefix tailTrace_1294335
  have hstable : (prefixWord ++ tailWord_1294335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294335).length < 2 ^ (prefixWord ++ tailWord_1294335).sum := by decide
  have hdescent : baseEnd_1294335 < baseStart_1294335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294337 : List Nat := [1, 2, 4, 1, 2, 1, 3, 4, 4]
def baseStart_1294337 : Nat := 118140960795 + 1294337 * 2 ^ 59
def prefixEnd_1294337 : Nat := 4983230072969 + 3 ^ 40 * 1294337 * 2
def baseEnd_1294337 : Nat := 147692668866357252052213

theorem tailTrace_1294337 : CollatzResearch.WordTrace tailWord_1294337 prefixEnd_1294337 147692668866357252052213 := by
  unfold tailWord_1294337
  simp only [CollatzResearch.WordTrace]
  refine ⟨47208348711845579005609265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31472232474563719337072843 47208348711845579005609265)
  ·
    refine ⟨35406261533884184254206949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47208348711845579005609265 35406261533884184254206949)
    ·
      refine ⟨6638674037603284547663803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35406261533884184254206949 6638674037603284547663803)
      ·
        refine ⟨9958011056404926821495705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6638674037603284547663803 9958011056404926821495705)
        ·
          refine ⟨7468508292303695116121779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9958011056404926821495705 7468508292303695116121779)
          ·
            refine ⟨11202762438455542674182669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7468508292303695116121779 11202762438455542674182669)
            ·
              refine ⟨4201035914420828502818501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11202762438455542674182669 4201035914420828502818501)
              ·
                refine ⟨787694233953905344278469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4201035914420828502818501 787694233953905344278469)
                ·
                  refine ⟨147692668866357252052213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 787694233953905344278469 147692668866357252052213)
                  ·
                    rfl

theorem cell22_1294337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 4].length) (baseStart_1294337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294337 prefixEnd_1294337 := by exact prefixLift 1294337
  have htrace : WordTrace (prefixWord ++ tailWord_1294337) baseStart_1294337 baseEnd_1294337 := by
    simpa [prefixWord, tailWord_1294337, baseEnd_1294337] using wordTrace_append hprefix tailTrace_1294337
  have hstable : (prefixWord ++ tailWord_1294337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294337).length < 2 ^ (prefixWord ++ tailWord_1294337).sum := by decide
  have hdescent : baseEnd_1294337 < baseStart_1294337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294350 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 1, 6]
def baseStart_1294350 : Nat := 118140960795 + 1294350 * 2 ^ 59
def prefixEnd_1294350 : Nat := 4983230072969 + 3 ^ 40 * 1294350 * 2
def baseEnd_1294350 : Nat := 443082456764744055581599

theorem tailTrace_1294350 : CollatzResearch.WordTrace tailWord_1294350 prefixEnd_1294350 443082456764744055581599 := by
  unfold tailWord_1294350
  simp only [CollatzResearch.WordTrace]
  refine ⟨5901102857599810278229063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31472548573865654817221669 5901102857599810278229063)
  ·
    refine ⟨8851654286399715417343595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5901102857599810278229063 8851654286399715417343595)
    ·
      refine ⟨13277481429599573126015393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8851654286399715417343595 13277481429599573126015393)
      ·
        refine ⟨9958111072199679844511545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13277481429599573126015393 9958111072199679844511545)
        ·
          refine ⟨7468583304149759883383659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9958111072199679844511545 7468583304149759883383659)
          ·
            refine ⟨11202874956224639825075489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7468583304149759883383659 11202874956224639825075489)
            ·
              refine ⟨8402156217168479868806617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11202874956224639825075489 8402156217168479868806617)
              ·
                refine ⟨6301617162876359901604963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8402156217168479868806617 6301617162876359901604963)
                ·
                  refine ⟨9452425744314539852407445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6301617162876359901604963 9452425744314539852407445)
                  ·
                    refine ⟨443082456764744055581599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9452425744314539852407445 443082456764744055581599)
                    ·
                      rfl

theorem cell22_1294350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_1294350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294350 prefixEnd_1294350 := by exact prefixLift 1294350
  have htrace : WordTrace (prefixWord ++ tailWord_1294350) baseStart_1294350 baseEnd_1294350 := by
    simpa [prefixWord, tailWord_1294350, baseEnd_1294350] using wordTrace_append hprefix tailTrace_1294350
  have hstable : (prefixWord ++ tailWord_1294350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294350).length < 2 ^ (prefixWord ++ tailWord_1294350).sum := by decide
  have hdescent : baseEnd_1294350 < baseStart_1294350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294363 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 1, 9]
def baseStart_1294363 : Nat := 118140960795 + 1294363 * 2 ^ 59
def prefixEnd_1294363 : Nat := 4983230072969 + 3 ^ 40 * 1294363 * 2
def baseEnd_1294363 : Nat := 443086906930416355006559

theorem tailTrace_1294363 : CollatzResearch.WordTrace tailWord_1294363 prefixEnd_1294363 443086906930416355006559 := by
  unfold tailWord_1294363
  simp only [CollatzResearch.WordTrace]
  refine ⟨47209297009751385446055743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31472864673167590297370495 47209297009751385446055743)
  ·
    refine ⟨70813945514627078169083615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47209297009751385446055743 70813945514627078169083615)
    ·
      refine ⟨106220918271940617253625423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70813945514627078169083615 106220918271940617253625423)
      ·
        refine ⟨159331377407910925880438135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106220918271940617253625423 159331377407910925880438135)
        ·
          refine ⟨238997066111866388820657203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159331377407910925880438135 238997066111866388820657203)
          ·
            refine ⟨358495599167799583230985805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238997066111866388820657203 358495599167799583230985805)
            ·
              refine ⟨134435849687924843711619677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 358495599167799583230985805 134435849687924843711619677)
              ·
                refine ⟨50413443632971816391857379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134435849687924843711619677 50413443632971816391857379)
                ·
                  refine ⟨75620165449457724587786069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50413443632971816391857379 75620165449457724587786069)
                  ·
                    refine ⟨443086906930416355006559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 75620165449457724587786069 443086906930416355006559)
                    ·
                      rfl

theorem cell22_1294363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 9].length) (baseStart_1294363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294363 prefixEnd_1294363 := by exact prefixLift 1294363
  have htrace : WordTrace (prefixWord ++ tailWord_1294363) baseStart_1294363 baseEnd_1294363 := by
    simpa [prefixWord, tailWord_1294363, baseEnd_1294363] using wordTrace_append hprefix tailTrace_1294363
  have hstable : (prefixWord ++ tailWord_1294363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294363).length < 2 ^ (prefixWord ++ tailWord_1294363).sum := by decide
  have hdescent : baseEnd_1294363 < baseStart_1294363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294474 : List Nat := [3, 1, 2, 3, 1, 2, 3, 2, 1, 4]
def baseStart_1294474 : Nat := 118140960795 + 1294474 * 2 ^ 59
def prefixEnd_1294474 : Nat := 4983230072969 + 3 ^ 40 * 1294474 * 2
def baseEnd_1294474 : Nat := 443124904498849065481219

theorem tailTrace_1294474 : CollatzResearch.WordTrace tailWord_1294474 prefixEnd_1294474 443124904498849065481219 := by
  unfold tailWord_1294474
  simp only [CollatzResearch.WordTrace]
  refine ⟨11803336378087312850836619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31475563674899500935564317 11803336378087312850836619)
  ·
    refine ⟨17705004567130969276254929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11803336378087312850836619 17705004567130969276254929)
    ·
      refine ⟨13278753425348226957191197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17705004567130969276254929 13278753425348226957191197)
      ·
        refine ⟨4979532534505585108946699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13278753425348226957191197 4979532534505585108946699)
        ·
          refine ⟨7469298801758377663420049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4979532534505585108946699 7469298801758377663420049)
          ·
            refine ⟨5601974101318783247565037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7469298801758377663420049 5601974101318783247565037)
            ·
              refine ⟨2100740287994543717836889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5601974101318783247565037 2100740287994543717836889)
              ·
                refine ⟨1575555215995907788377667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2100740287994543717836889 1575555215995907788377667)
                ·
                  refine ⟨2363332823993861682566501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1575555215995907788377667 2363332823993861682566501)
                  ·
                    refine ⟨443124904498849065481219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2363332823993861682566501 443124904498849065481219)
                    ·
                      rfl

theorem cell22_1294474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_1294474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294474 prefixEnd_1294474 := by exact prefixLift 1294474
  have htrace : WordTrace (prefixWord ++ tailWord_1294474) baseStart_1294474 baseEnd_1294474 := by
    simpa [prefixWord, tailWord_1294474, baseEnd_1294474] using wordTrace_append hprefix tailTrace_1294474
  have hstable : (prefixWord ++ tailWord_1294474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294474).length < 2 ^ (prefixWord ++ tailWord_1294474).sum := by decide
  have hdescent : baseEnd_1294474 < baseStart_1294474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294500 : List Nat := [2, 3, 1, 2, 14]
def baseStart_1294500 : Nat := 118140960795 + 1294500 * 2 ^ 59
def prefixEnd_1294500 : Nat := 4983230072969 + 3 ^ 40 * 1294500 * 2
def baseEnd_1294500 : Nat := 1823595904651002733873

theorem tailTrace_1294500 : CollatzResearch.WordTrace tailWord_1294500 prefixEnd_1294500 1823595904651002733873 := by
  unfold tailWord_1294500
  simp only [CollatzResearch.WordTrace]
  refine ⟨23607146905127528921896477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31476195873503371895861969 23607146905127528921896477)
  ·
    refine ⟨8852680089422823345711179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23607146905127528921896477 8852680089422823345711179)
    ·
      refine ⟨13279020134134235018566769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8852680089422823345711179 13279020134134235018566769)
      ·
        refine ⟨9959265100600676263925077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13279020134134235018566769 9959265100600676263925077)
        ·
          refine ⟨1823595904651002733873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 9959265100600676263925077 1823595904651002733873)
          ·
            rfl

theorem cell22_1294500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 14].length) (baseStart_1294500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294500 prefixEnd_1294500 := by exact prefixLift 1294500
  have htrace : WordTrace (prefixWord ++ tailWord_1294500) baseStart_1294500 baseEnd_1294500 := by
    simpa [prefixWord, tailWord_1294500, baseEnd_1294500] using wordTrace_append hprefix tailTrace_1294500
  have hstable : (prefixWord ++ tailWord_1294500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294500).length < 2 ^ (prefixWord ++ tailWord_1294500).sum := by decide
  have hdescent : baseEnd_1294500 < baseStart_1294500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294515 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 2, 7]
def baseStart_1294515 : Nat := 118140960795 + 1294515 * 2 ^ 59
def prefixEnd_1294515 : Nat := 4983230072969 + 3 ^ 40 * 1294515 * 2
def baseEnd_1294515 : Nat := 443138939636738625206093

theorem tailTrace_1294515 : CollatzResearch.WordTrace tailWord_1294515 prefixEnd_1294515 443138939636738625206093 := by
  unfold tailWord_1294515
  simp only [CollatzResearch.WordTrace]
  refine ⟨47214840905200715405588999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31476560603467143603725999 47214840905200715405588999)
  ·
    refine ⟨70822261357801073108383499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47214840905200715405588999 70822261357801073108383499)
    ·
      refine ⟨106233392036701609662575249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70822261357801073108383499 106233392036701609662575249)
      ·
        refine ⟨79675044027526207246931437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106233392036701609662575249 79675044027526207246931437)
        ·
          refine ⟨29878141510322327717599289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79675044027526207246931437 29878141510322327717599289)
          ·
            refine ⟨22408606132741745788199467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29878141510322327717599289 22408606132741745788199467)
            ·
              refine ⟨33612909199112618682299201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22408606132741745788199467 33612909199112618682299201)
              ·
                refine ⟨25209681899334464011724401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33612909199112618682299201 25209681899334464011724401)
                ·
                  refine ⟨18907261424500848008793301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25209681899334464011724401 18907261424500848008793301)
                  ·
                    refine ⟨443138939636738625206093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18907261424500848008793301 443138939636738625206093)
                    ·
                      rfl

theorem cell22_1294515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 7].length) (baseStart_1294515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294515 prefixEnd_1294515 := by exact prefixLift 1294515
  have htrace : WordTrace (prefixWord ++ tailWord_1294515) baseStart_1294515 baseEnd_1294515 := by
    simpa [prefixWord, tailWord_1294515, baseEnd_1294515] using wordTrace_append hprefix tailTrace_1294515
  have hstable : (prefixWord ++ tailWord_1294515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294515).length < 2 ^ (prefixWord ++ tailWord_1294515).sum := by decide
  have hdescent : baseEnd_1294515 < baseStart_1294515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294577 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 2, 5]
def baseStart_1294577 : Nat := 118140960795 + 1294577 * 2 ^ 59
def prefixEnd_1294577 : Nat := 4983230072969 + 3 ^ 40 * 1294577 * 2
def baseEnd_1294577 : Nat := 443160163503791130155903

theorem tailTrace_1294577 : CollatzResearch.WordTrace tailWord_1294577 prefixEnd_1294577 443160163503791130155903 := by
  unfold tailWord_1294577
  simp only [CollatzResearch.WordTrace]
  refine ⟨47217102230976099994345985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31478068153984066662897323 47217102230976099994345985)
  ·
    refine ⟨35412826673232074995759489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47217102230976099994345985 35412826673232074995759489)
    ·
      refine ⟨26559620004924056246819617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35412826673232074995759489 26559620004924056246819617)
      ·
        refine ⟨19919715003693042185114713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26559620004924056246819617 19919715003693042185114713)
        ·
          refine ⟨14939786252769781638836035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19919715003693042185114713 14939786252769781638836035)
          ·
            refine ⟨22409679379154672458254053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14939786252769781638836035 22409679379154672458254053)
            ·
              refine ⟨4201814883591501085922635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22409679379154672458254053 4201814883591501085922635)
              ·
                refine ⟨6302722325387251628883953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4201814883591501085922635 6302722325387251628883953)
                ·
                  refine ⟨4727041744040438721662965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6302722325387251628883953 4727041744040438721662965)
                  ·
                    refine ⟨443160163503791130155903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4727041744040438721662965 443160163503791130155903)
                    ·
                      rfl

theorem cell22_1294577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_1294577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294577 prefixEnd_1294577 := by exact prefixLift 1294577
  have htrace : WordTrace (prefixWord ++ tailWord_1294577) baseStart_1294577 baseEnd_1294577 := by
    simpa [prefixWord, tailWord_1294577, baseEnd_1294577] using wordTrace_append hprefix tailTrace_1294577
  have hstable : (prefixWord ++ tailWord_1294577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294577).length < 2 ^ (prefixWord ++ tailWord_1294577).sum := by decide
  have hdescent : baseEnd_1294577 < baseStart_1294577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294579 : List Nat := [1, 1, 1, 2, 2, 4, 5, 1, 5]
def baseStart_1294579 : Nat := 118140960795 + 1294579 * 2 ^ 59
def prefixEnd_1294579 : Nat := 4983230072969 + 3 ^ 40 * 1294579 * 2
def baseEnd_1294579 : Nat := 147720282714887930535299

theorem tailTrace_1294579 : CollatzResearch.WordTrace tailWord_1294579 prefixEnd_1294579 147720282714887930535299 := by
  unfold tailWord_1294579
  simp only [CollatzResearch.WordTrace]
  refine ⟨47217175176968854335918791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31478116784645902890612527 47217175176968854335918791)
  ·
    refine ⟨70825762765453281503878187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47217175176968854335918791 70825762765453281503878187)
    ·
      refine ⟨106238644148179922255817281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70825762765453281503878187 106238644148179922255817281)
      ·
        refine ⟨79678983111134941691862961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106238644148179922255817281 79678983111134941691862961)
        ·
          refine ⟨59759237333351206268897221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79678983111134941691862961 59759237333351206268897221)
          ·
            refine ⟨11204857000003351175418229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59759237333351206268897221 11204857000003351175418229)
            ·
              refine ⟨1050455343750314172695459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11204857000003351175418229 1050455343750314172695459)
              ·
                refine ⟨1575683015625471259043189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1050455343750314172695459 1575683015625471259043189)
                ·
                  refine ⟨147720282714887930535299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1575683015625471259043189 147720282714887930535299)
                  ·
                    rfl

theorem cell22_1294579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 5].length) (baseStart_1294579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294579 prefixEnd_1294579 := by exact prefixLift 1294579
  have htrace : WordTrace (prefixWord ++ tailWord_1294579) baseStart_1294579 baseEnd_1294579 := by
    simpa [prefixWord, tailWord_1294579, baseEnd_1294579] using wordTrace_append hprefix tailTrace_1294579
  have hstable : (prefixWord ++ tailWord_1294579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294579).length < 2 ^ (prefixWord ++ tailWord_1294579).sum := by decide
  have hdescent : baseEnd_1294579 < baseStart_1294579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294592 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 3, 4]
def baseStart_1294592 : Nat := 118140960795 + 1294592 * 2 ^ 59
def prefixEnd_1294592 : Nat := 4983230072969 + 3 ^ 40 * 1294592 * 2
def baseEnd_1294592 : Nat := 443165298310336091030857

theorem tailTrace_1294592 : CollatzResearch.WordTrace tailWord_1294592 prefixEnd_1294592 443165298310336091030857 := by
  unfold tailWord_1294592
  simp only [CollatzResearch.WordTrace]
  refine ⟨23608824662960878778071015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31478432883947838370761353 23608824662960878778071015)
  ·
    refine ⟨35413236994441318167106523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23608824662960878778071015 35413236994441318167106523)
    ·
      refine ⟨53119855491661977250659785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35413236994441318167106523 53119855491661977250659785)
      ·
        refine ⟨39839891618746482937994839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53119855491661977250659785 39839891618746482937994839)
        ·
          refine ⟨59759837428119724406992259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39839891618746482937994839 59759837428119724406992259)
          ·
            refine ⟨89639756142179586610488389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59759837428119724406992259 89639756142179586610488389)
            ·
              refine ⟨16807454276658672489466573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89639756142179586610488389 16807454276658672489466573)
              ·
                refine ⟨6302795353747002183549965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16807454276658672489466573 6302795353747002183549965)
                ·
                  refine ⟨2363548257655125818831237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6302795353747002183549965 2363548257655125818831237)
                  ·
                    refine ⟨443165298310336091030857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2363548257655125818831237 443165298310336091030857)
                    ·
                      rfl

theorem cell22_1294592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 3, 4].length) (baseStart_1294592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294592 prefixEnd_1294592 := by exact prefixLift 1294592
  have htrace : WordTrace (prefixWord ++ tailWord_1294592) baseStart_1294592 baseEnd_1294592 := by
    simpa [prefixWord, tailWord_1294592, baseEnd_1294592] using wordTrace_append hprefix tailTrace_1294592
  have hstable : (prefixWord ++ tailWord_1294592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294592).length < 2 ^ (prefixWord ++ tailWord_1294592).sum := by decide
  have hdescent : baseEnd_1294592 < baseStart_1294592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294609 : List Nat := [1, 2, 2, 1, 1, 5, 2, 3, 1, 4]
def baseStart_1294609 : Nat := 118140960795 + 1294609 * 2 ^ 59
def prefixEnd_1294609 : Nat := 4983230072969 + 3 ^ 40 * 1294609 * 2
def baseEnd_1294609 : Nat := 443171117757753713355805

theorem tailTrace_1294609 : CollatzResearch.WordTrace tailWord_1294609 prefixEnd_1294609 443171117757753713355805 := by
  unfold tailWord_1294609
  simp only [CollatzResearch.WordTrace]
  refine ⟨47218269366860169459510881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31478846244573446306340587 47218269366860169459510881)
  ·
    refine ⟨35413702025145127094633161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47218269366860169459510881 35413702025145127094633161)
    ·
      refine ⟨26560276518858845320974871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35413702025145127094633161 26560276518858845320974871)
      ·
        refine ⟨39840414778288267981462307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26560276518858845320974871 39840414778288267981462307)
        ·
          refine ⟨59760622167432401972193461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39840414778288267981462307 59760622167432401972193461)
          ·
            refine ⟨5602558328196787684893137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59760622167432401972193461 5602558328196787684893137)
            ·
              refine ⟨4201918746147590763669853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5602558328196787684893137 4201918746147590763669853)
              ·
                refine ⟨1575719529805346536376195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4201918746147590763669853 1575719529805346536376195)
                ·
                  refine ⟨2363579294708019804564293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1575719529805346536376195 2363579294708019804564293)
                  ·
                    refine ⟨443171117757753713355805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2363579294708019804564293 443171117757753713355805)
                    ·
                      rfl

theorem cell22_1294609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_1294609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294609 prefixEnd_1294609 := by exact prefixLift 1294609
  have htrace : WordTrace (prefixWord ++ tailWord_1294609) baseStart_1294609 baseEnd_1294609 := by
    simpa [prefixWord, tailWord_1294609, baseEnd_1294609] using wordTrace_append hprefix tailTrace_1294609
  have hstable : (prefixWord ++ tailWord_1294609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294609).length < 2 ^ (prefixWord ++ tailWord_1294609).sum := by decide
  have hdescent : baseEnd_1294609 < baseStart_1294609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294624 : List Nat := [2, 1, 1, 5, 2, 1, 3, 1, 6]
def baseStart_1294624 : Nat := 118140960795 + 1294624 * 2 ^ 59
def prefixEnd_1294624 : Nat := 4983230072969 + 3 ^ 40 * 1294624 * 2
def baseEnd_1294624 : Nat := 147725417521432891410253

theorem tailTrace_1294624 : CollatzResearch.WordTrace tailWord_1294624 prefixEnd_1294624 147725417521432891410253 := by
  unfold tailWord_1294624
  simp only [CollatzResearch.WordTrace]
  refine ⟨23609408230902913510653463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31479210974537218014204617 23609408230902913510653463)
  ·
    refine ⟨35414112346354370265980195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23609408230902913510653463 35414112346354370265980195)
    ·
      refine ⟨53121168519531555398970293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35414112346354370265980195 53121168519531555398970293)
      ·
        refine ⟨4980109548706083318653465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53121168519531555398970293 4980109548706083318653465)
        ·
          refine ⟨3735082161529562488990099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4980109548706083318653465 3735082161529562488990099)
          ·
            refine ⟨5602623242294343733485149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3735082161529562488990099 5602623242294343733485149)
            ·
              refine ⟨2100983715860378900056931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5602623242294343733485149 2100983715860378900056931)
              ·
                refine ⟨3151475573790568350085397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2100983715860378900056931 3151475573790568350085397)
                ·
                  refine ⟨147725417521432891410253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3151475573790568350085397 147725417521432891410253)
                  ·
                    rfl

theorem cell22_1294624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 6].length) (baseStart_1294624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294624 prefixEnd_1294624 := by exact prefixLift 1294624
  have htrace : WordTrace (prefixWord ++ tailWord_1294624) baseStart_1294624 baseEnd_1294624 := by
    simpa [prefixWord, tailWord_1294624, baseEnd_1294624] using wordTrace_append hprefix tailTrace_1294624
  have hstable : (prefixWord ++ tailWord_1294624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294624).length < 2 ^ (prefixWord ++ tailWord_1294624).sum := by decide
  have hdescent : baseEnd_1294624 < baseStart_1294624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294652 : List Nat := [2, 2, 2, 2, 1, 2, 1, 10]
def baseStart_1294652 : Nat := 118140960795 + 1294652 * 2 ^ 59
def prefixEnd_1294652 : Nat := 4983230072969 + 3 ^ 40 * 1294652 * 2
def baseEnd_1294652 : Nat := 49242870837390659392297

theorem tailTrace_1294652 : CollatzResearch.WordTrace tailWord_1294652 prefixEnd_1294652 49242870837390659392297 := by
  unfold tailWord_1294652
  simp only [CollatzResearch.WordTrace]
  refine ⟨23609918852852193901663105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31479891803802925202217473 23609918852852193901663105)
  ·
    refine ⟨17707439139639145426247329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23609918852852193901663105 17707439139639145426247329)
    ·
      refine ⟨13280579354729359069685497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17707439139639145426247329 13280579354729359069685497)
      ·
        refine ⟨9960434516047019302264123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13280579354729359069685497 9960434516047019302264123)
        ·
          refine ⟨14940651774070528953396185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9960434516047019302264123 14940651774070528953396185)
          ·
            refine ⟨11205488830552896715047139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14940651774070528953396185 11205488830552896715047139)
            ·
              refine ⟨16808233245829345072570709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11205488830552896715047139 16808233245829345072570709)
              ·
                refine ⟨49242870837390659392297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 16808233245829345072570709 49242870837390659392297)
                ·
                  rfl

theorem cell22_1294652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 10].length) (baseStart_1294652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294652 prefixEnd_1294652 := by exact prefixLift 1294652
  have htrace : WordTrace (prefixWord ++ tailWord_1294652) baseStart_1294652 baseEnd_1294652 := by
    simpa [prefixWord, tailWord_1294652, baseEnd_1294652] using wordTrace_append hprefix tailTrace_1294652
  have hstable : (prefixWord ++ tailWord_1294652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294652).length < 2 ^ (prefixWord ++ tailWord_1294652).sum := by decide
  have hdescent : baseEnd_1294652 < baseStart_1294652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294660 : List Nat := [2, 3, 4, 1, 2, 1, 3, 1, 1, 4]
def baseStart_1294660 : Nat := 118140960795 + 1294660 * 2 ^ 59
def prefixEnd_1294660 : Nat := 4983230072969 + 3 ^ 40 * 1294660 * 2
def baseEnd_1294660 : Nat := 443188576100006580330649

theorem tailTrace_1294660 : CollatzResearch.WordTrace tailWord_1294660 prefixEnd_1294660 443188576100006580330649 := by
  unfold tailWord_1294660
  simp only [CollatzResearch.WordTrace]
  refine ⟨23610064744837702584808717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31480086326450270113078289 23610064744837702584808717)
  ·
    refine ⟨8853774279314138469303269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23610064744837702584808717 8853774279314138469303269)
    ·
      refine ⟨1660082677371400962994363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8853774279314138469303269 1660082677371400962994363)
      ·
        refine ⟨2490124016057101444491545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1660082677371400962994363 2490124016057101444491545)
        ·
          refine ⟨1867593012042826083368659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2490124016057101444491545 1867593012042826083368659)
          ·
            refine ⟨2801389518064239125052989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1867593012042826083368659 2801389518064239125052989)
            ·
              refine ⟨1050521069274089671894871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2801389518064239125052989 1050521069274089671894871)
              ·
                refine ⟨1575781603911134507842307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1050521069274089671894871 1575781603911134507842307)
                ·
                  refine ⟨2363672405866701761763461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1575781603911134507842307 2363672405866701761763461)
                  ·
                    refine ⟨443188576100006580330649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2363672405866701761763461 443188576100006580330649)
                    ·
                      rfl

theorem cell22_1294660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_1294660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294660 prefixEnd_1294660 := by exact prefixLift 1294660
  have htrace : WordTrace (prefixWord ++ tailWord_1294660) baseStart_1294660 baseEnd_1294660 := by
    simpa [prefixWord, tailWord_1294660, baseEnd_1294660] using wordTrace_append hprefix tailTrace_1294660
  have hstable : (prefixWord ++ tailWord_1294660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294660).length < 2 ^ (prefixWord ++ tailWord_1294660).sum := by decide
  have hdescent : baseEnd_1294660 < baseStart_1294660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294701 : List Nat := [1, 5, 1, 1, 1, 2, 3, 2, 3, 3]
def baseStart_1294701 : Nat := 118140960795 + 1294701 * 2 ^ 59
def prefixEnd_1294701 : Nat := 4983230072969 + 3 ^ 40 * 1294701 * 2
def baseEnd_1294701 : Nat := 443202611237896140055523

theorem tailTrace_1294701 : CollatzResearch.WordTrace tailWord_1294701 prefixEnd_1294701 443202611237896140055523 := by
  unfold tailWord_1294701
  simp only [CollatzResearch.WordTrace]
  refine ⟨47221624882526869171859957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31481083255017912781239971 47221624882526869171859957)
  ·
    refine ⟨4427027332736893984861871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47221624882526869171859957 4427027332736893984861871)
    ·
      refine ⟨6640540999105340977292807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4427027332736893984861871 6640540999105340977292807)
      ·
        refine ⟨9960811498658011465939211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6640540999105340977292807 9960811498658011465939211)
        ·
          refine ⟨14941217247987017198908817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9960811498658011465939211 14941217247987017198908817)
          ·
            refine ⟨11205912935990262899181613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14941217247987017198908817 11205912935990262899181613)
            ·
              refine ⟨4202217350996348587193105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11205912935990262899181613 4202217350996348587193105)
              ·
                refine ⟨3151663013247261440394829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4202217350996348587193105 3151663013247261440394829)
                ·
                  refine ⟨1181873629967723040148061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3151663013247261440394829 1181873629967723040148061)
                  ·
                    refine ⟨443202611237896140055523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1181873629967723040148061 443202611237896140055523)
                    ·
                      rfl

theorem cell22_1294701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_1294701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294701 prefixEnd_1294701 := by exact prefixLift 1294701
  have htrace : WordTrace (prefixWord ++ tailWord_1294701) baseStart_1294701 baseEnd_1294701 := by
    simpa [prefixWord, tailWord_1294701, baseEnd_1294701] using wordTrace_append hprefix tailTrace_1294701
  have hstable : (prefixWord ++ tailWord_1294701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294701).length < 2 ^ (prefixWord ++ tailWord_1294701).sum := by decide
  have hdescent : baseEnd_1294701 < baseStart_1294701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294729 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 2, 5]
def baseStart_1294729 : Nat := 118140960795 + 1294729 * 2 ^ 59
def prefixEnd_1294729 : Nat := 4983230072969 + 3 ^ 40 * 1294729 * 2
def baseEnd_1294729 : Nat := 443212196210113400355437

theorem tailTrace_1294729 : CollatzResearch.WordTrace tailWord_1294729 prefixEnd_1294729 443212196210113400355437 := by
  unfold tailWord_1294729
  simp only [CollatzResearch.WordTrace]
  refine ⟨47222646126425429953879241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31481764084283619969252827 47222646126425429953879241)
  ·
    refine ⟨35416984594819072465409431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47222646126425429953879241 35416984594819072465409431)
    ·
      refine ⟨53125476892228608698114147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35416984594819072465409431 53125476892228608698114147)
      ·
        refine ⟨79688215338342913047171221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53125476892228608698114147 79688215338342913047171221)
        ·
          refine ⟨3735385093984824049086151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79688215338342913047171221 3735385093984824049086151)
          ·
            refine ⟨5603077640977236073629227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3735385093984824049086151 5603077640977236073629227)
            ·
              refine ⟨8404616461465854110443841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5603077640977236073629227 8404616461465854110443841)
              ·
                refine ⟨6303462346099390582832881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8404616461465854110443841 6303462346099390582832881)
                ·
                  refine ⟨4727596759574542937124661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6303462346099390582832881 4727596759574542937124661)
                  ·
                    refine ⟨443212196210113400355437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4727596759574542937124661 443212196210113400355437)
                    ·
                      rfl

theorem cell22_1294729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 5].length) (baseStart_1294729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294729 prefixEnd_1294729 := by exact prefixLift 1294729
  have htrace : WordTrace (prefixWord ++ tailWord_1294729) baseStart_1294729 baseEnd_1294729 := by
    simpa [prefixWord, tailWord_1294729, baseEnd_1294729] using wordTrace_append hprefix tailTrace_1294729
  have hstable : (prefixWord ++ tailWord_1294729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294729).length < 2 ^ (prefixWord ++ tailWord_1294729).sum := by decide
  have hdescent : baseEnd_1294729 < baseStart_1294729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294731 : List Nat := [1, 1, 1, 1, 4, 6, 1, 2, 5]
def baseStart_1294731 : Nat := 118140960795 + 1294731 * 2 ^ 59
def prefixEnd_1294731 : Nat := 4983230072969 + 3 ^ 40 * 1294731 * 2
def baseEnd_1294731 : Nat := 147737626950328687268477

theorem tailTrace_1294731 : CollatzResearch.WordTrace tailWord_1294731 prefixEnd_1294731 147737626950328687268477 := by
  unfold tailWord_1294731
  simp only [CollatzResearch.WordTrace]
  refine ⟨47222719072418184295452047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31481812714945456196968031 47222719072418184295452047)
  ·
    refine ⟨70834078608627276443178071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47222719072418184295452047 70834078608627276443178071)
    ·
      refine ⟨106251117912940914664767107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70834078608627276443178071 106251117912940914664767107)
      ·
        refine ⟨159376676869411371997150661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106251117912940914664767107 159376676869411371997150661)
        ·
          refine ⟨29883126913014632249465749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159376676869411371997150661 29883126913014632249465749)
          ·
            refine ⟨1400771574047560886693707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29883126913014632249465749 1400771574047560886693707)
            ·
              refine ⟨2101157361071341330040561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1400771574047560886693707 2101157361071341330040561)
              ·
                refine ⟨1575868020803505997530421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2101157361071341330040561 1575868020803505997530421)
                ·
                  refine ⟨147737626950328687268477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1575868020803505997530421 147737626950328687268477)
                  ·
                    rfl

theorem cell22_1294731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 5].length) (baseStart_1294731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294731 prefixEnd_1294731 := by exact prefixLift 1294731
  have htrace : WordTrace (prefixWord ++ tailWord_1294731) baseStart_1294731 baseEnd_1294731 := by
    simpa [prefixWord, tailWord_1294731, baseEnd_1294731] using wordTrace_append hprefix tailTrace_1294731
  have hstable : (prefixWord ++ tailWord_1294731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294731).length < 2 ^ (prefixWord ++ tailWord_1294731).sum := by decide
  have hdescent : baseEnd_1294731 < baseStart_1294731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294791 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 4, 3]
def baseStart_1294791 : Nat := 118140960795 + 1294791 * 2 ^ 59
def prefixEnd_1294791 : Nat := 4983230072969 + 3 ^ 40 * 1294791 * 2
def baseEnd_1294791 : Nat := 443233420077165905305247

theorem tailTrace_1294791 : CollatzResearch.WordTrace tailWord_1294791 prefixEnd_1294791 443233420077165905305247 := by
  unfold tailWord_1294791
  simp only [CollatzResearch.WordTrace]
  refine ⟨47224907452200814542636227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31483271634800543028424151 47224907452200814542636227)
  ·
    refine ⟨70837361178301221813954341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47224907452200814542636227 70837361178301221813954341)
    ·
      refine ⟨13282005220931479090116439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70837361178301221813954341 13282005220931479090116439)
      ·
        refine ⟨19923007831397218635174659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13282005220931479090116439 19923007831397218635174659)
        ·
          refine ⟨29884511747095827952761989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19923007831397218635174659 29884511747095827952761989)
          ·
            refine ⟨5603345952580467741142873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29884511747095827952761989 5603345952580467741142873)
            ·
              refine ⟨4202509464435350805857155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5603345952580467741142873 4202509464435350805857155)
              ·
                refine ⟨6303764196653026208785733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4202509464435350805857155 6303764196653026208785733)
                ·
                  refine ⟨1181955786872442414147325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6303764196653026208785733 1181955786872442414147325)
                  ·
                    refine ⟨443233420077165905305247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1181955786872442414147325 443233420077165905305247)
                    ·
                      rfl

theorem cell22_1294791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_1294791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294791 prefixEnd_1294791 := by exact prefixLift 1294791
  have htrace : WordTrace (prefixWord ++ tailWord_1294791) baseStart_1294791 baseEnd_1294791 := by
    simpa [prefixWord, tailWord_1294791, baseEnd_1294791] using wordTrace_append hprefix tailTrace_1294791
  have hstable : (prefixWord ++ tailWord_1294791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294791).length < 2 ^ (prefixWord ++ tailWord_1294791).sum := by decide
  have hdescent : baseEnd_1294791 < baseStart_1294791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294900 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 7]
def baseStart_1294900 : Nat := 118140960795 + 1294900 * 2 ^ 59
def prefixEnd_1294900 : Nat := 4983230072969 + 3 ^ 40 * 1294900 * 2
def baseEnd_1294900 : Nat := 147756911001575318109971

theorem tailTrace_1294900 : CollatzResearch.WordTrace tailWord_1294900 prefixEnd_1294900 147756911001575318109971 := by
  unfold tailWord_1294900
  simp only [CollatzResearch.WordTrace]
  refine ⟨23614441504402963079177077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31485922005870617438902769 23614441504402963079177077)
  ·
    refine ⟨2213853891037777788672851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23614441504402963079177077 2213853891037777788672851)
    ·
      refine ⟨3320780836556666683009277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2213853891037777788672851 3320780836556666683009277)
      ·
        refine ⟨1245292813708750006128479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3320780836556666683009277 1245292813708750006128479)
        ·
          refine ⟨1867939220563125009192719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1245292813708750006128479 1867939220563125009192719)
          ·
            refine ⟨2801908830844687513789079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1867939220563125009192719 2801908830844687513789079)
            ·
              refine ⟨4202863246267031270683619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2801908830844687513789079 4202863246267031270683619)
              ·
                refine ⟨6304294869400546906025429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4202863246267031270683619 6304294869400546906025429)
                ·
                  refine ⟨147756911001575318109971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6304294869400546906025429 147756911001575318109971)
                  ·
                    rfl

theorem cell22_1294900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_1294900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294900 prefixEnd_1294900 := by exact prefixLift 1294900
  have htrace : WordTrace (prefixWord ++ tailWord_1294900) baseStart_1294900 baseEnd_1294900 := by
    simpa [prefixWord, tailWord_1294900, baseEnd_1294900] using wordTrace_append hprefix tailTrace_1294900
  have hstable : (prefixWord ++ tailWord_1294900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294900).length < 2 ^ (prefixWord ++ tailWord_1294900).sum := by decide
  have hdescent : baseEnd_1294900 < baseStart_1294900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294911 : List Nat := [1, 1, 2, 2, 3, 2, 4, 1, 6]
def baseStart_1294911 : Nat := 118140960795 + 1294911 * 2 ^ 59
def prefixEnd_1294911 : Nat := 4983230072969 + 3 ^ 40 * 1294911 * 2
def baseEnd_1294911 : Nat := 147758166176508530768293

theorem tailTrace_1294911 : CollatzResearch.WordTrace tailWord_1294911 prefixEnd_1294911 147758166176508530768293 := by
  unfold tailWord_1294911
  simp only [CollatzResearch.WordTrace]
  refine ⟨47229284211766075037004587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31486189474510716691336391 47229284211766075037004587)
  ·
    refine ⟨70843926317649112555506881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47229284211766075037004587 70843926317649112555506881)
    ·
      refine ⟨53132944738236834416630161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70843926317649112555506881 53132944738236834416630161)
      ·
        refine ⟨39849708553677625812472621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53132944738236834416630161 39849708553677625812472621)
        ·
          refine ⟨14943640707629109679677233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39849708553677625812472621 14943640707629109679677233)
          ·
            refine ⟨11207730530721832259757925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14943640707629109679677233 11207730530721832259757925)
            ·
              refine ⟨2101449474510343548704611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11207730530721832259757925 2101449474510343548704611)
              ·
                refine ⟨3152174211765515323056917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2101449474510343548704611 3152174211765515323056917)
                ·
                  refine ⟨147758166176508530768293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3152174211765515323056917 147758166176508530768293)
                  ·
                    rfl

theorem cell22_1294911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 6].length) (baseStart_1294911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294911 prefixEnd_1294911 := by exact prefixLift 1294911
  have htrace : WordTrace (prefixWord ++ tailWord_1294911) baseStart_1294911 baseEnd_1294911 := by
    simpa [prefixWord, tailWord_1294911, baseEnd_1294911] using wordTrace_append hprefix tailTrace_1294911
  have hstable : (prefixWord ++ tailWord_1294911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294911).length < 2 ^ (prefixWord ++ tailWord_1294911).sum := by decide
  have hdescent : baseEnd_1294911 < baseStart_1294911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294945 : List Nat := [1, 2, 3, 1, 1, 6, 1, 3, 4]
def baseStart_1294945 : Nat := 118140960795 + 1294945 * 2 ^ 59
def prefixEnd_1294945 : Nat := 4983230072969 + 3 ^ 40 * 1294945 * 2
def baseEnd_1294945 : Nat := 147762045808120278984925

theorem tailTrace_1294945 : CollatzResearch.WordTrace tailWord_1294945 prefixEnd_1294945 147762045808120278984925 := by
  unfold tailWord_1294945
  simp only [CollatzResearch.WordTrace]
  refine ⟨47230524293642898843742289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31487016195761932562494859 47230524293642898843742289)
  ·
    refine ⟨35422893220232174132806717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47230524293642898843742289 35422893220232174132806717)
    ·
      refine ⟨13283584957587065299802519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35422893220232174132806717 13283584957587065299802519)
      ·
        refine ⟨19925377436380597949703779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13283584957587065299802519 19925377436380597949703779)
        ·
          refine ⟨29888066154570896924555669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19925377436380597949703779 29888066154570896924555669)
          ·
            refine ⟨1401003100995510793338547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29888066154570896924555669 1401003100995510793338547)
            ·
              refine ⟨2101504651493266190007821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1401003100995510793338547 2101504651493266190007821)
              ·
                refine ⟨788064244309974821252933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2101504651493266190007821 788064244309974821252933)
                ·
                  refine ⟨147762045808120278984925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 788064244309974821252933 147762045808120278984925)
                  ·
                    rfl

theorem cell22_1294945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 4].length) (baseStart_1294945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294945 prefixEnd_1294945 := by exact prefixLift 1294945
  have htrace : WordTrace (prefixWord ++ tailWord_1294945) baseStart_1294945 baseEnd_1294945 := by
    simpa [prefixWord, tailWord_1294945, baseEnd_1294945] using wordTrace_append hprefix tailTrace_1294945
  have hstable : (prefixWord ++ tailWord_1294945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294945).length < 2 ^ (prefixWord ++ tailWord_1294945).sum := by decide
  have hdescent : baseEnd_1294945 < baseStart_1294945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294958 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 4, 4]
def baseStart_1294958 : Nat := 118140960795 + 1294958 * 2 ^ 59
def prefixEnd_1294958 : Nat := 4983230072969 + 3 ^ 40 * 1294958 * 2
def baseEnd_1294958 : Nat := 443290587590033136379735

theorem tailTrace_1294958 : CollatzResearch.WordTrace tailWord_1294958 prefixEnd_1294958 443290587590033136379735 := by
  unfold tailWord_1294958
  simp only [CollatzResearch.WordTrace]
  refine ⟨5903874805324475257995691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31487332295063868042643685 5903874805324475257995691)
  ·
    refine ⟨8855812207986712886993537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5903874805324475257995691 8855812207986712886993537)
    ·
      refine ⟨6641859155990034665245153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8855812207986712886993537 6641859155990034665245153)
      ·
        refine ⟨4981394366992525998933865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6641859155990034665245153 4981394366992525998933865)
        ·
          refine ⟨3736045775244394499200399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4981394366992525998933865 3736045775244394499200399)
          ·
            refine ⟨5604068662866591748800599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3736045775244394499200399 5604068662866591748800599)
            ·
              refine ⟨8406102994299887623200899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5604068662866591748800599 8406102994299887623200899)
              ·
                refine ⟨12609154491449831434801349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8406102994299887623200899 12609154491449831434801349)
                ·
                  refine ⟨2364216467146843394025253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12609154491449831434801349 2364216467146843394025253)
                  ·
                    refine ⟨443290587590033136379735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2364216467146843394025253 443290587590033136379735)
                    ·
                      rfl

theorem cell22_1294958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_1294958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294958 prefixEnd_1294958 := by exact prefixLift 1294958
  have htrace : WordTrace (prefixWord ++ tailWord_1294958) baseStart_1294958 baseEnd_1294958 := by
    simpa [prefixWord, tailWord_1294958, baseEnd_1294958] using wordTrace_append hprefix tailTrace_1294958
  have hstable : (prefixWord ++ tailWord_1294958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294958).length < 2 ^ (prefixWord ++ tailWord_1294958).sum := by decide
  have hdescent : baseEnd_1294958 < baseStart_1294958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294962 : List Nat := [3, 2, 1, 2, 4, 1, 3, 2, 4]
def baseStart_1294962 : Nat := 118140960795 + 1294962 * 2 ^ 59
def prefixEnd_1294962 : Nat := 4983230072969 + 3 ^ 40 * 1294962 * 2
def baseEnd_1294962 : Nat := 147763985623926153093241

theorem tailTrace_1294962 : CollatzResearch.WordTrace tailWord_1294962 prefixEnd_1294962 147763985623926153093241 := by
  unfold tailWord_1294962
  simp only [CollatzResearch.WordTrace]
  refine ⟨11807786083645327686777785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31487429556387540498074093 11807786083645327686777785)
  ·
    refine ⟨8855839562733995765083339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11807786083645327686777785 8855839562733995765083339)
    ·
      refine ⟨13283759344100993647625009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8855839562733995765083339 13283759344100993647625009)
      ·
        refine ⟨9962819508075745235718757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13283759344100993647625009 9962819508075745235718757)
        ·
          refine ⟨1868028657764202231697267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9962819508075745235718757 1868028657764202231697267)
          ·
            refine ⟨2802042986646303347545901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1868028657764202231697267 2802042986646303347545901)
            ·
              refine ⟨1050766119992363755329713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2802042986646303347545901 1050766119992363755329713)
              ·
                refine ⟨788074589994272816497285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1050766119992363755329713 788074589994272816497285)
                ·
                  refine ⟨147763985623926153093241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 788074589994272816497285 147763985623926153093241)
                  ·
                    rfl

theorem cell22_1294962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_1294962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294962 prefixEnd_1294962 := by exact prefixLift 1294962
  have htrace : WordTrace (prefixWord ++ tailWord_1294962) baseStart_1294962 baseEnd_1294962 := by
    simpa [prefixWord, tailWord_1294962, baseEnd_1294962] using wordTrace_append hprefix tailTrace_1294962
  have hstable : (prefixWord ++ tailWord_1294962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294962).length < 2 ^ (prefixWord ++ tailWord_1294962).sum := by decide
  have hdescent : baseEnd_1294962 < baseStart_1294962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294973 : List Nat := [1, 4, 1, 1, 5, 1, 2, 7]
def baseStart_1294973 : Nat := 118140960795 + 1294973 * 2 ^ 59
def prefixEnd_1294973 : Nat := 4983230072969 + 3 ^ 40 * 1294973 * 2
def baseEnd_1294973 : Nat := 49255080266286455250521

theorem tailTrace_1294973 : CollatzResearch.WordTrace tailWord_1294973 prefixEnd_1294973 49255080266286455250521 := by
  unfold tailWord_1294973
  simp only [CollatzResearch.WordTrace]
  refine ⟨47231545537541459625761573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31487697025027639750507715 47231545537541459625761573)
  ·
    refine ⟨8855914788289023679830295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47231545537541459625761573 8855914788289023679830295)
    ·
      refine ⟨13283872182433535519745443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8855914788289023679830295 13283872182433535519745443)
      ·
        refine ⟨19925808273650303279618165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13283872182433535519745443 19925808273650303279618165)
        ·
          refine ⟨1868044525654715932464203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19925808273650303279618165 1868044525654715932464203)
          ·
            refine ⟨2802066788482073898696305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1868044525654715932464203 2802066788482073898696305)
            ·
              refine ⟨2101550091361555424022229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2802066788482073898696305 2101550091361555424022229)
              ·
                refine ⟨49255080266286455250521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2101550091361555424022229 49255080266286455250521)
                ·
                  rfl

theorem cell22_1294973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 7].length) (baseStart_1294973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1294973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1294973 prefixEnd_1294973 := by exact prefixLift 1294973
  have htrace : WordTrace (prefixWord ++ tailWord_1294973) baseStart_1294973 baseEnd_1294973 := by
    simpa [prefixWord, tailWord_1294973, baseEnd_1294973] using wordTrace_append hprefix tailTrace_1294973
  have hstable : (prefixWord ++ tailWord_1294973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294973).length < 2 ^ (prefixWord ++ tailWord_1294973).sum := by decide
  have hdescent : baseEnd_1294973 < baseStart_1294973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295048 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 3, 4]
def baseStart_1295048 : Nat := 118140960795 + 1295048 * 2 ^ 59
def prefixEnd_1295048 : Nat := 4983230072969 + 3 ^ 40 * 1295048 * 2
def baseEnd_1295048 : Nat := 443321396429302901629459

theorem tailTrace_1295048 : CollatzResearch.WordTrace tailWord_1295048 prefixEnd_1295048 443321396429302901629459 := by
  unfold tailWord_1295048
  simp only [CollatzResearch.WordTrace]
  refine ⟨23617140506134873717370899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31489520674846498289827865 23617140506134873717370899)
  ·
    refine ⟨35425710759202310576056349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23617140506134873717370899 35425710759202310576056349)
    ·
      refine ⟨13284641534700866466021131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35425710759202310576056349 13284641534700866466021131)
      ·
        refine ⟨19926962302051299699031697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13284641534700866466021131 19926962302051299699031697)
        ·
          refine ⟨14945221726538474774273773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19926962302051299699031697 14945221726538474774273773)
          ·
            refine ⟨5604458147451928040352665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14945221726538474774273773 5604458147451928040352665)
            ·
              refine ⟨4203343610588946030264499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5604458147451928040352665 4203343610588946030264499)
              ·
                refine ⟨6305015415883419045396749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4203343610588946030264499 6305015415883419045396749)
                ·
                  refine ⟨2364380780956282142023781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6305015415883419045396749 2364380780956282142023781)
                  ·
                    refine ⟨443321396429302901629459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2364380780956282142023781 443321396429302901629459)
                    ·
                      rfl

theorem cell22_1295048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_1295048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1295048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1295048 prefixEnd_1295048 := by exact prefixLift 1295048
  have htrace : WordTrace (prefixWord ++ tailWord_1295048) baseStart_1295048 baseEnd_1295048 := by
    simpa [prefixWord, tailWord_1295048, baseEnd_1295048] using wordTrace_append hprefix tailTrace_1295048
  have hstable : (prefixWord ++ tailWord_1295048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295048).length < 2 ^ (prefixWord ++ tailWord_1295048).sum := by decide
  have hdescent : baseEnd_1295048 < baseStart_1295048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295080 : List Nat := [2, 1, 4, 1, 4, 1, 2, 1, 6]
def baseStart_1295080 : Nat := 118140960795 + 1295080 * 2 ^ 59
def prefixEnd_1295080 : Nat := 4983230072969 + 3 ^ 40 * 1295080 * 2
def baseEnd_1295080 : Nat := 147777450227755161609787

theorem tailTrace_1295080 : CollatzResearch.WordTrace tailWord_1295080 prefixEnd_1295080 147777450227755161609787 := by
  unfold tailWord_1295080
  simp only [CollatzResearch.WordTrace]
  refine ⟨23617724074076908449953347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31490298765435877933271129 23617724074076908449953347)
  ·
    refine ⟨35426586111115362674930021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23617724074076908449953347 35426586111115362674930021)
    ·
      refine ⟨6642484895834130501549379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35426586111115362674930021 6642484895834130501549379)
      ·
        refine ⟨9963727343751195752324069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6642484895834130501549379 9963727343751195752324069)
        ·
          refine ⟨1868198876953349203560763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9963727343751195752324069 1868198876953349203560763)
          ·
            refine ⟨2802298315430023805341145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1868198876953349203560763 2802298315430023805341145)
            ·
              refine ⟨2101723736572517854005859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2802298315430023805341145 2101723736572517854005859)
              ·
                refine ⟨3152585604858776781008789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2101723736572517854005859 3152585604858776781008789)
                ·
                  refine ⟨147777450227755161609787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3152585604858776781008789 147777450227755161609787)
                  ·
                    rfl

theorem cell22_1295080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 6].length) (baseStart_1295080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1295080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1295080 prefixEnd_1295080 := by exact prefixLift 1295080
  have htrace : WordTrace (prefixWord ++ tailWord_1295080) baseStart_1295080 baseEnd_1295080 := by
    simpa [prefixWord, tailWord_1295080, baseEnd_1295080] using wordTrace_append hprefix tailTrace_1295080
  have hstable : (prefixWord ++ tailWord_1295080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295080).length < 2 ^ (prefixWord ++ tailWord_1295080).sum := by decide
  have hdescent : baseEnd_1295080 < baseStart_1295080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295091 : List Nat := [1, 1, 1, 2, 2, 3, 1, 11]
def baseStart_1295091 : Nat := 118140960795 + 1295091 * 2 ^ 59
def prefixEnd_1295091 : Nat := 4983230072969 + 3 ^ 40 * 1295091 * 2
def baseEnd_1295091 : Nat := 49259568467562791422703

theorem tailTrace_1295091 : CollatzResearch.WordTrace tailWord_1295091 prefixEnd_1295091 49259568467562791422703 := by
  unfold tailWord_1295091
  simp only [CollatzResearch.WordTrace]
  refine ⟨47235849351113965778557127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31490566234075977185704751 47235849351113965778557127)
  ·
    refine ⟨70853774026670948667835691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47235849351113965778557127 70853774026670948667835691)
    ·
      refine ⟨106280661040006423001753537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70853774026670948667835691 106280661040006423001753537)
      ·
        refine ⟨79710495780004817251315153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106280661040006423001753537 79710495780004817251315153)
        ·
          refine ⟨59782871835003612938486365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79710495780004817251315153 59782871835003612938486365)
          ·
            refine ⟨22418576938126354851932387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59782871835003612938486365 22418576938126354851932387)
            ·
              refine ⟨33627865407189532277898581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22418576938126354851932387 33627865407189532277898581)
              ·
                refine ⟨49259568467562791422703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 33627865407189532277898581 49259568467562791422703)
                ·
                  rfl

theorem cell22_1295091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 11].length) (baseStart_1295091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1295091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1295091 prefixEnd_1295091 := by exact prefixLift 1295091
  have htrace : WordTrace (prefixWord ++ tailWord_1295091) baseStart_1295091 baseEnd_1295091 := by
    simpa [prefixWord, tailWord_1295091, baseEnd_1295091] using wordTrace_append hprefix tailTrace_1295091
  have hstable : (prefixWord ++ tailWord_1295091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295091).length < 2 ^ (prefixWord ++ tailWord_1295091).sum := by decide
  have hdescent : baseEnd_1295091 < baseStart_1295091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295108 : List Nat := [2, 3, 2, 2, 1, 1, 3, 8]
def baseStart_1295108 : Nat := 118140960795 + 1295108 * 2 ^ 59
def prefixEnd_1295108 : Nat := 4983230072969 + 3 ^ 40 * 1295108 * 2
def baseEnd_1295108 : Nat := 49260215072831416125475

theorem tailTrace_1295108 : CollatzResearch.WordTrace tailWord_1295108 prefixEnd_1295108 49260215072831416125475 := by
  unfold tailWord_1295108
  simp only [CollatzResearch.WordTrace]
  refine ⟨23618234696026188840962989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31490979594701585121283985 23618234696026188840962989)
  ·
    refine ⟨8856838011009820815361121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23618234696026188840962989 8856838011009820815361121)
    ·
      refine ⟨6642628508257365611520841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8856838011009820815361121 6642628508257365611520841)
      ·
        refine ⟨4981971381193024208640631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6642628508257365611520841 4981971381193024208640631)
        ·
          refine ⟨7472957071789536312960947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4981971381193024208640631 7472957071789536312960947)
          ·
            refine ⟨11209435607684304469441421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7472957071789536312960947 11209435607684304469441421)
            ·
              refine ⟨4203538352881614176040533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11209435607684304469441421 4203538352881614176040533)
              ·
                refine ⟨49260215072831416125475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4203538352881614176040533 49260215072831416125475)
                ·
                  rfl

theorem cell22_1295108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 8].length) (baseStart_1295108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1295108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1295108 prefixEnd_1295108 := by exact prefixLift 1295108
  have htrace : WordTrace (prefixWord ++ tailWord_1295108) baseStart_1295108 baseEnd_1295108 := by
    simpa [prefixWord, tailWord_1295108, baseEnd_1295108] using wordTrace_append hprefix tailTrace_1295108
  have hstable : (prefixWord ++ tailWord_1295108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295108).length < 2 ^ (prefixWord ++ tailWord_1295108).sum := by decide
  have hdescent : baseEnd_1295108 < baseStart_1295108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295191 : List Nat := [1, 1, 3, 2, 4, 3, 2, 2, 1, 3]
def baseStart_1295191 : Nat := 118140960795 + 1295191 * 2 ^ 59
def prefixEnd_1295191 : Nat := 4983230072969 + 3 ^ 40 * 1295191 * 2
def baseEnd_1295191 : Nat := 443370348251698195304021

theorem tailTrace_1295191 : CollatzResearch.WordTrace tailWord_1295191 prefixEnd_1295191 443370348251698195304021 := by
  unfold tailWord_1295191
  simp only [CollatzResearch.WordTrace]
  refine ⟨47239496650751682857197427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31492997767167788571464951 47239496650751682857197427)
  ·
    refine ⟨70859244976127524285796141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47239496650751682857197427 70859244976127524285796141)
    ·
      refine ⟨26572216866047821607173553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70859244976127524285796141 26572216866047821607173553)
      ·
        refine ⟨19929162649535866205380165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26572216866047821607173553 19929162649535866205380165)
        ·
          refine ⟨3736717996787974913508781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19929162649535866205380165 3736717996787974913508781)
          ·
            refine ⟨1401269248795490592565793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3736717996787974913508781 1401269248795490592565793)
            ·
              refine ⟨1050951936596617944424345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1401269248795490592565793 1050951936596617944424345)
              ·
                refine ⟨788213952447463458318259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1050951936596617944424345 788213952447463458318259)
                ·
                  refine ⟨1182320928671195187477389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 788213952447463458318259 1182320928671195187477389)
                  ·
                    refine ⟨443370348251698195304021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1182320928671195187477389 443370348251698195304021)
                    ·
                      rfl

theorem cell22_1295191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 1, 3].length) (baseStart_1295191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1295191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1295191 prefixEnd_1295191 := by exact prefixLift 1295191
  have htrace : WordTrace (prefixWord ++ tailWord_1295191) baseStart_1295191 baseEnd_1295191 := by
    simpa [prefixWord, tailWord_1295191, baseEnd_1295191] using wordTrace_append hprefix tailTrace_1295191
  have hstable : (prefixWord ++ tailWord_1295191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295191).length < 2 ^ (prefixWord ++ tailWord_1295191).sum := by decide
  have hdescent : baseEnd_1295191 < baseStart_1295191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295202 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_1295202 : Nat := 118140960795 + 1295202 * 2 ^ 59
def prefixEnd_1295202 : Nat := 4983230072969 + 3 ^ 40 * 1295202 * 2
def baseEnd_1295202 : Nat := 443374113776497833278987

theorem tailTrace_1295202 : CollatzResearch.WordTrace tailWord_1295202 prefixEnd_1295202 443374113776497833278987 := by
  unfold tailWord_1295202
  simp only [CollatzResearch.WordTrace]
  refine ⟨11809974463427957933961965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31493265235807887823898573 11809974463427957933961965)
  ·
    refine ⟨4428740423785484225235737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11809974463427957933961965 4428740423785484225235737)
    ·
      refine ⟨3321555317839113168926803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4428740423785484225235737 3321555317839113168926803)
      ·
        refine ⟨4982332976758669753390205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3321555317839113168926803 4982332976758669753390205)
        ·
          refine ⟨1868374866284501157521327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4982332976758669753390205 1868374866284501157521327)
          ·
            refine ⟨2802562299426751736281991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1868374866284501157521327 2802562299426751736281991)
            ·
              refine ⟨4203843449140127604422987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2802562299426751736281991 4203843449140127604422987)
              ·
                refine ⟨6305765173710191406634481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4203843449140127604422987 6305765173710191406634481)
                ·
                  refine ⟨4729323880282643554975861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6305765173710191406634481 4729323880282643554975861)
                  ·
                    refine ⟨443374113776497833278987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4729323880282643554975861 443374113776497833278987)
                    ·
                      rfl

theorem cell22_1295202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_1295202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1295202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1295202 prefixEnd_1295202 := by exact prefixLift 1295202
  have htrace : WordTrace (prefixWord ++ tailWord_1295202) baseStart_1295202 baseEnd_1295202 := by
    simpa [prefixWord, tailWord_1295202, baseEnd_1295202] using wordTrace_append hprefix tailTrace_1295202
  have hstable : (prefixWord ++ tailWord_1295202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295202).length < 2 ^ (prefixWord ++ tailWord_1295202).sum := by decide
  have hdescent : baseEnd_1295202 < baseStart_1295202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295322 : List Nat := [3, 1, 1, 2, 4, 2, 1, 3, 5]
def baseStart_1295322 : Nat := 118140960795 + 1295322 * 2 ^ 59
def prefixEnd_1295322 : Nat := 4983230072969 + 3 ^ 40 * 1295322 * 2
def baseEnd_1295322 : Nat := 147805064076285840092873

theorem tailTrace_1295322 : CollatzResearch.WordTrace tailWord_1295322 prefixEnd_1295322 147805064076285840092873 := by
  unfold tailWord_1295322
  simp only [CollatzResearch.WordTrace]
  refine ⟨11811068653319273057554055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31496183075518061486810813 11811068653319273057554055)
  ·
    refine ⟨17716602979978909586331083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11811068653319273057554055 17716602979978909586331083)
    ·
      refine ⟨26574904469968364379496625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17716602979978909586331083 26574904469968364379496625)
      ·
        refine ⟨19931178352476273284622469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26574904469968364379496625 19931178352476273284622469)
        ·
          refine ⟨3737095941089301240866713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19931178352476273284622469 3737095941089301240866713)
          ·
            refine ⟨2802821955816975930650035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3737095941089301240866713 2802821955816975930650035)
            ·
              refine ⟨4204232933725463895975053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2802821955816975930650035 4204232933725463895975053)
              ·
                refine ⟨1576587350147048960990645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4204232933725463895975053 1576587350147048960990645)
                ·
                  refine ⟨147805064076285840092873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1576587350147048960990645 147805064076285840092873)
                  ·
                    rfl

theorem cell22_1295322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_1295322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1295322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1295322 prefixEnd_1295322 := by exact prefixLift 1295322
  have htrace : WordTrace (prefixWord ++ tailWord_1295322) baseStart_1295322 baseEnd_1295322 := by
    simpa [prefixWord, tailWord_1295322, baseEnd_1295322] using wordTrace_append hprefix tailTrace_1295322
  have hstable : (prefixWord ++ tailWord_1295322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295322).length < 2 ^ (prefixWord ++ tailWord_1295322).sum := by decide
  have hdescent : baseEnd_1295322 < baseStart_1295322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295365 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 3, 5]
def baseStart_1295365 : Nat := 118140960795 + 1295365 * 2 ^ 59
def prefixEnd_1295365 : Nat := 4983230072969 + 3 ^ 40 * 1295365 * 2
def baseEnd_1295365 : Nat := 443429912007619741453487

theorem tailTrace_1295365 : CollatzResearch.WordTrace tailWord_1295365 prefixEnd_1295365 443429912007619741453487 := by
  unfold tailWord_1295365
  simp only [CollatzResearch.WordTrace]
  refine ⟨47245842952121310574031549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31497228634747540382687699 47245842952121310574031549)
  ·
    refine ⟨17717191107045491465261831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47245842952121310574031549 17717191107045491465261831)
    ·
      refine ⟨26575786660568237197892747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17717191107045491465261831 26575786660568237197892747)
      ·
        refine ⟨39863679990852355796839121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26575786660568237197892747 39863679990852355796839121)
        ·
          refine ⟨29897759993139266847629341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39863679990852355796839121 29897759993139266847629341)
          ·
            refine ⟨11211659997427225067861003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29897759993139266847629341 11211659997427225067861003)
            ·
              refine ⟨16817489996140837601791505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11211659997427225067861003 16817489996140837601791505)
              ·
                refine ⟨12613117497105628201343629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16817489996140837601791505 12613117497105628201343629)
                ·
                  refine ⟨4729919061414610575503861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12613117497105628201343629 4729919061414610575503861)
                  ·
                    refine ⟨443429912007619741453487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4729919061414610575503861 443429912007619741453487)
                    ·
                      rfl

theorem cell22_1295365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_1295365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1295365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1295365 prefixEnd_1295365 := by exact prefixLift 1295365
  have htrace : WordTrace (prefixWord ++ tailWord_1295365) baseStart_1295365 baseEnd_1295365 := by
    simpa [prefixWord, tailWord_1295365, baseEnd_1295365] using wordTrace_append hprefix tailTrace_1295365
  have hstable : (prefixWord ++ tailWord_1295365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295365).length < 2 ^ (prefixWord ++ tailWord_1295365).sum := by decide
  have hdescent : baseEnd_1295365 < baseStart_1295365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295399 : List Nat := [1, 1, 7, 1, 1, 1, 2, 2, 1, 5]
def baseStart_1295399 : Nat := 118140960795 + 1295399 * 2 ^ 59
def prefixEnd_1295399 : Nat := 4983230072969 + 3 ^ 40 * 1295399 * 2
def baseEnd_1295399 : Nat := 443441550902454986103383

theorem tailTrace_1295399 : CollatzResearch.WordTrace tailWord_1295399 prefixEnd_1295399 443441550902454986103383 := by
  unfold tailWord_1295399
  simp only [CollatzResearch.WordTrace]
  refine ⟨47247083033998134380769251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31498055355998756253846167 47247083033998134380769251)
  ·
    refine ⟨70870624550997201571153877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47247083033998134380769251 70870624550997201571153877)
    ·
      refine ⟨1661030262913996911823919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 70870624550997201571153877 1661030262913996911823919)
      ·
        refine ⟨2491545394370995367735879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1661030262913996911823919 2491545394370995367735879)
        ·
          refine ⟨3737318091556493051603819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2491545394370995367735879 3737318091556493051603819)
          ·
            refine ⟨5605977137334739577405729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3737318091556493051603819 5605977137334739577405729)
            ·
              refine ⟨4204482853001054683054297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5605977137334739577405729 4204482853001054683054297)
              ·
                refine ⟨3153362139750791012290723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4204482853001054683054297 3153362139750791012290723)
                ·
                  refine ⟨4730043209626186518436085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3153362139750791012290723 4730043209626186518436085)
                  ·
                    refine ⟨443441550902454986103383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4730043209626186518436085 443441550902454986103383)
                    ·
                      rfl

theorem cell22_1295399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_1295399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1295399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1295399 prefixEnd_1295399 := by exact prefixLift 1295399
  have htrace : WordTrace (prefixWord ++ tailWord_1295399) baseStart_1295399 baseEnd_1295399 := by
    simpa [prefixWord, tailWord_1295399, baseEnd_1295399] using wordTrace_append hprefix tailTrace_1295399
  have hstable : (prefixWord ++ tailWord_1295399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295399).length < 2 ^ (prefixWord ++ tailWord_1295399).sum := by decide
  have hdescent : baseEnd_1295399 < baseStart_1295399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295416 : List Nat := [2, 1, 2, 1, 5, 3, 1, 2, 2, 3]
def baseStart_1295416 : Nat := 118140960795 + 1295416 * 2 ^ 59
def prefixEnd_1295416 : Nat := 4983230072969 + 3 ^ 40 * 1295416 * 2
def baseEnd_1295416 : Nat := 443447370349872608428331

theorem tailTrace_1295416 : CollatzResearch.WordTrace tailWord_1295416 prefixEnd_1295416 443447370349872608428331 := by
  unfold tailWord_1295416
  simp only [CollatzResearch.WordTrace]
  refine ⟨23623851537468273142069051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31498468716624364189425401 23623851537468273142069051)
  ·
    refine ⟨35435777306202409713103577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23623851537468273142069051 35435777306202409713103577)
    ·
      refine ⟨26576832979651807284827683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35435777306202409713103577 26576832979651807284827683)
      ·
        refine ⟨39865249469477710927241525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26576832979651807284827683 39865249469477710927241525)
        ·
          refine ⟨3737367137763535399428893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39865249469477710927241525 3737367137763535399428893)
          ·
            refine ⟨1401512676661325774785835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3737367137763535399428893 1401512676661325774785835)
            ·
              refine ⟨2102269014991988662178753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1401512676661325774785835 2102269014991988662178753)
              ·
                refine ⟨1576701761243991496634065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2102269014991988662178753 1576701761243991496634065)
                ·
                  refine ⟨1182526320932993622475549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1576701761243991496634065 1182526320932993622475549)
                  ·
                    refine ⟨443447370349872608428331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1182526320932993622475549 443447370349872608428331)
                    ·
                      rfl

theorem cell22_1295416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 2, 3].length) (baseStart_1295416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1295416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1295416 prefixEnd_1295416 := by exact prefixLift 1295416
  have htrace : WordTrace (prefixWord ++ tailWord_1295416) baseStart_1295416 baseEnd_1295416 := by
    simpa [prefixWord, tailWord_1295416, baseEnd_1295416] using wordTrace_append hprefix tailTrace_1295416
  have hstable : (prefixWord ++ tailWord_1295416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295416).length < 2 ^ (prefixWord ++ tailWord_1295416).sum := by decide
  have hdescent : baseEnd_1295416 < baseStart_1295416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295444 : List Nat := [2, 4, 1, 1, 1, 1, 4, 2, 3, 3]
def baseStart_1295444 : Nat := 118140960795 + 1295444 * 2 ^ 59
def prefixEnd_1295444 : Nat := 4983230072969 + 3 ^ 40 * 1295444 * 2
def baseEnd_1295444 : Nat := 443456955322089868728245

theorem tailTrace_1295444 : CollatzResearch.WordTrace tailWord_1295444 prefixEnd_1295444 443456955322089868728245 := by
  unfold tailWord_1295444
  simp only [CollatzResearch.WordTrace]
  refine ⟨23624362159417553533078693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31499149545890071377438257 23624362159417553533078693)
  ·
    refine ⟨4429567904890791287452255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23624362159417553533078693 4429567904890791287452255)
    ·
      refine ⟨6644351857336186931178383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4429567904890791287452255 6644351857336186931178383)
      ·
        refine ⟨9966527786004280396767575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6644351857336186931178383 9966527786004280396767575)
        ·
          refine ⟨14949791679006420595151363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9966527786004280396767575 14949791679006420595151363)
          ·
            refine ⟨22424687518509630892727045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14949791679006420595151363 22424687518509630892727045)
            ·
              refine ⟨4204628909720555792386321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22424687518509630892727045 4204628909720555792386321)
              ·
                refine ⟨3153471682290416844289741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4204628909720555792386321 3153471682290416844289741)
                ·
                  refine ⟨1182551880858906316608653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3153471682290416844289741 1182551880858906316608653)
                  ·
                    refine ⟨443456955322089868728245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1182551880858906316608653 443456955322089868728245)
                    ·
                      rfl

theorem cell22_1295444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_1295444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1295444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1295444 prefixEnd_1295444 := by exact prefixLift 1295444
  have htrace : WordTrace (prefixWord ++ tailWord_1295444) baseStart_1295444 baseEnd_1295444 := by
    simpa [prefixWord, tailWord_1295444, baseEnd_1295444] using wordTrace_append hprefix tailTrace_1295444
  have hstable : (prefixWord ++ tailWord_1295444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295444).length < 2 ^ (prefixWord ++ tailWord_1295444).sum := by decide
  have hdescent : baseEnd_1295444 < baseStart_1295444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295446 : List Nat := [5, 2, 2, 1, 2, 1, 1, 8]
def baseStart_1295446 : Nat := 118140960795 + 1295446 * 2 ^ 59
def prefixEnd_1295446 : Nat := 4983230072969 + 3 ^ 40 * 1295446 * 2
def baseEnd_1295446 : Nat := 49273071106995836686471

theorem tailTrace_1295446 : CollatzResearch.WordTrace tailWord_1295446 prefixEnd_1295446 49273071106995836686471 := by
  unfold tailWord_1295446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2953049829051741337983137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31499198176551907605153461 2953049829051741337983137)
  ·
    refine ⟨2214787371788806003487353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2953049829051741337983137 2214787371788806003487353)
    ·
      refine ⟨1661090528841604502615515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2214787371788806003487353 1661090528841604502615515)
      ·
        refine ⟨2491635793262406753923273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1661090528841604502615515 2491635793262406753923273)
        ·
          refine ⟨1868726844946805065442455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2491635793262406753923273 1868726844946805065442455)
          ·
            refine ⟨2803090267420207598163683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1868726844946805065442455 2803090267420207598163683)
            ·
              refine ⟨4204635401130311397245525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2803090267420207598163683 4204635401130311397245525)
              ·
                refine ⟨49273071106995836686471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4204635401130311397245525 49273071106995836686471)
                ·
                  rfl

theorem cell22_1295446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_1295446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1295446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1295446 prefixEnd_1295446 := by exact prefixLift 1295446
  have htrace : WordTrace (prefixWord ++ tailWord_1295446) baseStart_1295446 baseEnd_1295446 := by
    simpa [prefixWord, tailWord_1295446, baseEnd_1295446] using wordTrace_append hprefix tailTrace_1295446
  have hstable : (prefixWord ++ tailWord_1295446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295446).length < 2 ^ (prefixWord ++ tailWord_1295446).sum := by decide
  have hdescent : baseEnd_1295446 < baseStart_1295446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295521 : List Nat := [1, 2, 3, 3, 1, 1, 5, 1, 1, 4]
def baseStart_1295521 : Nat := 118140960795 + 1295521 * 2 ^ 59
def prefixEnd_1295521 : Nat := 4983230072969 + 3 ^ 40 * 1295521 * 2
def baseEnd_1295521 : Nat := 443483313995687334553009

theorem tailTrace_1295521 : CollatzResearch.WordTrace tailWord_1295521 prefixEnd_1295521 443483313995687334553009 := by
  unfold tailWord_1295521
  simp only [CollatzResearch.WordTrace]
  refine ⟨47251532739556149216710417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31501021826370766144473611 47251532739556149216710417)
  ·
    refine ⟨35438649554667111912532813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47251532739556149216710417 35438649554667111912532813)
    ·
      refine ⟨13289493583000166967199805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35438649554667111912532813 13289493583000166967199805)
      ·
        refine ⟨4983560093625062612699927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13289493583000166967199805 4983560093625062612699927)
        ·
          refine ⟨7475340140437593919049891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4983560093625062612699927 7475340140437593919049891)
          ·
            refine ⟨11213010210656390878574837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7475340140437593919049891 11213010210656390878574837)
            ·
              refine ⟨1051219707249036644866391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11213010210656390878574837 1051219707249036644866391)
              ·
                refine ⟨1576829560873554967299587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1051219707249036644866391 1576829560873554967299587)
                ·
                  refine ⟨2365244341310332450949381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1576829560873554967299587 2365244341310332450949381)
                  ·
                    refine ⟨443483313995687334553009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2365244341310332450949381 443483313995687334553009)
                    ·
                      rfl

theorem cell22_1295521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_1295521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1295521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1295521 prefixEnd_1295521 := by exact prefixLift 1295521
  have htrace : WordTrace (prefixWord ++ tailWord_1295521) baseStart_1295521 baseEnd_1295521 := by
    simpa [prefixWord, tailWord_1295521, baseEnd_1295521] using wordTrace_append hprefix tailTrace_1295521
  have hstable : (prefixWord ++ tailWord_1295521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295521).length < 2 ^ (prefixWord ++ tailWord_1295521).sum := by decide
  have hdescent : baseEnd_1295521 < baseStart_1295521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295532 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 4, 4]
def baseStart_1295532 : Nat := 118140960795 + 1295532 * 2 ^ 59
def prefixEnd_1295532 : Nat := 4983230072969 + 3 ^ 40 * 1295532 * 2
def baseEnd_1295532 : Nat := 443487079520486972527975

theorem tailTrace_1295532 : CollatzResearch.WordTrace tailWord_1295532 prefixEnd_1295532 443487079520486972527975 := by
  unfold tailWord_1295532
  simp only [CollatzResearch.WordTrace]
  refine ⟨23625966971258149047680425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31501289295010865396907233 23625966971258149047680425)
  ·
    refine ⟨17719475228443611785760319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23625966971258149047680425 17719475228443611785760319)
    ·
      refine ⟨26579212842665417678640479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17719475228443611785760319 26579212842665417678640479)
      ·
        refine ⟨39868819263998126517960719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26579212842665417678640479 39868819263998126517960719)
        ·
          refine ⟨59803228895997189776941079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39868819263998126517960719 59803228895997189776941079)
          ·
            refine ⟨89704843343995784665411619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59803228895997189776941079 89704843343995784665411619)
            ·
              refine ⟨134557265015993676998117429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89704843343995784665411619 134557265015993676998117429)
              ·
                refine ⟨12614743595249407218573509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134557265015993676998117429 12614743595249407218573509)
                ·
                  refine ⟨2365264424109263853482533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12614743595249407218573509 2365264424109263853482533)
                  ·
                    refine ⟨443487079520486972527975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2365264424109263853482533 443487079520486972527975)
                    ·
                      rfl

theorem cell22_1295532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_1295532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1295532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1295532 prefixEnd_1295532 := by exact prefixLift 1295532
  have htrace : WordTrace (prefixWord ++ tailWord_1295532) baseStart_1295532 baseEnd_1295532 := by
    simpa [prefixWord, tailWord_1295532, baseEnd_1295532] using wordTrace_append hprefix tailTrace_1295532
  have hstable : (prefixWord ++ tailWord_1295532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295532).length < 2 ^ (prefixWord ++ tailWord_1295532).sum := by decide
  have hdescent : baseEnd_1295532 < baseStart_1295532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295572 : List Nat := [2, 4, 1, 4, 2, 1, 2, 1, 1, 4]
def baseStart_1295572 : Nat := 118140960795 + 1295572 * 2 ^ 59
def prefixEnd_1295572 : Nat := 4983230072969 + 3 ^ 40 * 1295572 * 2
def baseEnd_1295572 : Nat := 443500772337940201527853

theorem tailTrace_1295572 : CollatzResearch.WordTrace tailWord_1295572 prefixEnd_1295572 443500772337940201527853 := by
  unfold tailWord_1295572
  simp only [CollatzResearch.WordTrace]
  refine ⟨23626696431185692463408485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31502261908247589951211313 23626696431185692463408485)
  ·
    refine ⟨4430005580847317336889091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23626696431185692463408485 4430005580847317336889091)
    ·
      refine ⟨6645008371270976005333637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4430005580847317336889091 6645008371270976005333637)
      ·
        refine ⟨1245939069613308001000057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6645008371270976005333637 1245939069613308001000057)
        ·
          refine ⟨934454302209981000750043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1245939069613308001000057 934454302209981000750043)
          ·
            refine ⟨1401681453314971501125065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934454302209981000750043 1401681453314971501125065)
            ·
              refine ⟨1051261089986228625843799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1401681453314971501125065 1051261089986228625843799)
              ·
                refine ⟨1576891634979342938765699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1051261089986228625843799 1576891634979342938765699)
                ·
                  refine ⟨2365337452469014408148549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1576891634979342938765699 2365337452469014408148549)
                  ·
                    refine ⟨443500772337940201527853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2365337452469014408148549 443500772337940201527853)
                    ·
                      rfl

theorem cell22_1295572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_1295572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1295572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1295572 prefixEnd_1295572 := by exact prefixLift 1295572
  have htrace : WordTrace (prefixWord ++ tailWord_1295572) baseStart_1295572 baseEnd_1295572 := by
    simpa [prefixWord, tailWord_1295572, baseEnd_1295572] using wordTrace_append hprefix tailTrace_1295572
  have hstable : (prefixWord ++ tailWord_1295572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295572).length < 2 ^ (prefixWord ++ tailWord_1295572).sum := by decide
  have hdescent : baseEnd_1295572 < baseStart_1295572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295596 : List Nat := [2, 2, 1, 1, 2, 5, 2, 1, 3, 3]
def baseStart_1295596 : Nat := 118140960795 + 1295596 * 2 ^ 59
def prefixEnd_1295596 : Nat := 4983230072969 + 3 ^ 40 * 1295596 * 2
def baseEnd_1295596 : Nat := 443508988028412138927779

theorem tailTrace_1295596 : CollatzResearch.WordTrace tailWord_1295596 prefixEnd_1295596 443508988028412138927779 := by
  unfold tailWord_1295596
  simp only [CollatzResearch.WordTrace]
  refine ⟨23627134107142218512845321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31502845476189624683793761 23627134107142218512845321)
  ·
    refine ⟨17720350580356663884633991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23627134107142218512845321 17720350580356663884633991)
    ·
      refine ⟨26580525870534995826950987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17720350580356663884633991 26580525870534995826950987)
      ·
        refine ⟨39870788805802493740426481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26580525870534995826950987 39870788805802493740426481)
        ·
          refine ⟨29903091604351870305319861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39870788805802493740426481 29903091604351870305319861)
          ·
            refine ⟨2803414837907987841123737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29903091604351870305319861 2803414837907987841123737)
            ·
              refine ⟨2102561128430990880842803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2803414837907987841123737 2102561128430990880842803)
              ·
                refine ⟨3153841692646486321264205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2102561128430990880842803 3153841692646486321264205)
                ·
                  refine ⟨1182690634742432370474077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3153841692646486321264205 1182690634742432370474077)
                  ·
                    refine ⟨443508988028412138927779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1182690634742432370474077 443508988028412138927779)
                    ·
                      rfl

theorem cell22_1295596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 3].length) (baseStart_1295596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1295596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1295596 prefixEnd_1295596 := by exact prefixLift 1295596
  have htrace : WordTrace (prefixWord ++ tailWord_1295596) baseStart_1295596 baseEnd_1295596 := by
    simpa [prefixWord, tailWord_1295596, baseEnd_1295596] using wordTrace_append hprefix tailTrace_1295596
  have hstable : (prefixWord ++ tailWord_1295596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295596).length < 2 ^ (prefixWord ++ tailWord_1295596).sum := by decide
  have hdescent : baseEnd_1295596 < baseStart_1295596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295630 : List Nat := [4, 1, 1, 2, 1, 5, 1, 3, 1, 3]
def baseStart_1295630 : Nat := 118140960795 + 1295630 * 2 ^ 59
def prefixEnd_1295630 : Nat := 4983230072969 + 3 ^ 40 * 1295630 * 2
def baseEnd_1295630 : Nat := 443520626923247383577675

theorem tailTrace_1295630 : CollatzResearch.WordTrace tailWord_1295630 prefixEnd_1295630 443520626923247383577675 := by
  unfold tailWord_1295630
  simp only [CollatzResearch.WordTrace]
  refine ⟨5906938537020157604053543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31503672197440840554952229 5906938537020157604053543)
  ·
    refine ⟨8860407805530236406080315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5906938537020157604053543 8860407805530236406080315)
    ·
      refine ⟨13290611708295354609120473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8860407805530236406080315 13290611708295354609120473)
      ·
        refine ⟨9967958781221515956840355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13290611708295354609120473 9967958781221515956840355)
        ·
          refine ⟨14951938171832273935260533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9967958781221515956840355 14951938171832273935260533)
          ·
            refine ⟨1401744203609275681430675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14951938171832273935260533 1401744203609275681430675)
            ·
              refine ⟨2102616305413913522146013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1401744203609275681430675 2102616305413913522146013)
              ·
                refine ⟨788481114530217570804755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2102616305413913522146013 788481114530217570804755)
                ·
                  refine ⟨1182721671795326356207133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 788481114530217570804755 1182721671795326356207133)
                  ·
                    refine ⟨443520626923247383577675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1182721671795326356207133 443520626923247383577675)
                    ·
                      rfl

theorem cell22_1295630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_1295630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1295630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1295630 prefixEnd_1295630 := by exact prefixLift 1295630
  have htrace : WordTrace (prefixWord ++ tailWord_1295630) baseStart_1295630 baseEnd_1295630 := by
    simpa [prefixWord, tailWord_1295630, baseEnd_1295630] using wordTrace_append hprefix tailTrace_1295630
  have hstable : (prefixWord ++ tailWord_1295630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295630).length < 2 ^ (prefixWord ++ tailWord_1295630).sum := by decide
  have hdescent : baseEnd_1295630 < baseStart_1295630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295701 : List Nat := [1, 3, 2, 2, 3, 1, 2, 2, 2, 4]
def baseStart_1295701 : Nat := 118140960795 + 1295701 * 2 ^ 59
def prefixEnd_1295701 : Nat := 4983230072969 + 3 ^ 40 * 1295701 * 2
def baseEnd_1295701 : Nat := 443544931674226865052457

theorem tailTrace_1295701 : CollatzResearch.WordTrace tailWord_1295701 prefixEnd_1295701 443544931674226865052457 := by
  unfold tailWord_1295701
  simp only [CollatzResearch.WordTrace]
  refine ⟨47258097878904039958262957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31505398585936026638841971 47258097878904039958262957)
  ·
    refine ⟨17721786704589014984348609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47258097878904039958262957 17721786704589014984348609)
    ·
      refine ⟨13291340028441761238261457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17721786704589014984348609 13291340028441761238261457)
      ·
        refine ⟨9968505021331320928696093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13291340028441761238261457 9968505021331320928696093)
        ·
          refine ⟨3738189382999245348261035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9968505021331320928696093 3738189382999245348261035)
          ·
            refine ⟨5607284074498868022391553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3738189382999245348261035 5607284074498868022391553)
            ·
              refine ⟨4205463055874151016793665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5607284074498868022391553 4205463055874151016793665)
              ·
                refine ⟨3154097291905613262595249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4205463055874151016793665 3154097291905613262595249)
                ·
                  refine ⟨2365572968929209946946437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3154097291905613262595249 2365572968929209946946437)
                  ·
                    refine ⟨443544931674226865052457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2365572968929209946946437 443544931674226865052457)
                    ·
                      rfl

theorem cell22_1295701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_1295701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1295701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1295701 prefixEnd_1295701 := by exact prefixLift 1295701
  have htrace : WordTrace (prefixWord ++ tailWord_1295701) baseStart_1295701 baseEnd_1295701 := by
    simpa [prefixWord, tailWord_1295701, baseEnd_1295701] using wordTrace_append hprefix tailTrace_1295701
  have hstable : (prefixWord ++ tailWord_1295701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295701).length < 2 ^ (prefixWord ++ tailWord_1295701).sum := by decide
  have hdescent : baseEnd_1295701 < baseStart_1295701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295703 : List Nat := [1, 1, 3, 2, 3, 3, 2, 2, 2, 3]
def baseStart_1295703 : Nat := 118140960795 + 1295703 * 2 ^ 59
def prefixEnd_1295703 : Nat := 4983230072969 + 3 ^ 40 * 1295703 * 2
def baseEnd_1295703 : Nat := 443545616315099526502451

theorem tailTrace_1295703 : CollatzResearch.WordTrace tailWord_1295703 prefixEnd_1295703 443545616315099526502451 := by
  unfold tailWord_1295703
  simp only [CollatzResearch.WordTrace]
  refine ⟨47258170824896794299835763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31505447216597862866557175 47258170824896794299835763)
  ·
    refine ⟨70887256237345191449753645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47258170824896794299835763 70887256237345191449753645)
    ·
      refine ⟨26582721089004446793657617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70887256237345191449753645 26582721089004446793657617)
      ·
        refine ⟨19937040816753335095243213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26582721089004446793657617 19937040816753335095243213)
        ·
          refine ⟨7476390306282500660716205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19937040816753335095243213 7476390306282500660716205)
          ·
            refine ⟨2803646364855937747768577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7476390306282500660716205 2803646364855937747768577)
            ·
              refine ⟨2102734773641953310826433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2803646364855937747768577 2102734773641953310826433)
              ·
                refine ⟨1577051080231464983119825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2102734773641953310826433 1577051080231464983119825)
                ·
                  refine ⟨1182788310173598737339869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1577051080231464983119825 1182788310173598737339869)
                  ·
                    refine ⟨443545616315099526502451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1182788310173598737339869 443545616315099526502451)
                    ·
                      rfl

theorem cell22_1295703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 3].length) (baseStart_1295703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1295703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1295703 prefixEnd_1295703 := by exact prefixLift 1295703
  have htrace : WordTrace (prefixWord ++ tailWord_1295703) baseStart_1295703 baseEnd_1295703 := by
    simpa [prefixWord, tailWord_1295703, baseEnd_1295703] using wordTrace_append hprefix tailTrace_1295703
  have hstable : (prefixWord ++ tailWord_1295703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295703).length < 2 ^ (prefixWord ++ tailWord_1295703).sum := by decide
  have hdescent : baseEnd_1295703 < baseStart_1295703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295716 : List Nat := [2, 3, 1, 1, 3, 4, 1, 7]
def baseStart_1295716 : Nat := 118140960795 + 1295716 * 2 ^ 59
def prefixEnd_1295716 : Nat := 4983230072969 + 3 ^ 40 * 1295716 * 2
def baseEnd_1295716 : Nat := 49283340720085758436379

theorem tailTrace_1295716 : CollatzResearch.WordTrace tailWord_1295716 prefixEnd_1295716 49283340720085758436379 := by
  unfold tailWord_1295716
  simp only [CollatzResearch.WordTrace]
  refine ⟨23629322486924848760029501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31505763315899798346706001 23629322486924848760029501)
  ·
    refine ⟨8860995932596818285011063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23629322486924848760029501 8860995932596818285011063)
    ·
      refine ⟨13291493898895227427516595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8860995932596818285011063 13291493898895227427516595)
      ·
        refine ⟨19937240848342841141274893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13291493898895227427516595 19937240848342841141274893)
        ·
          refine ⟨7476465318128565427978085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19937240848342841141274893 7476465318128565427978085)
          ·
            refine ⟨1401837247149106017745891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7476465318128565427978085 1401837247149106017745891)
            ·
              refine ⟨2102755870723659026618837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1401837247149106017745891 2102755870723659026618837)
              ·
                refine ⟨49283340720085758436379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2102755870723659026618837 49283340720085758436379)
                ·
                  rfl

theorem cell22_1295716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 7].length) (baseStart_1295716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1295716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1295716 prefixEnd_1295716 := by exact prefixLift 1295716
  have htrace : WordTrace (prefixWord ++ tailWord_1295716) baseStart_1295716 baseEnd_1295716 := by
    simpa [prefixWord, tailWord_1295716, baseEnd_1295716] using wordTrace_append hprefix tailTrace_1295716
  have hstable : (prefixWord ++ tailWord_1295716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295716).length < 2 ^ (prefixWord ++ tailWord_1295716).sum := by decide
  have hdescent : baseEnd_1295716 < baseStart_1295716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295733 : List Nat := [1, 3, 4, 1, 3, 1, 3, 6]
def baseStart_1295733 : Nat := 118140960795 + 1295733 * 2 ^ 59
def prefixEnd_1295733 : Nat := 4983230072969 + 3 ^ 40 * 1295733 * 2
def baseEnd_1295733 : Nat := 49283987325354383139151

theorem tailTrace_1295733 : CollatzResearch.WordTrace tailWord_1295733 prefixEnd_1295733 49283987325354383139151 := by
  unfold tailWord_1295733
  simp only [CollatzResearch.WordTrace]
  refine ⟨47259265014788109423427853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31506176676525406282285235 47259265014788109423427853)
  ·
    refine ⟨17722224380545541033785445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47259265014788109423427853 17722224380545541033785445)
    ·
      refine ⟨3322917071352288943834771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17722224380545541033785445 3322917071352288943834771)
      ·
        refine ⟨4984375607028433415752157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3322917071352288943834771 4984375607028433415752157)
        ·
          refine ⟨1869140852635662530907059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4984375607028433415752157 1869140852635662530907059)
          ·
            refine ⟨2803711278953493796360589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869140852635662530907059 2803711278953493796360589)
            ·
              refine ⟨1051391729607560173635221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2803711278953493796360589 1051391729607560173635221)
              ·
                refine ⟨49283987325354383139151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1051391729607560173635221 49283987325354383139151)
                ·
                  rfl

theorem cell22_1295733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 6].length) (baseStart_1295733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1295733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1295733 prefixEnd_1295733 := by exact prefixLift 1295733
  have htrace : WordTrace (prefixWord ++ tailWord_1295733) baseStart_1295733 baseEnd_1295733 := by
    simpa [prefixWord, tailWord_1295733, baseEnd_1295733] using wordTrace_append hprefix tailTrace_1295733
  have hstable : (prefixWord ++ tailWord_1295733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295733).length < 2 ^ (prefixWord ++ tailWord_1295733).sum := by decide
  have hdescent : baseEnd_1295733 < baseStart_1295733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295874 : List Nat := [3, 4, 1, 2, 1, 3, 2, 2, 4]
def baseStart_1295874 : Nat := 118140960795 + 1295874 * 2 ^ 59
def prefixEnd_1295874 : Nat := 4983230072969 + 3 ^ 40 * 1295874 * 2
def baseEnd_1295874 : Nat := 147868051036570693492309

theorem tailTrace_1295874 : CollatzResearch.WordTrace tailWord_1295874 prefixEnd_1295874 147868051036570693492309 := by
  unfold tailWord_1295874
  simp only [CollatzResearch.WordTrace]
  refine ⟨11816101926819322626077669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31509605138184860336207117 11816101926819322626077669)
  ·
    refine ⟨2215519111278622992389563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11816101926819322626077669 2215519111278622992389563)
    ·
      refine ⟨3323278666917934488584345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2215519111278622992389563 3323278666917934488584345)
      ·
        refine ⟨2492459000188450866438259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3323278666917934488584345 2492459000188450866438259)
        ·
          refine ⟨3738688500282676299657389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2492459000188450866438259 3738688500282676299657389)
          ·
            refine ⟨1402008187606003612371521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3738688500282676299657389 1402008187606003612371521)
            ·
              refine ⟨1051506140704502709278641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1402008187606003612371521 1051506140704502709278641)
              ·
                refine ⟨788629605528377031958981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1051506140704502709278641 788629605528377031958981)
                ·
                  refine ⟨147868051036570693492309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 788629605528377031958981 147868051036570693492309)
                  ·
                    rfl

theorem cell22_1295874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_1295874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1295874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1295874 prefixEnd_1295874 := by exact prefixLift 1295874
  have htrace : WordTrace (prefixWord ++ tailWord_1295874) baseStart_1295874 baseEnd_1295874 := by
    simpa [prefixWord, tailWord_1295874, baseEnd_1295874] using wordTrace_append hprefix tailTrace_1295874
  have hstable : (prefixWord ++ tailWord_1295874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295874).length < 2 ^ (prefixWord ++ tailWord_1295874).sum := by decide
  have hdescent : baseEnd_1295874 < baseStart_1295874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295975 : List Nat := [1, 1, 5, 1, 1, 1, 5, 3, 4]
def baseStart_1295975 : Nat := 118140960795 + 1295975 * 2 ^ 59
def prefixEnd_1295975 : Nat := 4983230072969 + 3 ^ 40 * 1295975 * 2
def baseEnd_1295975 : Nat := 147879575824593827900539

theorem tailTrace_1295975 : CollatzResearch.WordTrace tailWord_1295975 prefixEnd_1295975 147879575824593827900539 := by
  unfold tailWord_1295975
  simp only [CollatzResearch.WordTrace]
  refine ⟨47268091479911384753737379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31512060986607589835824919 47268091479911384753737379)
  ·
    refine ⟨70902137219867077130606069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47268091479911384753737379 70902137219867077130606069)
    ·
      refine ⟨6647075364362538480994319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70902137219867077130606069 6647075364362538480994319)
      ·
        refine ⟨9970613046543807721491479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6647075364362538480994319 9970613046543807721491479)
        ·
          refine ⟨14955919569815711582237219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9970613046543807721491479 14955919569815711582237219)
          ·
            refine ⟨22433879354723567373355829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14955919569815711582237219 22433879354723567373355829)
            ·
              refine ⟨2103176189505334441252109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22433879354723567373355829 2103176189505334441252109)
              ·
                refine ⟨788691071064500415469541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2103176189505334441252109 788691071064500415469541)
                ·
                  refine ⟨147879575824593827900539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 788691071064500415469541 147879575824593827900539)
                  ·
                    rfl

theorem cell22_1295975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 4].length) (baseStart_1295975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1295975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1295975 prefixEnd_1295975 := by exact prefixLift 1295975
  have htrace : WordTrace (prefixWord ++ tailWord_1295975) baseStart_1295975 baseEnd_1295975 := by
    simpa [prefixWord, tailWord_1295975, baseEnd_1295975] using wordTrace_append hprefix tailTrace_1295975
  have hstable : (prefixWord ++ tailWord_1295975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295975).length < 2 ^ (prefixWord ++ tailWord_1295975).sum := by decide
  have hdescent : baseEnd_1295975 < baseStart_1295975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296007 : List Nat := [1, 1, 4, 2, 1, 3, 4, 1, 2, 3]
def baseStart_1296007 : Nat := 118140960795 + 1296007 * 2 ^ 59
def prefixEnd_1296007 : Nat := 4983230072969 + 3 ^ 40 * 1296007 * 2
def baseEnd_1296007 : Nat := 443649681727744066901519

theorem tailTrace_1296007 : CollatzResearch.WordTrace tailWord_1296007 prefixEnd_1296007 443649681727744066901519 := by
  unfold tailWord_1296007
  simp only [CollatzResearch.WordTrace]
  refine ⟨47269258615795454218902275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31512839077196969479268183 47269258615795454218902275)
  ·
    refine ⟨70903887923693181328353413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47269258615795454218902275 70903887923693181328353413)
    ·
      refine ⟨13294478985692471499066265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70903887923693181328353413 13294478985692471499066265)
      ·
        refine ⟨9970859239269353624299699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13294478985692471499066265 9970859239269353624299699)
        ·
          refine ⟨14956288858904030436449549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9970859239269353624299699 14956288858904030436449549)
          ·
            refine ⟨5608608322089011413668581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14956288858904030436449549 5608608322089011413668581)
            ·
              refine ⟨1051614060391689640062859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5608608322089011413668581 1051614060391689640062859)
              ·
                refine ⟨1577421090587534460094289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1051614060391689640062859 1577421090587534460094289)
                ·
                  refine ⟨1183065817940650845070717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1577421090587534460094289 1183065817940650845070717)
                  ·
                    refine ⟨443649681727744066901519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1183065817940650845070717 443649681727744066901519)
                    ·
                      rfl

theorem cell22_1296007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_1296007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296007 prefixEnd_1296007 := by exact prefixLift 1296007
  have htrace : WordTrace (prefixWord ++ tailWord_1296007) baseStart_1296007 baseEnd_1296007 := by
    simpa [prefixWord, tailWord_1296007, baseEnd_1296007] using wordTrace_append hprefix tailTrace_1296007
  have hstable : (prefixWord ++ tailWord_1296007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296007).length < 2 ^ (prefixWord ++ tailWord_1296007).sum := by decide
  have hdescent : baseEnd_1296007 < baseStart_1296007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296048 : List Nat := [2, 1, 1, 1, 2, 1, 5, 4, 5]
def baseStart_1296048 : Nat := 118140960795 + 1296048 * 2 ^ 59
def prefixEnd_1296048 : Nat := 4983230072969 + 3 ^ 40 * 1296048 * 2
def baseEnd_1296048 : Nat := 147887905621877875542131

theorem tailTrace_1296048 : CollatzResearch.WordTrace tailWord_1296048 prefixEnd_1296048 147887905621877875542131 := by
  unfold tailWord_1296048
  simp only [CollatzResearch.WordTrace]
  refine ⟨23635377004323459110572399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31513836005764612147429865 23635377004323459110572399)
  ·
    refine ⟨35453065506485188665858599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23635377004323459110572399 35453065506485188665858599)
    ·
      refine ⟨53179598259727782998787899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35453065506485188665858599 53179598259727782998787899)
      ·
        refine ⟨79769397389591674498181849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53179598259727782998787899 79769397389591674498181849)
        ·
          refine ⟨59827048042193755873636387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79769397389591674498181849 59827048042193755873636387)
          ·
            refine ⟨89740572063290633810454581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59827048042193755873636387 89740572063290633810454581)
            ·
              refine ⟨8413178630933496919730117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89740572063290633810454581 8413178630933496919730117)
              ·
                refine ⟨1577470993300030672449397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8413178630933496919730117 1577470993300030672449397)
                ·
                  refine ⟨147887905621877875542131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1577470993300030672449397 147887905621877875542131)
                  ·
                    rfl

theorem cell22_1296048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 5].length) (baseStart_1296048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296048 prefixEnd_1296048 := by exact prefixLift 1296048
  have htrace : WordTrace (prefixWord ++ tailWord_1296048) baseStart_1296048 baseEnd_1296048 := by
    simpa [prefixWord, tailWord_1296048, baseEnd_1296048] using wordTrace_append hprefix tailTrace_1296048
  have hstable : (prefixWord ++ tailWord_1296048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296048).length < 2 ^ (prefixWord ++ tailWord_1296048).sum := by decide
  have hdescent : baseEnd_1296048 < baseStart_1296048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296063 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 2, 5]
def baseStart_1296063 : Nat := 118140960795 + 1296063 * 2 ^ 59
def prefixEnd_1296063 : Nat := 4983230072969 + 3 ^ 40 * 1296063 * 2
def baseEnd_1296063 : Nat := 443668851672178587501347

theorem tailTrace_1296063 : CollatzResearch.WordTrace tailWord_1296063 prefixEnd_1296063 443668851672178587501347 := by
  unfold tailWord_1296063
  simp only [CollatzResearch.WordTrace]
  refine ⟨47271301103592575782940843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31514200735728383855293895 47271301103592575782940843)
  ·
    refine ⟨70906951655388863674411265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47271301103592575782940843 70906951655388863674411265)
    ·
      refine ⟨53180213741541647755808449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70906951655388863674411265 53180213741541647755808449)
      ·
        refine ⟨39885160306156235816856337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53180213741541647755808449 39885160306156235816856337)
        ·
          refine ⟨29913870229617176862642253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39885160306156235816856337 29913870229617176862642253)
          ·
            refine ⟨11217701336106441323490845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29913870229617176862642253 11217701336106441323490845)
            ·
              refine ⟨4206638001039915496309067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11217701336106441323490845 4206638001039915496309067)
              ·
                refine ⟨6309957001559873244463601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4206638001039915496309067 6309957001559873244463601)
                ·
                  refine ⟨4732467751169904933347701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6309957001559873244463601 4732467751169904933347701)
                  ·
                    refine ⟨443668851672178587501347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4732467751169904933347701 443668851672178587501347)
                    ·
                      rfl

theorem cell22_1296063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 5].length) (baseStart_1296063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296063 prefixEnd_1296063 := by exact prefixLift 1296063
  have htrace : WordTrace (prefixWord ++ tailWord_1296063) baseStart_1296063 baseEnd_1296063 := by
    simpa [prefixWord, tailWord_1296063, baseEnd_1296063] using wordTrace_append hprefix tailTrace_1296063
  have hstable : (prefixWord ++ tailWord_1296063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296063).length < 2 ^ (prefixWord ++ tailWord_1296063).sum := by decide
  have hdescent : baseEnd_1296063 < baseStart_1296063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296095 : List Nat := [1, 1, 2, 3, 2, 2, 3, 3, 1, 4]
def baseStart_1296095 : Nat := 118140960795 + 1296095 * 2 ^ 59
def prefixEnd_1296095 : Nat := 4983230072969 + 3 ^ 40 * 1296095 * 2
def baseEnd_1296095 : Nat := 443679805926141170701249

theorem tailTrace_1296095 : CollatzResearch.WordTrace tailWord_1296095 prefixEnd_1296095 443679805926141170701249 := by
  unfold tailWord_1296095
  simp only [CollatzResearch.WordTrace]
  refine ⟨47272468239476645248105739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31514978826317763498737159 47272468239476645248105739)
  ·
    refine ⟨70908702359214967872158609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47272468239476645248105739 70908702359214967872158609)
    ·
      refine ⟨53181526769411225904118957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70908702359214967872158609 53181526769411225904118957)
      ·
        refine ⟨19943072538529209714044609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53181526769411225904118957 19943072538529209714044609)
        ·
          refine ⟨14957304403896907285533457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19943072538529209714044609 14957304403896907285533457)
          ·
            refine ⟨11217978302922680464150093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14957304403896907285533457 11217978302922680464150093)
            ·
              refine ⟨4206741863596005174056285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11217978302922680464150093 4206741863596005174056285)
              ·
                refine ⟨1577528198848501940271107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4206741863596005174056285 1577528198848501940271107)
                ·
                  refine ⟨2366292298272752910406661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1577528198848501940271107 2366292298272752910406661)
                  ·
                    refine ⟨443679805926141170701249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2366292298272752910406661 443679805926141170701249)
                    ·
                      rfl

theorem cell22_1296095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 4].length) (baseStart_1296095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296095 prefixEnd_1296095 := by exact prefixLift 1296095
  have htrace : WordTrace (prefixWord ++ tailWord_1296095) baseStart_1296095 baseEnd_1296095 := by
    simpa [prefixWord, tailWord_1296095, baseEnd_1296095] using wordTrace_append hprefix tailTrace_1296095
  have hstable : (prefixWord ++ tailWord_1296095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296095).length < 2 ^ (prefixWord ++ tailWord_1296095).sum := by decide
  have hdescent : baseEnd_1296095 < baseStart_1296095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296099 : List Nat := [1, 1, 1, 7, 3, 1, 1, 2, 5]
def baseStart_1296099 : Nat := 118140960795 + 1296099 * 2 ^ 59
def prefixEnd_1296099 : Nat := 4983230072969 + 3 ^ 40 * 1296099 * 2
def baseEnd_1296099 : Nat := 147893725069295497867079

theorem tailTrace_1296099 : CollatzResearch.WordTrace tailWord_1296099 prefixEnd_1296099 147893725069295497867079 := by
  unfold tailWord_1296099
  simp only [CollatzResearch.WordTrace]
  refine ⟨47272614131462153931251351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31515076087641435954167567 47272614131462153931251351)
  ·
    refine ⟨70908921197193230896877027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47272614131462153931251351 70908921197193230896877027)
    ·
      refine ⟨106363381795789846345315541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70908921197193230896877027 106363381795789846345315541)
      ·
        refine ⟨2492891760838824523718333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 106363381795789846345315541 2492891760838824523718333)
        ·
          refine ⟨934834410314559196394375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2492891760838824523718333 934834410314559196394375)
          ·
            refine ⟨1402251615471838794591563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934834410314559196394375 1402251615471838794591563)
            ·
              refine ⟨2103377423207758191887345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1402251615471838794591563 2103377423207758191887345)
              ·
                refine ⟨1577533067405818643915509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2103377423207758191887345 1577533067405818643915509)
                ·
                  refine ⟨147893725069295497867079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1577533067405818643915509 147893725069295497867079)
                  ·
                    rfl

theorem cell22_1296099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 5].length) (baseStart_1296099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296099 prefixEnd_1296099 := by exact prefixLift 1296099
  have htrace : WordTrace (prefixWord ++ tailWord_1296099) baseStart_1296099 baseEnd_1296099 := by
    simpa [prefixWord, tailWord_1296099, baseEnd_1296099] using wordTrace_append hprefix tailTrace_1296099
  have hstable : (prefixWord ++ tailWord_1296099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296099).length < 2 ^ (prefixWord ++ tailWord_1296099).sum := by decide
  have hdescent : baseEnd_1296099 < baseStart_1296099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296108 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 3, 5]
def baseStart_1296108 : Nat := 118140960795 + 1296108 * 2 ^ 59
def prefixEnd_1296108 : Nat := 4983230072969 + 3 ^ 40 * 1296108 * 2
def baseEnd_1296108 : Nat := 443684256091813470126209

theorem tailTrace_1296108 : CollatzResearch.WordTrace tailWord_1296108 prefixEnd_1296108 443684256091813470126209 := by
  unfold tailWord_1296108
  simp only [CollatzResearch.WordTrace]
  refine ⟨23636471194214774234164489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31515294925619698978885985 23636471194214774234164489)
  ·
    refine ⟨17727353395661080675623367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23636471194214774234164489 17727353395661080675623367)
    ·
      refine ⟨26591030093491621013435051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17727353395661080675623367 26591030093491621013435051)
      ·
        refine ⟨39886545140237431520152577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26591030093491621013435051 39886545140237431520152577)
        ·
          refine ⟨29914908855178073640114433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39886545140237431520152577 29914908855178073640114433)
          ·
            refine ⟨22436181641383555230085825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29914908855178073640114433 22436181641383555230085825)
            ·
              refine ⟨16827136231037666422564369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22436181641383555230085825 16827136231037666422564369)
              ·
                refine ⟨12620352173278249816923277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16827136231037666422564369 12620352173278249816923277)
                ·
                  refine ⟨4732632064979343681346229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12620352173278249816923277 4732632064979343681346229)
                  ·
                    refine ⟨443684256091813470126209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4732632064979343681346229 443684256091813470126209)
                    ·
                      rfl

theorem cell22_1296108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_1296108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296108 prefixEnd_1296108 := by exact prefixLift 1296108
  have htrace : WordTrace (prefixWord ++ tailWord_1296108) baseStart_1296108 baseEnd_1296108 := by
    simpa [prefixWord, tailWord_1296108, baseEnd_1296108] using wordTrace_append hprefix tailTrace_1296108
  have hstable : (prefixWord ++ tailWord_1296108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296108).length < 2 ^ (prefixWord ++ tailWord_1296108).sum := by decide
  have hdescent : baseEnd_1296108 < baseStart_1296108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296110 : List Nat := [4, 1, 2, 1, 1, 2, 4, 1, 6]
def baseStart_1296110 : Nat := 118140960795 + 1296110 * 2 ^ 59
def prefixEnd_1296110 : Nat := 4983230072969 + 3 ^ 40 * 1296110 * 2
def baseEnd_1296110 : Nat := 147894980244228710525401

theorem tailTrace_1296110 : CollatzResearch.WordTrace tailWord_1296110 prefixEnd_1296110 147894980244228710525401 := by
  unfold tailWord_1296110
  simp only [CollatzResearch.WordTrace]
  refine ⟨5909126916802787851237723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31515343556281535206601189 5909126916802787851237723)
  ·
    refine ⟨8863690375204181776856585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5909126916802787851237723 8863690375204181776856585)
    ·
      refine ⟨6647767781403136332642439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8863690375204181776856585 6647767781403136332642439)
      ·
        refine ⟨9971651672104704498963659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6647767781403136332642439 9971651672104704498963659)
        ·
          refine ⟨14957477508157056748445489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9971651672104704498963659 14957477508157056748445489)
          ·
            refine ⟨11218108131117792561334117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14957477508157056748445489 11218108131117792561334117)
            ·
              refine ⟨2103395274584586105250147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11218108131117792561334117 2103395274584586105250147)
              ·
                refine ⟨3155092911876879157875221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2103395274584586105250147 3155092911876879157875221)
                ·
                  refine ⟨147894980244228710525401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3155092911876879157875221 147894980244228710525401)
                  ·
                    rfl

theorem cell22_1296110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_1296110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296110 prefixEnd_1296110 := by exact prefixLift 1296110
  have htrace : WordTrace (prefixWord ++ tailWord_1296110) baseStart_1296110 baseEnd_1296110 := by
    simpa [prefixWord, tailWord_1296110, baseEnd_1296110] using wordTrace_append hprefix tailTrace_1296110
  have hstable : (prefixWord ++ tailWord_1296110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296110).length < 2 ^ (prefixWord ++ tailWord_1296110).sum := by decide
  have hdescent : baseEnd_1296110 < baseStart_1296110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
