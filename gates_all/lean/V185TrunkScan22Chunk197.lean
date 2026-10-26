import V185TrunkScan22Chunk196

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1756800 : List Nat := [2, 1, 1, 2, 1, 4, 2, 9]
def baseStart_1756800 : Nat := 118140960795 + 1756800 * 2 ^ 59
def prefixEnd_1756800 : Nat := 4983230072969 + 3 ^ 40 * 1756800 * 2
def baseEnd_1756800 : Nat := 66820949171765314490417

theorem tailTrace_1756800 : CollatzResearch.WordTrace tailWord_1756800 prefixEnd_1756800 66820949171765314490417 := by
  unfold tailWord_1756800
  simp only [CollatzResearch.WordTrace]
  refine ⟨32037880017710556198949927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42717173356947408265266569 32037880017710556198949927)
  ·
    refine ⟨48056820026565834298424891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32037880017710556198949927 48056820026565834298424891)
    ·
      refine ⟨72085230039848751447637337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48056820026565834298424891 72085230039848751447637337)
      ·
        refine ⟨54063922529886563585728003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72085230039848751447637337 54063922529886563585728003)
        ·
          refine ⟨81095883794829845378592005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54063922529886563585728003 81095883794829845378592005)
          ·
            refine ⟨15205478211530596008486001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81095883794829845378592005 15205478211530596008486001)
            ·
              refine ⟨11404108658647947006364501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15205478211530596008486001 11404108658647947006364501)
              ·
                refine ⟨66820949171765314490417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11404108658647947006364501 66820949171765314490417)
                ·
                  rfl

theorem cell22_1756800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 9].length) (baseStart_1756800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756800 prefixEnd_1756800 := by exact prefixLift 1756800
  have htrace : WordTrace (prefixWord ++ tailWord_1756800) baseStart_1756800 baseEnd_1756800 := by
    simpa [prefixWord, tailWord_1756800, baseEnd_1756800] using wordTrace_append hprefix tailTrace_1756800
  have hstable : (prefixWord ++ tailWord_1756800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756800).length < 2 ^ (prefixWord ++ tailWord_1756800).sum := by decide
  have hdescent : baseEnd_1756800 < baseStart_1756800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756840 : List Nat := [2, 1, 7, 1, 2, 1, 1, 1, 6]
def baseStart_1756840 : Nat := 118140960795 + 1756840 * 2 ^ 59
def prefixEnd_1756840 : Nat := 4983230072969 + 3 ^ 40 * 1756840 * 2
def baseEnd_1756840 : Nat := 200467411787780353137877

theorem tailTrace_1756840 : CollatzResearch.WordTrace tailWord_1756840 prefixEnd_1756840 200467411787780353137877 := by
  unfold tailWord_1756840
  simp only [CollatzResearch.WordTrace]
  refine ⟨32038609477638099614677987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42718145970184132819570649 32038609477638099614677987)
  ·
    refine ⟨48057914216457149422016981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32038609477638099614677987 48057914216457149422016981)
    ·
      refine ⟨1126357364448214439578523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 48057914216457149422016981 1126357364448214439578523)
      ·
        refine ⟨1689536046672321659367785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1126357364448214439578523 1689536046672321659367785)
        ·
          refine ⟨1267152035004241244525839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1689536046672321659367785 1267152035004241244525839)
          ·
            refine ⟨1900728052506361866788759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267152035004241244525839 1900728052506361866788759)
            ·
              refine ⟨2851092078759542800183139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1900728052506361866788759 2851092078759542800183139)
              ·
                refine ⟨4276638118139314200274709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2851092078759542800183139 4276638118139314200274709)
                ·
                  refine ⟨200467411787780353137877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4276638118139314200274709 200467411787780353137877)
                  ·
                    rfl

theorem cell22_1756840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 6].length) (baseStart_1756840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756840 prefixEnd_1756840 := by exact prefixLift 1756840
  have htrace : WordTrace (prefixWord ++ tailWord_1756840) baseStart_1756840 baseEnd_1756840 := by
    simpa [prefixWord, tailWord_1756840, baseEnd_1756840] using wordTrace_append hprefix tailTrace_1756840
  have hstable : (prefixWord ++ tailWord_1756840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756840).length < 2 ^ (prefixWord ++ tailWord_1756840).sum := by decide
  have hdescent : baseEnd_1756840 < baseStart_1756840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756909 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_1756909 : Nat := 118140960795 + 1756909 * 2 ^ 59
def prefixEnd_1756909 : Nat := 4983230072969 + 3 ^ 40 * 1756909 * 2
def baseEnd_1756909 : Nat := 601425855473447879438419

theorem tailTrace_1756909 : CollatzResearch.WordTrace tailWord_1756909 prefixEnd_1756909 601425855473447879438419 := by
  unfold tailWord_1756909
  simp only [CollatzResearch.WordTrace]
  refine ⟨64079735592026224013617781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42719823728017482675745187 64079735592026224013617781)
  ·
    refine ⟨6007475211752458501276667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64079735592026224013617781 6007475211752458501276667)
    ·
      refine ⟨9011212817628687751915001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6007475211752458501276667 9011212817628687751915001)
      ·
        refine ⟨6758409613221515813936251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9011212817628687751915001 6758409613221515813936251)
        ·
          refine ⟨10137614419832273720904377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6758409613221515813936251 10137614419832273720904377)
          ·
            refine ⟨7603210814874205290678283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10137614419832273720904377 7603210814874205290678283)
            ·
              refine ⟨11404816222311307936017425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7603210814874205290678283 11404816222311307936017425)
              ·
                refine ⟨8553612166733480952013069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11404816222311307936017425 8553612166733480952013069)
                ·
                  refine ⟨3207604562525055357004901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8553612166733480952013069 3207604562525055357004901)
                  ·
                    refine ⟨601425855473447879438419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3207604562525055357004901 601425855473447879438419)
                    ·
                      rfl

theorem cell22_1756909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_1756909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756909 prefixEnd_1756909 := by exact prefixLift 1756909
  have htrace : WordTrace (prefixWord ++ tailWord_1756909) baseStart_1756909 baseEnd_1756909 := by
    simpa [prefixWord, tailWord_1756909, baseEnd_1756909] using wordTrace_append hprefix tailTrace_1756909
  have hstable : (prefixWord ++ tailWord_1756909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756909).length < 2 ^ (prefixWord ++ tailWord_1756909).sum := by decide
  have hdescent : baseEnd_1756909 < baseStart_1756909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756986 : List Nat := [3, 1, 1, 1, 5, 3, 2, 6]
def baseStart_1756986 : Nat := 118140960795 + 1756986 * 2 ^ 59
def prefixEnd_1756986 : Nat := 4983230072969 + 3 ^ 40 * 1756986 * 2
def baseEnd_1756986 : Nat := 66828023794116149473687

theorem tailTrace_1756986 : CollatzResearch.WordTrace tailWord_1756986 prefixEnd_1756986 66828023794116149473687 := by
  unfold tailWord_1756986
  simp only [CollatzResearch.WordTrace]
  refine ⟨16020636003186816541042703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42721696008498177442780541 16020636003186816541042703)
  ·
    refine ⟨24030954004780224811564055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16020636003186816541042703 24030954004780224811564055)
    ·
      refine ⟨36046431007170337217346083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24030954004780224811564055 36046431007170337217346083)
      ·
        refine ⟨54069646510755505826019125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36046431007170337217346083 54069646510755505826019125)
        ·
          refine ⟨5069029360383328671189293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54069646510755505826019125 5069029360383328671189293)
          ·
            refine ⟨1900886010143748251695985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5069029360383328671189293 1900886010143748251695985)
            ·
              refine ⟨1425664507607811188771989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1900886010143748251695985 1425664507607811188771989)
              ·
                refine ⟨66828023794116149473687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1425664507607811188771989 66828023794116149473687)
                ·
                  rfl

theorem cell22_1756986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 6].length) (baseStart_1756986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756986 prefixEnd_1756986 := by exact prefixLift 1756986
  have htrace : WordTrace (prefixWord ++ tailWord_1756986) baseStart_1756986 baseEnd_1756986 := by
    simpa [prefixWord, tailWord_1756986, baseEnd_1756986] using wordTrace_append hprefix tailTrace_1756986
  have hstable : (prefixWord ++ tailWord_1756986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756986).length < 2 ^ (prefixWord ++ tailWord_1756986).sum := by decide
  have hdescent : baseEnd_1756986 < baseStart_1756986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756997 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 9]
def baseStart_1756997 : Nat := 118140960795 + 1756997 * 2 ^ 59
def prefixEnd_1756997 : Nat := 4983230072969 + 3 ^ 40 * 1756997 * 2
def baseEnd_1756997 : Nat := 200485326557281661079383

theorem tailTrace_1756997 : CollatzResearch.WordTrace tailWord_1756997 prefixEnd_1756997 200485326557281661079383 := by
  unfold tailWord_1756997
  simp only [CollatzResearch.WordTrace]
  refine ⟨64082945215707415042821245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42721963477138276695214163 64082945215707415042821245)
  ·
    refine ⟨24031104455890280641057967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64082945215707415042821245 24031104455890280641057967)
    ·
      refine ⟨36046656683835420961586951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24031104455890280641057967 36046656683835420961586951)
      ·
        refine ⟨54069985025753131442380427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36046656683835420961586951 54069985025753131442380427)
        ·
          refine ⟨81104977538629697163570641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54069985025753131442380427 81104977538629697163570641)
          ·
            refine ⟨60828733153972272872677981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81104977538629697163570641 60828733153972272872677981)
            ·
              refine ⟨22810774932739602327254243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60828733153972272872677981 22810774932739602327254243)
              ·
                refine ⟨34216162399109403490881365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22810774932739602327254243 34216162399109403490881365)
                ·
                  refine ⟨200485326557281661079383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34216162399109403490881365 200485326557281661079383)
                  ·
                    rfl

theorem cell22_1756997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_1756997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756997 prefixEnd_1756997 := by exact prefixLift 1756997
  have htrace : WordTrace (prefixWord ++ tailWord_1756997) baseStart_1756997 baseEnd_1756997 := by
    simpa [prefixWord, tailWord_1756997, baseEnd_1756997] using wordTrace_append hprefix tailTrace_1756997
  have hstable : (prefixWord ++ tailWord_1756997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756997).length < 2 ^ (prefixWord ++ tailWord_1756997).sum := by decide
  have hdescent : baseEnd_1756997 < baseStart_1756997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757136 : List Nat := [2, 1, 1, 1, 1, 2, 5, 3, 3, 3]
def baseStart_1757136 : Nat := 118140960795 + 1757136 * 2 ^ 59
def prefixEnd_1757136 : Nat := 4983230072969 + 3 ^ 40 * 1757136 * 2
def baseEnd_1757136 : Nat := 601503562212494954012723

theorem tailTrace_1757136 : CollatzResearch.WordTrace tailWord_1757136 prefixEnd_1757136 601503562212494954012723 := by
  unfold tailWord_1757136
  simp only [CollatzResearch.WordTrace]
  refine ⟨32044007481101920891065631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42725343308135894521420841 32044007481101920891065631)
  ·
    refine ⟨48066011221652881336598447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32044007481101920891065631 48066011221652881336598447)
    ·
      refine ⟨72099016832479322004897671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48066011221652881336598447 72099016832479322004897671)
      ·
        refine ⟨108148525248718983007346507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72099016832479322004897671 108148525248718983007346507)
        ·
          refine ⟨162222787873078474511019761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108148525248718983007346507 162222787873078474511019761)
          ·
            refine ⟨121667090904808855883264821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162222787873078474511019761 121667090904808855883264821)
            ·
              refine ⟨11406289772325830239056077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121667090904808855883264821 11406289772325830239056077)
              ·
                refine ⟨4277358664622186339646029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11406289772325830239056077 4277358664622186339646029)
                ·
                  refine ⟨1604009499233319877367261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4277358664622186339646029 1604009499233319877367261)
                  ·
                    refine ⟨601503562212494954012723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1604009499233319877367261 601503562212494954012723)
                    ·
                      rfl

theorem cell22_1757136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 3, 3].length) (baseStart_1757136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757136 prefixEnd_1757136 := by exact prefixLift 1757136
  have htrace : WordTrace (prefixWord ++ tailWord_1757136) baseStart_1757136 baseEnd_1757136 := by
    simpa [prefixWord, tailWord_1757136, baseEnd_1757136] using wordTrace_append hprefix tailTrace_1757136
  have hstable : (prefixWord ++ tailWord_1757136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757136).length < 2 ^ (prefixWord ++ tailWord_1757136).sum := by decide
  have hdescent : baseEnd_1757136 < baseStart_1757136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757142 : List Nat := [5, 2, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_1757142 : Nat := 118140960795 + 1757142 * 2 ^ 59
def prefixEnd_1757142 : Nat := 4983230072969 + 3 ^ 40 * 1757142 * 2
def baseEnd_1757142 : Nat := 601505616135112938362705

theorem tailTrace_1757142 : CollatzResearch.WordTrace tailWord_1757142 prefixEnd_1757142 601505616135112938362705 := by
  unfold tailWord_1757142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4005514612511381550428105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42725489200121403204566453 4005514612511381550428105)
  ·
    refine ⟨3004135959383536162821079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4005514612511381550428105 3004135959383536162821079)
    ·
      refine ⟨4506203939075304244231619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3004135959383536162821079 4506203939075304244231619)
      ·
        refine ⟨6759305908612956366347429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4506203939075304244231619 6759305908612956366347429)
        ·
          refine ⟨1267369857864929318690143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6759305908612956366347429 1267369857864929318690143)
          ·
            refine ⟨1901054786797393978035215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267369857864929318690143 1901054786797393978035215)
            ·
              refine ⟨2851582180196090967052823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1901054786797393978035215 2851582180196090967052823)
              ·
                refine ⟨4277373270294136450579235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2851582180196090967052823 4277373270294136450579235)
                ·
                  refine ⟨6416059905441204675868853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4277373270294136450579235 6416059905441204675868853)
                  ·
                    refine ⟨601505616135112938362705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6416059905441204675868853 601505616135112938362705)
                    ·
                      rfl

theorem cell22_1757142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_1757142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757142 prefixEnd_1757142 := by exact prefixLift 1757142
  have htrace : WordTrace (prefixWord ++ tailWord_1757142) baseStart_1757142 baseEnd_1757142 := by
    simpa [prefixWord, tailWord_1757142, baseEnd_1757142] using wordTrace_append hprefix tailTrace_1757142
  have hstable : (prefixWord ++ tailWord_1757142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757142).length < 2 ^ (prefixWord ++ tailWord_1757142).sum := by decide
  have hdescent : baseEnd_1757142 < baseStart_1757142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757164 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 1, 7]
def baseStart_1757164 : Nat := 118140960795 + 1757164 * 2 ^ 59
def prefixEnd_1757164 : Nat := 4983230072969 + 3 ^ 40 * 1757164 * 2
def baseEnd_1757164 : Nat := 601513147184712214312637

theorem tailTrace_1757164 : CollatzResearch.WordTrace tailWord_1757164 prefixEnd_1757164 601513147184712214312637 := by
  unfold tailWord_1757164
  simp only [CollatzResearch.WordTrace]
  refine ⟨32044518103051201282075273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42726024137401601709433697 32044518103051201282075273)
  ·
    refine ⟨24033388577288400961556455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32044518103051201282075273 24033388577288400961556455)
    ·
      refine ⟨36050082865932601442334683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24033388577288400961556455 36050082865932601442334683)
      ·
        refine ⟨54075124298898902163502025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36050082865932601442334683 54075124298898902163502025)
        ·
          refine ⟨40556343224174176622626519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54075124298898902163502025 40556343224174176622626519)
          ·
            refine ⟨60834514836261264933939779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40556343224174176622626519 60834514836261264933939779)
            ·
              refine ⟨91251772254391897400909669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60834514836261264933939779 91251772254391897400909669)
              ·
                refine ⟨17109707297698480762670563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91251772254391897400909669 17109707297698480762670563)
                ·
                  refine ⟨25664560946547721144005845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17109707297698480762670563 25664560946547721144005845)
                  ·
                    refine ⟨601513147184712214312637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25664560946547721144005845 601513147184712214312637)
                    ·
                      rfl

theorem cell22_1757164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_1757164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757164 prefixEnd_1757164 := by exact prefixLift 1757164
  have htrace : WordTrace (prefixWord ++ tailWord_1757164) baseStart_1757164 baseEnd_1757164 := by
    simpa [prefixWord, tailWord_1757164, baseEnd_1757164] using wordTrace_append hprefix tailTrace_1757164
  have hstable : (prefixWord ++ tailWord_1757164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757164).length < 2 ^ (prefixWord ++ tailWord_1757164).sum := by decide
  have hdescent : baseEnd_1757164 < baseStart_1757164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757166 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 7]
def baseStart_1757166 : Nat := 118140960795 + 1757166 * 2 ^ 59
def prefixEnd_1757166 : Nat := 4983230072969 + 3 ^ 40 * 1757166 * 2
def baseEnd_1757166 : Nat := 200504610608528291920877

theorem tailTrace_1757166 : CollatzResearch.WordTrace tailWord_1757166 prefixEnd_1757166 200504610608528291920877 := by
  unfold tailWord_1757166
  simp only [CollatzResearch.WordTrace]
  refine ⟨8011138644011894613215419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42726072768063437937148901 8011138644011894613215419)
  ·
    refine ⟨12016707966017841919823129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8011138644011894613215419 12016707966017841919823129)
    ·
      refine ⟨9012530974513381439867347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12016707966017841919823129 9012530974513381439867347)
      ·
        refine ⟨13518796461770072159801021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9012530974513381439867347 13518796461770072159801021)
        ·
          refine ⟨5069548673163777059925383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13518796461770072159801021 5069548673163777059925383)
          ·
            refine ⟨7604323009745665589888075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5069548673163777059925383 7604323009745665589888075)
            ·
              refine ⟨11406484514618498384832113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7604323009745665589888075 11406484514618498384832113)
              ·
                refine ⟨8554863385963873788624085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11406484514618498384832113 8554863385963873788624085)
                ·
                  refine ⟨200504610608528291920877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8554863385963873788624085 200504610608528291920877)
                  ·
                    rfl

theorem cell22_1757166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_1757166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757166 prefixEnd_1757166 := by exact prefixLift 1757166
  have htrace : WordTrace (prefixWord ++ tailWord_1757166) baseStart_1757166 baseEnd_1757166 := by
    simpa [prefixWord, tailWord_1757166, baseEnd_1757166] using wordTrace_append hprefix tailTrace_1757166
  have hstable : (prefixWord ++ tailWord_1757166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757166).length < 2 ^ (prefixWord ++ tailWord_1757166).sum := by decide
  have hdescent : baseEnd_1757166 < baseStart_1757166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757196 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 3, 4]
def baseStart_1757196 : Nat := 118140960795 + 1757196 * 2 ^ 59
def prefixEnd_1757196 : Nat := 4983230072969 + 3 ^ 40 * 1757196 * 2
def baseEnd_1757196 : Nat := 601524101438674797512539

theorem tailTrace_1757196 : CollatzResearch.WordTrace tailWord_1757196 prefixEnd_1757196 601524101438674797512539 := by
  unfold tailWord_1757196
  simp only [CollatzResearch.WordTrace]
  refine ⟨32045101670993236014657721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42726802227990981352876961 32045101670993236014657721)
  ·
    refine ⟨24033826253244927010993291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32045101670993236014657721 24033826253244927010993291)
    ·
      refine ⟨36050739379867390516489937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24033826253244927010993291 36050739379867390516489937)
      ·
        refine ⟨27038054534900542887367453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36050739379867390516489937 27038054534900542887367453)
        ·
          refine ⟨10139270450587703582762795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27038054534900542887367453 10139270450587703582762795)
          ·
            refine ⟨15208905675881555374144193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10139270450587703582762795 15208905675881555374144193)
            ·
              refine ⟨11406679256911166530608145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15208905675881555374144193 11406679256911166530608145)
              ·
                refine ⟨8555009442683374897956109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11406679256911166530608145 8555009442683374897956109)
                ·
                  refine ⟨3208128541006265586733541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8555009442683374897956109 3208128541006265586733541)
                  ·
                    refine ⟨601524101438674797512539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3208128541006265586733541 601524101438674797512539)
                    ·
                      rfl

theorem cell22_1757196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_1757196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757196 prefixEnd_1757196 := by exact prefixLift 1757196
  have htrace : WordTrace (prefixWord ++ tailWord_1757196) baseStart_1757196 baseEnd_1757196 := by
    simpa [prefixWord, tailWord_1757196, baseEnd_1757196] using wordTrace_append hprefix tailTrace_1757196
  have hstable : (prefixWord ++ tailWord_1757196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757196).length < 2 ^ (prefixWord ++ tailWord_1757196).sum := by decide
  have hdescent : baseEnd_1757196 < baseStart_1757196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757213 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 3, 4]
def baseStart_1757213 : Nat := 118140960795 + 1757213 * 2 ^ 59
def prefixEnd_1757213 : Nat := 4983230072969 + 3 ^ 40 * 1757213 * 2
def baseEnd_1757213 : Nat := 601529920886092419837487

theorem tailTrace_1757213 : CollatzResearch.WordTrace tailWord_1757213 prefixEnd_1757213 601529920886092419837487 := by
  unfold tailWord_1757213
  simp only [CollatzResearch.WordTrace]
  refine ⟨64090823382924883932684293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42727215588616589288456195 64090823382924883932684293)
  ·
    refine ⟨12017029384298415737378305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64090823382924883932684293 12017029384298415737378305)
    ·
      refine ⟨9012772038223811803033729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12017029384298415737378305 9012772038223811803033729)
      ·
        refine ⟨6759579028667858852275297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9012772038223811803033729 6759579028667858852275297)
        ·
          refine ⟨5069684271500894139206473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6759579028667858852275297 5069684271500894139206473)
          ·
            refine ⟨3802263203625670604404855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5069684271500894139206473 3802263203625670604404855)
            ·
              refine ⟨5703394805438505906607283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3802263203625670604404855 5703394805438505906607283)
              ·
                refine ⟨8555092208157758859910925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5703394805438505906607283 8555092208157758859910925)
                ·
                  refine ⟨3208159578059159572466597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8555092208157758859910925 3208159578059159572466597)
                  ·
                    refine ⟨601529920886092419837487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3208159578059159572466597 601529920886092419837487)
                    ·
                      rfl

theorem cell22_1757213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_1757213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757213 prefixEnd_1757213 := by exact prefixLift 1757213
  have htrace : WordTrace (prefixWord ++ tailWord_1757213) baseStart_1757213 baseEnd_1757213 := by
    simpa [prefixWord, tailWord_1757213, baseEnd_1757213] using wordTrace_append hprefix tailTrace_1757213
  have hstable : (prefixWord ++ tailWord_1757213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757213).length < 2 ^ (prefixWord ++ tailWord_1757213).sum := by decide
  have hdescent : baseEnd_1757213 < baseStart_1757213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757305 : List Nat := [1, 2, 1, 3, 4, 2, 2, 1, 3, 3]
def baseStart_1757305 : Nat := 118140960795 + 1757305 * 2 ^ 59
def prefixEnd_1757305 : Nat := 4983230072969 + 3 ^ 40 * 1757305 * 2
def baseEnd_1757305 : Nat := 601561414366234846537205

theorem tailTrace_1757305 : CollatzResearch.WordTrace tailWord_1757305 prefixEnd_1757305 601561414366234846537205 := by
  unfold tailWord_1757305
  simp only [CollatzResearch.WordTrace]
  refine ⟨64094178898591583645033369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42729452599061055763355579 64094178898591583645033369)
  ·
    refine ⟨48070634173943687733775027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64094178898591583645033369 48070634173943687733775027)
    ·
      refine ⟨72105951260915531600662541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48070634173943687733775027 72105951260915531600662541)
      ·
        refine ⟨27039731722843324350248453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72105951260915531600662541 27039731722843324350248453)
        ·
          refine ⟨5069949698033123315671585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27039731722843324350248453 5069949698033123315671585)
          ·
            refine ⟨3802462273524842486753689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5069949698033123315671585 3802462273524842486753689)
            ·
              refine ⟨2851846705143631865065267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3802462273524842486753689 2851846705143631865065267)
              ·
                refine ⟨4277770057715447797597901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2851846705143631865065267 4277770057715447797597901)
                ·
                  refine ⟨1604163771643292924099213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4277770057715447797597901 1604163771643292924099213)
                  ·
                    refine ⟨601561414366234846537205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1604163771643292924099213 601561414366234846537205)
                    ·
                      rfl

theorem cell22_1757305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 3].length) (baseStart_1757305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757305 prefixEnd_1757305 := by exact prefixLift 1757305
  have htrace : WordTrace (prefixWord ++ tailWord_1757305) baseStart_1757305 baseEnd_1757305 := by
    simpa [prefixWord, tailWord_1757305, baseEnd_1757305] using wordTrace_append hprefix tailTrace_1757305
  have hstable : (prefixWord ++ tailWord_1757305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757305).length < 2 ^ (prefixWord ++ tailWord_1757305).sum := by decide
  have hdescent : baseEnd_1757305 < baseStart_1757305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757391 : List Nat := [1, 1, 2, 1, 1, 3, 3, 10]
def baseStart_1757391 : Nat := 118140960795 + 1757391 * 2 ^ 59
def prefixEnd_1757391 : Nat := 4983230072969 + 3 ^ 40 * 1757391 * 2
def baseEnd_1757391 : Nat := 66843428213751032098549

theorem tailTrace_1757391 : CollatzResearch.WordTrace tailWord_1757391 prefixEnd_1757391 66843428213751032098549 := by
  unfold tailWord_1757391
  simp only [CollatzResearch.WordTrace]
  refine ⟨64097315576280020332664027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42731543717520013555109351 64097315576280020332664027)
  ·
    refine ⟨96145973364420030498996041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64097315576280020332664027 96145973364420030498996041)
    ·
      refine ⟨72109480023315022874247031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96145973364420030498996041 72109480023315022874247031)
      ·
        refine ⟨108164220034972534311370547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72109480023315022874247031 108164220034972534311370547)
        ·
          refine ⟨162246330052458801467055821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108164220034972534311370547 162246330052458801467055821)
          ·
            refine ⟨60842373769672050550145933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162246330052458801467055821 60842373769672050550145933)
            ·
              refine ⟨22815890163627018956304725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60842373769672050550145933 22815890163627018956304725)
              ·
                refine ⟨66843428213751032098549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22815890163627018956304725 66843428213751032098549)
                ·
                  rfl

theorem cell22_1757391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 10].length) (baseStart_1757391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757391 prefixEnd_1757391 := by exact prefixLift 1757391
  have htrace : WordTrace (prefixWord ++ tailWord_1757391) baseStart_1757391 baseEnd_1757391 := by
    simpa [prefixWord, tailWord_1757391, baseEnd_1757391] using wordTrace_append hprefix tailTrace_1757391
  have hstable : (prefixWord ++ tailWord_1757391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757391).length < 2 ^ (prefixWord ++ tailWord_1757391).sum := by decide
  have hdescent : baseEnd_1757391 < baseStart_1757391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757393 : List Nat := [1, 2, 2, 1, 2, 2, 3, 3, 2, 4]
def baseStart_1757393 : Nat := 118140960795 + 1757393 * 2 ^ 59
def prefixEnd_1757393 : Nat := 4983230072969 + 3 ^ 40 * 1757393 * 2
def baseEnd_1757393 : Nat := 601591538564631950336935

theorem tailTrace_1757393 : CollatzResearch.WordTrace tailWord_1757393 prefixEnd_1757393 601591538564631950336935 := by
  unfold tailWord_1757393
  simp only [CollatzResearch.WordTrace]
  refine ⟨64097388522272774674236833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42731592348181849782824555 64097388522272774674236833)
  ·
    refine ⟨48073041391704581005677625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64097388522272774674236833 48073041391704581005677625)
    ·
      refine ⟨36054781043778435754258219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48073041391704581005677625 36054781043778435754258219)
      ·
        refine ⟨54082171565667653631387329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36054781043778435754258219 54082171565667653631387329)
        ·
          refine ⟨40561628674250740223540497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54082171565667653631387329 40561628674250740223540497)
          ·
            refine ⟨30421221505688055167655373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40561628674250740223540497 30421221505688055167655373)
            ·
              refine ⟨11407958064633020687870765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30421221505688055167655373 11407958064633020687870765)
              ·
                refine ⟨4277984274237382757951537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11407958064633020687870765 4277984274237382757951537)
                ·
                  refine ⟨3208488205678037068463653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4277984274237382757951537 3208488205678037068463653)
                  ·
                    refine ⟨601591538564631950336935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3208488205678037068463653 601591538564631950336935)
                    ·
                      rfl

theorem cell22_1757393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_1757393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757393 prefixEnd_1757393 := by exact prefixLift 1757393
  have htrace : WordTrace (prefixWord ++ tailWord_1757393) baseStart_1757393 baseEnd_1757393 := by
    simpa [prefixWord, tailWord_1757393, baseEnd_1757393] using wordTrace_append hprefix tailTrace_1757393
  have hstable : (prefixWord ++ tailWord_1757393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757393).length < 2 ^ (prefixWord ++ tailWord_1757393).sum := by decide
  have hdescent : baseEnd_1757393 < baseStart_1757393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757442 : List Nat := [3, 4, 1, 1, 2, 2, 3, 6]
def baseStart_1757442 : Nat := 118140960795 + 1757442 * 2 ^ 59
def prefixEnd_1757442 : Nat := 4983230072969 + 3 ^ 40 * 1757442 * 2
def baseEnd_1757442 : Nat := 66845368029556906206865

theorem tailTrace_1757442 : CollatzResearch.WordTrace tailWord_1757442 prefixEnd_1757442 66845368029556906206865 := by
  unfold tailWord_1757442
  simp only [CollatzResearch.WordTrace]
  refine ⟨16024793924773814010692645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42732783799396837361847053 16024793924773814010692645)
  ·
    refine ⟨3004648860895090127004871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16024793924773814010692645 3004648860895090127004871)
    ·
      refine ⟨4506973291342635190507307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3004648860895090127004871 4506973291342635190507307)
      ·
        refine ⟨6760459937013952785760961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4506973291342635190507307 6760459937013952785760961)
        ·
          refine ⟨5070344952760464589320721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6760459937013952785760961 5070344952760464589320721)
          ·
            refine ⟨3802758714570348441990541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5070344952760464589320721 3802758714570348441990541)
            ·
              refine ⟨1426034517963880665746453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3802758714570348441990541 1426034517963880665746453)
              ·
                refine ⟨66845368029556906206865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1426034517963880665746453 66845368029556906206865)
                ·
                  rfl

theorem cell22_1757442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 6].length) (baseStart_1757442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757442 prefixEnd_1757442 := by exact prefixLift 1757442
  have htrace : WordTrace (prefixWord ++ tailWord_1757442) baseStart_1757442 baseEnd_1757442 := by
    simpa [prefixWord, tailWord_1757442, baseEnd_1757442] using wordTrace_append hprefix tailTrace_1757442
  have hstable : (prefixWord ++ tailWord_1757442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757442).length < 2 ^ (prefixWord ++ tailWord_1757442).sum := by decide
  have hdescent : baseEnd_1757442 < baseStart_1757442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757444 : List Nat := [2, 3, 2, 2, 4, 1, 1, 1, 2, 4]
def baseStart_1757444 : Nat := 118140960795 + 1757444 * 2 ^ 59
def prefixEnd_1757444 : Nat := 4983230072969 + 3 ^ 40 * 1757444 * 2
def baseEnd_1757444 : Nat := 601608996906884817311779

theorem tailTrace_1757444 : CollatzResearch.WordTrace tailWord_1757444 prefixEnd_1757444 601608996906884817311779 := by
  unfold tailWord_1757444
  simp only [CollatzResearch.WordTrace]
  refine ⟨32049624322544005192171693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42732832430058673589562257 32049624322544005192171693)
  ·
    refine ⟨12018609120954001947064385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32049624322544005192171693 12018609120954001947064385)
    ·
      refine ⟨9013956840715501460298289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12018609120954001947064385 9013956840715501460298289)
      ·
        refine ⟨6760467630536626095223717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9013956840715501460298289 6760467630536626095223717)
        ·
          refine ⟨1267587680725617392854447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6760467630536626095223717 1267587680725617392854447)
          ·
            refine ⟨1901381521088426089281671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267587680725617392854447 1901381521088426089281671)
            ·
              refine ⟨2852072281632639133922507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1901381521088426089281671 2852072281632639133922507)
              ·
                refine ⟨4278108422448958700883761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2852072281632639133922507 4278108422448958700883761)
                ·
                  refine ⟨3208581316836719025662821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4278108422448958700883761 3208581316836719025662821)
                  ·
                    refine ⟨601608996906884817311779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3208581316836719025662821 601608996906884817311779)
                    ·
                      rfl

theorem cell22_1757444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_1757444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757444 prefixEnd_1757444 := by exact prefixLift 1757444
  have htrace : WordTrace (prefixWord ++ tailWord_1757444) baseStart_1757444 baseEnd_1757444 := by
    simpa [prefixWord, tailWord_1757444, baseEnd_1757444] using wordTrace_append hprefix tailTrace_1757444
  have hstable : (prefixWord ++ tailWord_1757444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757444).length < 2 ^ (prefixWord ++ tailWord_1757444).sum := by decide
  have hdescent : baseEnd_1757444 < baseStart_1757444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757457 : List Nat := [1, 2, 2, 1, 1, 5, 1, 5, 1, 3]
def baseStart_1757457 : Nat := 118140960795 + 1757457 * 2 ^ 59
def prefixEnd_1757457 : Nat := 4983230072969 + 3 ^ 40 * 1757457 * 2
def baseEnd_1757457 : Nat := 601613447072557116736739

theorem tailTrace_1757457 : CollatzResearch.WordTrace tailWord_1757457 prefixEnd_1757457 601613447072557116736739 := by
  unfold tailWord_1757457
  simp only [CollatzResearch.WordTrace]
  refine ⟨64099722794040913604566625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42733148529360609069711083 64099722794040913604566625)
  ·
    refine ⟨48074792095530685203424969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64099722794040913604566625 48074792095530685203424969)
    ·
      refine ⟨36056094071648013902568727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48074792095530685203424969 36056094071648013902568727)
      ·
        refine ⟨54084141107472020853853091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36056094071648013902568727 54084141107472020853853091)
        ·
          refine ⟨81126211661208031280779637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54084141107472020853853091 81126211661208031280779637)
          ·
            refine ⟨7605582343238252932573091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81126211661208031280779637 7605582343238252932573091)
            ·
              refine ⟨11408373514857379398859637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7605582343238252932573091 11408373514857379398859637)
              ·
                refine ⟨1069535017017879318643091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11408373514857379398859637 1069535017017879318643091)
                ·
                  refine ⟨1604302525526818977964637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1069535017017879318643091 1604302525526818977964637)
                  ·
                    refine ⟨601613447072557116736739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1604302525526818977964637 601613447072557116736739)
                    ·
                      rfl

theorem cell22_1757457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 1, 3].length) (baseStart_1757457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757457 prefixEnd_1757457 := by exact prefixLift 1757457
  have htrace : WordTrace (prefixWord ++ tailWord_1757457) baseStart_1757457 baseEnd_1757457 := by
    simpa [prefixWord, tailWord_1757457, baseEnd_1757457] using wordTrace_append hprefix tailTrace_1757457
  have hstable : (prefixWord ++ tailWord_1757457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757457).length < 2 ^ (prefixWord ++ tailWord_1757457).sum := by decide
  have hdescent : baseEnd_1757457 < baseStart_1757457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757474 : List Nat := [3, 3, 1, 1, 3, 1, 2, 4, 1, 3]
def baseStart_1757474 : Nat := 118140960795 + 1757474 * 2 ^ 59
def prefixEnd_1757474 : Nat := 4983230072969 + 3 ^ 40 * 1757474 * 2
def baseEnd_1757474 : Nat := 601619266519974739061687

theorem tailTrace_1757474 : CollatzResearch.WordTrace tailWord_1757474 prefixEnd_1757474 601619266519974739061687 := by
  unfold tailWord_1757474
  simp only [CollatzResearch.WordTrace]
  refine ⟨16025085708744831376983869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42733561889986217005290317 16025085708744831376983869)
  ·
    refine ⟨6009407140779311766368951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16025085708744831376983869 6009407140779311766368951)
    ·
      refine ⟨9014110711168967649553427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6009407140779311766368951 9014110711168967649553427)
      ·
        refine ⟨13521166066753451474330141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9014110711168967649553427 13521166066753451474330141)
        ·
          refine ⟨5070437275032544302873803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13521166066753451474330141 5070437275032544302873803)
          ·
            refine ⟨7605655912548816454310705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5070437275032544302873803 7605655912548816454310705)
            ·
              refine ⟨5704241934411612340733029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7605655912548816454310705 5704241934411612340733029)
              ·
                refine ⟨1069545362702177313887443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5704241934411612340733029 1069545362702177313887443)
                ·
                  refine ⟨1604318044053265970831165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1069545362702177313887443 1604318044053265970831165)
                  ·
                    refine ⟨601619266519974739061687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1604318044053265970831165 601619266519974739061687)
                    ·
                      rfl

theorem cell22_1757474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_1757474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757474 prefixEnd_1757474 := by exact prefixLift 1757474
  have htrace : WordTrace (prefixWord ++ tailWord_1757474) baseStart_1757474 baseEnd_1757474 := by
    simpa [prefixWord, tailWord_1757474, baseEnd_1757474] using wordTrace_append hprefix tailTrace_1757474
  have hstable : (prefixWord ++ tailWord_1757474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757474).length < 2 ^ (prefixWord ++ tailWord_1757474).sum := by decide
  have hdescent : baseEnd_1757474 < baseStart_1757474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757508 : List Nat := [2, 3, 4, 1, 2, 2, 1, 3, 1, 3]
def baseStart_1757508 : Nat := 118140960795 + 1757508 * 2 ^ 59
def prefixEnd_1757508 : Nat := 4983230072969 + 3 ^ 40 * 1757508 * 2
def baseEnd_1757508 : Nat := 601630905414809983711583

theorem tailTrace_1757508 : CollatzResearch.WordTrace tailWord_1757508 prefixEnd_1757508 601630905414809983711583 := by
  unfold tailWord_1757508
  simp only [CollatzResearch.WordTrace]
  refine ⟨32050791458428074657336589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42734388611237432876448785 32050791458428074657336589)
  ·
    refine ⟨12019046796910527996501221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32050791458428074657336589 12019046796910527996501221)
    ·
      refine ⟨2253571274420723999343979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12019046796910527996501221 2253571274420723999343979)
      ·
        refine ⟨3380356911631085999015969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2253571274420723999343979 3380356911631085999015969)
        ·
          refine ⟨2535267683723314499261977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3380356911631085999015969 2535267683723314499261977)
          ·
            refine ⟨1901450762792485874446483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2535267683723314499261977 1901450762792485874446483)
            ·
              refine ⟨2852176144188728811669725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1901450762792485874446483 2852176144188728811669725)
              ·
                refine ⟨1069566054070773304376147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2852176144188728811669725 1069566054070773304376147)
                ·
                  refine ⟨1604349081106159956564221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1069566054070773304376147 1604349081106159956564221)
                  ·
                    refine ⟨601630905414809983711583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1604349081106159956564221 601630905414809983711583)
                    ·
                      rfl

theorem cell22_1757508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_1757508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757508 prefixEnd_1757508 := by exact prefixLift 1757508
  have htrace : WordTrace (prefixWord ++ tailWord_1757508) baseStart_1757508 baseEnd_1757508 := by
    simpa [prefixWord, tailWord_1757508, baseEnd_1757508] using wordTrace_append hprefix tailTrace_1757508
  have hstable : (prefixWord ++ tailWord_1757508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757508).length < 2 ^ (prefixWord ++ tailWord_1757508).sum := by decide
  have hdescent : baseEnd_1757508 < baseStart_1757508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757513 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 3, 5]
def baseStart_1757513 : Nat := 118140960795 + 1757513 * 2 ^ 59
def prefixEnd_1757513 : Nat := 4983230072969 + 3 ^ 40 * 1757513 * 2
def baseEnd_1757513 : Nat := 601632617016991637336567

theorem tailTrace_1757513 : CollatzResearch.WordTrace tailWord_1757513 prefixEnd_1757513 601632617016991637336567 := by
  unfold tailWord_1757513
  simp only [CollatzResearch.WordTrace]
  refine ⟨64101765281838035168605193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42734510187892023445736795 64101765281838035168605193)
  ·
    refine ⟨48076323961378526376453895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64101765281838035168605193 48076323961378526376453895)
    ·
      refine ⟨72114485942067789564680843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48076323961378526376453895 72114485942067789564680843)
      ·
        refine ⟨108171728913101684347021265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72114485942067789564680843 108171728913101684347021265)
        ·
          refine ⟨81128796684826263260265949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108171728913101684347021265 81128796684826263260265949)
          ·
            refine ⟨30423298756809848722599731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81128796684826263260265949 30423298756809848722599731)
            ·
              refine ⟨45634948135214773083899597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30423298756809848722599731 45634948135214773083899597)
              ·
                refine ⟨17113105550705539906462349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45634948135214773083899597 17113105550705539906462349)
                ·
                  refine ⟨6417414581514577464923381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17113105550705539906462349 6417414581514577464923381)
                  ·
                    refine ⟨601632617016991637336567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6417414581514577464923381 601632617016991637336567)
                    ·
                      rfl

theorem cell22_1757513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_1757513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757513 prefixEnd_1757513 := by exact prefixLift 1757513
  have htrace : WordTrace (prefixWord ++ tailWord_1757513) baseStart_1757513 baseEnd_1757513 := by
    simpa [prefixWord, tailWord_1757513, baseEnd_1757513] using wordTrace_append hprefix tailTrace_1757513
  have hstable : (prefixWord ++ tailWord_1757513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757513).length < 2 ^ (prefixWord ++ tailWord_1757513).sum := by decide
  have hdescent : baseEnd_1757513 < baseStart_1757513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757515 : List Nat := [1, 1, 1, 1, 3, 1, 1, 9, 4]
def baseStart_1757515 : Nat := 118140960795 + 1757515 * 2 ^ 59
def prefixEnd_1757515 : Nat := 4983230072969 + 3 ^ 40 * 1757515 * 2
def baseEnd_1757515 : Nat := 200544433885954766262187

theorem tailTrace_1757515 : CollatzResearch.WordTrace tailWord_1757515 prefixEnd_1757515 200544433885954766262187 := by
  unfold tailWord_1757515
  simp only [CollatzResearch.WordTrace]
  refine ⟨64101838227830789510177999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42734558818553859673451999 64101838227830789510177999)
  ·
    refine ⟨96152757341746184265266999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64101838227830789510177999 96152757341746184265266999)
    ·
      refine ⟨144229136012619276397900499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96152757341746184265266999 144229136012619276397900499)
      ·
        refine ⟨216343704018928914596850749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144229136012619276397900499 216343704018928914596850749)
        ·
          refine ⟨81128889007098342973819031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216343704018928914596850749 81128889007098342973819031)
          ·
            refine ⟨121693333510647514460728547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81128889007098342973819031 121693333510647514460728547)
            ·
              refine ⟨182540000265971271691092821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121693333510647514460728547 182540000265971271691092821)
              ·
                refine ⟨1069570314058425420064997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 182540000265971271691092821 1069570314058425420064997)
                ·
                  refine ⟨200544433885954766262187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1069570314058425420064997 200544433885954766262187)
                  ·
                    rfl

theorem cell22_1757515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 4].length) (baseStart_1757515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757515 prefixEnd_1757515 := by exact prefixLift 1757515
  have htrace : WordTrace (prefixWord ++ tailWord_1757515) baseStart_1757515 baseEnd_1757515 := by
    simpa [prefixWord, tailWord_1757515, baseEnd_1757515] using wordTrace_append hprefix tailTrace_1757515
  have hstable : (prefixWord ++ tailWord_1757515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757515).length < 2 ^ (prefixWord ++ tailWord_1757515).sum := by decide
  have hdescent : baseEnd_1757515 < baseStart_1757515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757528 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 3, 6]
def baseStart_1757528 : Nat := 118140960795 + 1757528 * 2 ^ 59
def prefixEnd_1757528 : Nat := 4983230072969 + 3 ^ 40 * 1757528 * 2
def baseEnd_1757528 : Nat := 601637751823536598211521

theorem tailTrace_1757528 : CollatzResearch.WordTrace tailWord_1757528 prefixEnd_1757528 601637751823536598211521 := by
  unfold tailWord_1757528
  simp only [CollatzResearch.WordTrace]
  refine ⟨32051156188391846365200619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42734874917855795153600825 32051156188391846365200619)
  ·
    refine ⟨48076734282587769547800929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32051156188391846365200619 48076734282587769547800929)
    ·
      refine ⟨36057550711940827160850697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48076734282587769547800929 36057550711940827160850697)
      ·
        refine ⟨27043163033955620370638023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36057550711940827160850697 27043163033955620370638023)
        ·
          refine ⟨40564744550933430555957035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27043163033955620370638023 40564744550933430555957035)
          ·
            refine ⟨60847116826400145833935553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40564744550933430555957035 60847116826400145833935553)
            ·
              refine ⟨45635337619800109375451665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60847116826400145833935553 45635337619800109375451665)
              ·
                refine ⟨34226503214850082031588749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45635337619800109375451665 34226503214850082031588749)
                ·
                  refine ⟨12834938705568780761845781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34226503214850082031588749 12834938705568780761845781)
                  ·
                    refine ⟨601637751823536598211521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12834938705568780761845781 601637751823536598211521)
                    ·
                      rfl

theorem cell22_1757528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_1757528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757528 prefixEnd_1757528 := by exact prefixLift 1757528
  have htrace : WordTrace (prefixWord ++ tailWord_1757528) baseStart_1757528 baseEnd_1757528 := by
    simpa [prefixWord, tailWord_1757528, baseEnd_1757528] using wordTrace_append hprefix tailTrace_1757528
  have hstable : (prefixWord ++ tailWord_1757528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757528).length < 2 ^ (prefixWord ++ tailWord_1757528).sum := by decide
  have hdescent : baseEnd_1757528 < baseStart_1757528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757605 : List Nat := [1, 3, 1, 2, 1, 1, 3, 5, 5]
def baseStart_1757605 : Nat := 118140960795 + 1757605 * 2 ^ 59
def prefixEnd_1757605 : Nat := 4983230072969 + 3 ^ 40 * 1757605 * 2
def baseEnd_1757605 : Nat := 200554703499044688012095

theorem tailTrace_1757605 : CollatzResearch.WordTrace tailWord_1757605 prefixEnd_1757605 200554703499044688012095 := by
  unfold tailWord_1757605
  simp only [CollatzResearch.WordTrace]
  refine ⟨64105120797504734880954269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42736747198336489920636179 64105120797504734880954269)
  ·
    refine ⟨24039420299064275580357851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64105120797504734880954269 24039420299064275580357851)
    ·
      refine ⟨36059130448596413370536777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24039420299064275580357851 36059130448596413370536777)
      ·
        refine ⟨27044347836447310027902583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36059130448596413370536777 27044347836447310027902583)
        ·
          refine ⟨40566521754670965041853875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27044347836447310027902583 40566521754670965041853875)
          ·
            refine ⟨60849782632006447562780813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40566521754670965041853875 60849782632006447562780813)
            ·
              refine ⟨22818668487002417836042805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60849782632006447562780813 22818668487002417836042805)
              ·
                refine ⟨2139250170656476672129013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22818668487002417836042805 2139250170656476672129013)
                ·
                  refine ⟨200554703499044688012095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2139250170656476672129013 200554703499044688012095)
                  ·
                    rfl

theorem cell22_1757605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_1757605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757605 prefixEnd_1757605 := by exact prefixLift 1757605
  have htrace : WordTrace (prefixWord ++ tailWord_1757605) baseStart_1757605 baseEnd_1757605 := by
    simpa [prefixWord, tailWord_1757605, baseEnd_1757605] using wordTrace_append hprefix tailTrace_1757605
  have hstable : (prefixWord ++ tailWord_1757605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757605).length < 2 ^ (prefixWord ++ tailWord_1757605).sum := by decide
  have hdescent : baseEnd_1757605 < baseStart_1757605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757680 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 1, 6]
def baseStart_1757680 : Nat := 118140960795 + 1757680 * 2 ^ 59
def prefixEnd_1757680 : Nat := 4983230072969 + 3 ^ 40 * 1757680 * 2
def baseEnd_1757680 : Nat := 601689784529858868411055

theorem tailTrace_1757680 : CollatzResearch.WordTrace tailWord_1757680 prefixEnd_1757680 601689784529858868411055 := by
  unfold tailWord_1757680
  simp only [CollatzResearch.WordTrace]
  refine ⟨32053928136116511344967247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42738570848155348459956329 32053928136116511344967247)
  ·
    refine ⟨48080892204174767017450871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32053928136116511344967247 48080892204174767017450871)
    ·
      refine ⟨72121338306262150526176307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48080892204174767017450871 72121338306262150526176307)
      ·
        refine ⟨108182007459393225789264461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72121338306262150526176307 108182007459393225789264461)
        ·
          refine ⟨40568252797272459670974173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108182007459393225789264461 40568252797272459670974173)
          ·
            refine ⟨15213094798977172376615315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40568252797272459670974173 15213094798977172376615315)
            ·
              refine ⟨22819642198465758564922973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15213094798977172376615315 22819642198465758564922973)
              ·
                refine ⟨8557365824424659461846115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22819642198465758564922973 8557365824424659461846115)
                ·
                  refine ⟨12836048736636989192769173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8557365824424659461846115 12836048736636989192769173)
                  ·
                    refine ⟨601689784529858868411055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12836048736636989192769173 601689784529858868411055)
                    ·
                      rfl

theorem cell22_1757680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_1757680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757680 prefixEnd_1757680 := by exact prefixLift 1757680
  have htrace : WordTrace (prefixWord ++ tailWord_1757680) baseStart_1757680 baseEnd_1757680 := by
    simpa [prefixWord, tailWord_1757680, baseEnd_1757680] using wordTrace_append hprefix tailTrace_1757680
  have hstable : (prefixWord ++ tailWord_1757680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757680).length < 2 ^ (prefixWord ++ tailWord_1757680).sum := by decide
  have hdescent : baseEnd_1757680 < baseStart_1757680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757697 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 4, 4]
def baseStart_1757697 : Nat := 118140960795 + 1757697 * 2 ^ 59
def prefixEnd_1757697 : Nat := 4983230072969 + 3 ^ 40 * 1757697 * 2
def baseEnd_1757697 : Nat := 601695603977276490736003

theorem tailTrace_1757697 : CollatzResearch.WordTrace tailWord_1757697 prefixEnd_1757697 601695603977276490736003 := by
  unfold tailWord_1757697
  simp only [CollatzResearch.WordTrace]
  refine ⟨64108476313171434593303345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42738984208780956395535563 64108476313171434593303345)
  ·
    refine ⟨48081357234878575944977509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64108476313171434593303345 48081357234878575944977509)
    ·
      refine ⟨9015254481539732989683283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48081357234878575944977509 9015254481539732989683283)
      ·
        refine ⟨13522881722309599484524925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9015254481539732989683283 13522881722309599484524925)
        ·
          refine ⟨5071080645866099806696847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13522881722309599484524925 5071080645866099806696847)
          ·
            refine ⟨7606620968799149710045271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5071080645866099806696847 7606620968799149710045271)
            ·
              refine ⟨11409931453198724565067907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7606620968799149710045271 11409931453198724565067907)
              ·
                refine ⟨17114897179798086847601861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11409931453198724565067907 17114897179798086847601861)
                ·
                  refine ⟨3209043221212141283925349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17114897179798086847601861 3209043221212141283925349)
                  ·
                    refine ⟨601695603977276490736003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3209043221212141283925349 601695603977276490736003)
                    ·
                      rfl

theorem cell22_1757697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_1757697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757697 prefixEnd_1757697 := by exact prefixLift 1757697
  have htrace : WordTrace (prefixWord ++ tailWord_1757697) baseStart_1757697 baseEnd_1757697 := by
    simpa [prefixWord, tailWord_1757697, baseEnd_1757697] using wordTrace_append hprefix tailTrace_1757697
  have hstable : (prefixWord ++ tailWord_1757697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757697).length < 2 ^ (prefixWord ++ tailWord_1757697).sum := by decide
  have hdescent : baseEnd_1757697 < baseStart_1757697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757727 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 5, 3]
def baseStart_1757727 : Nat := 118140960795 + 1757727 * 2 ^ 59
def prefixEnd_1757727 : Nat := 4983230072969 + 3 ^ 40 * 1757727 * 2
def baseEnd_1757727 : Nat := 601705873590366412485911

theorem tailTrace_1757727 : CollatzResearch.WordTrace tailWord_1757727 prefixEnd_1757727 601705873590366412485911 := by
  unfold tailWord_1757727
  simp only [CollatzResearch.WordTrace]
  refine ⟨64109570503062749716895435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42739713668708499811263623 64109570503062749716895435)
  ·
    refine ⟨96164355754594124575343153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64109570503062749716895435 96164355754594124575343153)
    ·
      refine ⟨72123266815945593431507365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96164355754594124575343153 72123266815945593431507365)
      ·
        refine ⟨13523112527989798768407631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72123266815945593431507365 13523112527989798768407631)
        ·
          refine ⟨20284668791984698152611447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13523112527989798768407631 20284668791984698152611447)
          ·
            refine ⟨30427003187977047228917171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20284668791984698152611447 30427003187977047228917171)
            ·
              refine ⟨45640504781965570843375757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30427003187977047228917171 45640504781965570843375757)
              ·
                refine ⟨17115189293237089066265909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45640504781965570843375757 17115189293237089066265909)
                ·
                  refine ⟨1604548996240977099962429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17115189293237089066265909 1604548996240977099962429)
                  ·
                    refine ⟨601705873590366412485911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1604548996240977099962429 601705873590366412485911)
                    ·
                      rfl

theorem cell22_1757727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 3].length) (baseStart_1757727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757727 prefixEnd_1757727 := by exact prefixLift 1757727
  have htrace : WordTrace (prefixWord ++ tailWord_1757727) baseStart_1757727 baseEnd_1757727 := by
    simpa [prefixWord, tailWord_1757727, baseEnd_1757727] using wordTrace_append hprefix tailTrace_1757727
  have hstable : (prefixWord ++ tailWord_1757727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757727).length < 2 ^ (prefixWord ++ tailWord_1757727).sum := by decide
  have hdescent : baseEnd_1757727 < baseStart_1757727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757740 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 9]
def baseStart_1757740 : Nat := 118140960795 + 1757740 * 2 ^ 59
def prefixEnd_1757740 : Nat := 4983230072969 + 3 ^ 40 * 1757740 * 2
def baseEnd_1757740 : Nat := 200570107918679570636957

theorem tailTrace_1757740 : CollatzResearch.WordTrace tailWord_1757740 prefixEnd_1757740 200570107918679570636957 := by
  unfold tailWord_1757740
  simp only [CollatzResearch.WordTrace]
  refine ⟨32055022326007826468559337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42740029768010435291412449 32055022326007826468559337)
  ·
    refine ⟨24041266744505869851419503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32055022326007826468559337 24041266744505869851419503)
    ·
      refine ⟨36061900116758804777129255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24041266744505869851419503 36061900116758804777129255)
      ·
        refine ⟨54092850175138207165693883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36061900116758804777129255 54092850175138207165693883)
        ·
          refine ⟨81139275262707310748540825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54092850175138207165693883 81139275262707310748540825)
          ·
            refine ⟨60854456447030483061405619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81139275262707310748540825 60854456447030483061405619)
            ·
              refine ⟨91281684670545724592108429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60854456447030483061405619 91281684670545724592108429)
              ·
                refine ⟨34230631751454646722040661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91281684670545724592108429 34230631751454646722040661)
                ·
                  refine ⟨200570107918679570636957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34230631751454646722040661 200570107918679570636957)
                  ·
                    rfl

theorem cell22_1757740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_1757740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757740 prefixEnd_1757740 := by exact prefixLift 1757740
  have htrace : WordTrace (prefixWord ++ tailWord_1757740) baseStart_1757740 baseEnd_1757740 := by
    simpa [prefixWord, tailWord_1757740, baseEnd_1757740] using wordTrace_append hprefix tailTrace_1757740
  have hstable : (prefixWord ++ tailWord_1757740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757740).length < 2 ^ (prefixWord ++ tailWord_1757740).sum := by decide
  have hdescent : baseEnd_1757740 < baseStart_1757740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757772 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 2, 5]
def baseStart_1757772 : Nat := 118140960795 + 1757772 * 2 ^ 59
def prefixEnd_1757772 : Nat := 4983230072969 + 3 ^ 40 * 1757772 * 2
def baseEnd_1757772 : Nat := 601721278010001295110773

theorem tailTrace_1757772 : CollatzResearch.WordTrace tailWord_1757772 prefixEnd_1757772 601721278010001295110773 := by
  unfold tailWord_1757772
  simp only [CollatzResearch.WordTrace]
  refine ⟨32055605893949861201141785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42740807858599814934855713 32055605893949861201141785)
  ·
    refine ⟨24041704420462395900856339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32055605893949861201141785 24041704420462395900856339)
    ·
      refine ⟨36062556630693593851284509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24041704420462395900856339 36062556630693593851284509)
      ·
        refine ⟨13523458736510097694231691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36062556630693593851284509 13523458736510097694231691)
        ·
          refine ⟨20285188104765146541347537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13523458736510097694231691 20285188104765146541347537)
          ·
            refine ⟨15213891078573859906010653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20285188104765146541347537 15213891078573859906010653)
            ·
              refine ⟨5705209154465197464753995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15213891078573859906010653 5705209154465197464753995)
              ·
                refine ⟨8557813731697796197130993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5705209154465197464753995 8557813731697796197130993)
                ·
                  refine ⟨6418360298773347147848245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8557813731697796197130993 6418360298773347147848245)
                  ·
                    refine ⟨601721278010001295110773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6418360298773347147848245 601721278010001295110773)
                    ·
                      rfl

theorem cell22_1757772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_1757772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757772 prefixEnd_1757772 := by exact prefixLift 1757772
  have htrace : WordTrace (prefixWord ++ tailWord_1757772) baseStart_1757772 baseEnd_1757772 := by
    simpa [prefixWord, tailWord_1757772, baseEnd_1757772] using wordTrace_append hprefix tailTrace_1757772
  have hstable : (prefixWord ++ tailWord_1757772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757772).length < 2 ^ (prefixWord ++ tailWord_1757772).sum := by decide
  have hdescent : baseEnd_1757772 < baseStart_1757772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757802 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 8]
def baseStart_1757802 : Nat := 118140960795 + 1757802 * 2 ^ 59
def prefixEnd_1757802 : Nat := 4983230072969 + 3 ^ 40 * 1757802 * 2
def baseEnd_1757802 : Nat := 200577182541030405620227

theorem tailTrace_1757802 : CollatzResearch.WordTrace tailWord_1757802 prefixEnd_1757802 200577182541030405620227 := by
  unfold tailWord_1757802
  simp only [CollatzResearch.WordTrace]
  refine ⟨16028076494447759381468915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42741537318527358350583773 16028076494447759381468915)
  ·
    refine ⟨24042114741671639072203373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16028076494447759381468915 24042114741671639072203373)
    ·
      refine ⟨9015793028126864652076265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24042114741671639072203373 9015793028126864652076265)
      ·
        refine ⟨6761844771095148489057199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9015793028126864652076265 6761844771095148489057199)
        ·
          refine ⟨10142767156642722733585799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6761844771095148489057199 10142767156642722733585799)
          ·
            refine ⟨15214150734964084100378699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10142767156642722733585799 15214150734964084100378699)
            ·
              refine ⟨22821226102446126150568049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15214150734964084100378699 22821226102446126150568049)
              ·
                refine ⟨17115919576834594612926037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22821226102446126150568049 17115919576834594612926037)
                ·
                  refine ⟨200577182541030405620227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17115919576834594612926037 200577182541030405620227)
                  ·
                    rfl

theorem cell22_1757802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_1757802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757802 prefixEnd_1757802 := by exact prefixLift 1757802
  have htrace : WordTrace (prefixWord ++ tailWord_1757802) baseStart_1757802 baseEnd_1757802 := by
    simpa [prefixWord, tailWord_1757802, baseEnd_1757802] using wordTrace_append hprefix tailTrace_1757802
  have hstable : (prefixWord ++ tailWord_1757802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757802).length < 2 ^ (prefixWord ++ tailWord_1757802).sum := by decide
  have hdescent : baseEnd_1757802 < baseStart_1757802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757847 : List Nat := [1, 1, 3, 3, 2, 1, 3, 8]
def baseStart_1757847 : Nat := 118140960795 + 1757847 * 2 ^ 59
def prefixEnd_1757847 : Nat := 4983230072969 + 3 ^ 40 * 1757847 * 2
def baseEnd_1757847 : Nat := 66860772449191788831727

theorem tailTrace_1757847 : CollatzResearch.WordTrace tailWord_1757847 prefixEnd_1757847 66860772449191788831727 := by
  unfold tailWord_1757847
  simp only [CollatzResearch.WordTrace]
  refine ⟨64113947262628010211263795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42742631508418673474175863 64113947262628010211263795)
  ·
    refine ⟨96170920893942015316895693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64113947262628010211263795 96170920893942015316895693)
    ·
      refine ⟨36064095335228255743835885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96170920893942015316895693 36064095335228255743835885)
      ·
        refine ⟨13524035750710595903938457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36064095335228255743835885 13524035750710595903938457)
        ·
          refine ⟨10143026813032946927953843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13524035750710595903938457 10143026813032946927953843)
          ·
            refine ⟨15214540219549420391930765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10143026813032946927953843 15214540219549420391930765)
            ·
              refine ⟨5705452582331032646974037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15214540219549420391930765 5705452582331032646974037)
              ·
                refine ⟨66860772449191788831727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5705452582331032646974037 66860772449191788831727)
                ·
                  rfl

theorem cell22_1757847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 8].length) (baseStart_1757847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757847 prefixEnd_1757847 := by exact prefixLift 1757847
  have htrace : WordTrace (prefixWord ++ tailWord_1757847) baseStart_1757847 baseEnd_1757847 := by
    simpa [prefixWord, tailWord_1757847, baseEnd_1757847] using wordTrace_append hprefix tailTrace_1757847
  have hstable : (prefixWord ++ tailWord_1757847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757847).length < 2 ^ (prefixWord ++ tailWord_1757847).sum := by decide
  have hdescent : baseEnd_1757847 < baseStart_1757847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757870 : List Nat := [4, 1, 4, 1, 1, 2, 3, 2, 4]
def baseStart_1757870 : Nat := 118140960795 + 1757870 * 2 ^ 59
def prefixEnd_1757870 : Nat := 4983230072969 + 3 ^ 40 * 1757870 * 2
def baseEnd_1757870 : Nat := 200584941804253902053491

theorem tailTrace_1757870 : CollatzResearch.WordTrace tailWord_1757870 prefixEnd_1757870 200584941804253902053491 := by
  unfold tailWord_1757870
  simp only [CollatzResearch.WordTrace]
  refine ⟨8014348267693085642418883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42743190761029790092900709 8014348267693085642418883)
  ·
    refine ⟨12021522401539628463628325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8014348267693085642418883 12021522401539628463628325)
    ·
      refine ⟨2254035450288680336930311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12021522401539628463628325 2254035450288680336930311)
      ·
        refine ⟨3381053175433020505395467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2254035450288680336930311 3381053175433020505395467)
        ·
          refine ⟨5071579763149530758093201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3381053175433020505395467 5071579763149530758093201)
          ·
            refine ⟨3803684822362148068569901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5071579763149530758093201 3803684822362148068569901)
            ·
              refine ⟨1426381808385805525713713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3803684822362148068569901 1426381808385805525713713)
              ·
                refine ⟨1069786356289354144285285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1426381808385805525713713 1069786356289354144285285)
                ·
                  refine ⟨200584941804253902053491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1069786356289354144285285 200584941804253902053491)
                  ·
                    rfl

theorem cell22_1757870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_1757870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757870 prefixEnd_1757870 := by exact prefixLift 1757870
  have htrace : WordTrace (prefixWord ++ tailWord_1757870) baseStart_1757870 baseEnd_1757870 := by
    simpa [prefixWord, tailWord_1757870, baseEnd_1757870] using wordTrace_append hprefix tailTrace_1757870
  have hstable : (prefixWord ++ tailWord_1757870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757870).length < 2 ^ (prefixWord ++ tailWord_1757870).sum := by decide
  have hdescent : baseEnd_1757870 < baseStart_1757870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757956 : List Nat := [2, 3, 2, 2, 1, 1, 2, 4, 1, 4]
def baseStart_1757956 : Nat := 118140960795 + 1757956 * 2 ^ 59
def prefixEnd_1757956 : Nat := 4983230072969 + 3 ^ 40 * 1757956 * 2
def baseEnd_1757956 : Nat := 601784264970286148510209

theorem tailTrace_1757956 : CollatzResearch.WordTrace tailWord_1757956 prefixEnd_1757956 601784264970286148510209 := by
  unfold tailWord_1757956
  simp only [CollatzResearch.WordTrace]
  refine ⟨32058961409616560913490861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42745281879488747884654481 32058961409616560913490861)
  ·
    refine ⟨12022110528606210342559073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32058961409616560913490861 12022110528606210342559073)
    ·
      refine ⟨9016582896454657756919305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12022110528606210342559073 9016582896454657756919305)
      ·
        refine ⟨6762437172340993317689479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9016582896454657756919305 6762437172340993317689479)
        ·
          refine ⟨10143655758511489976534219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6762437172340993317689479 10143655758511489976534219)
          ·
            refine ⟨15215483637767234964801329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10143655758511489976534219 15215483637767234964801329)
            ·
              refine ⟨11411612728325426223600997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15215483637767234964801329 11411612728325426223600997)
              ·
                refine ⟨2139677386561017416925187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11411612728325426223600997 2139677386561017416925187)
                ·
                  refine ⟨3209516079841526125387781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2139677386561017416925187 3209516079841526125387781)
                  ·
                    refine ⟨601784264970286148510209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3209516079841526125387781 601784264970286148510209)
                    ·
                      rfl

theorem cell22_1757956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_1757956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757956 prefixEnd_1757956 := by exact prefixLift 1757956
  have htrace : WordTrace (prefixWord ++ tailWord_1757956) baseStart_1757956 baseEnd_1757956 := by
    simpa [prefixWord, tailWord_1757956, baseEnd_1757956] using wordTrace_append hprefix tailTrace_1757956
  have hstable : (prefixWord ++ tailWord_1757956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757956).length < 2 ^ (prefixWord ++ tailWord_1757956).sum := by decide
  have hdescent : baseEnd_1757956 < baseStart_1757956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757969 : List Nat := [1, 2, 2, 1, 1, 3, 4, 2, 1, 5]
def baseStart_1757969 : Nat := 118140960795 + 1757969 * 2 ^ 59
def prefixEnd_1757969 : Nat := 4983230072969 + 3 ^ 40 * 1757969 * 2
def baseEnd_1757969 : Nat := 601788715135958447935169

theorem tailTrace_1757969 : CollatzResearch.WordTrace tailWord_1757969 prefixEnd_1757969 601788715135958447935169 := by
  unfold tailWord_1757969
  simp only [CollatzResearch.WordTrace]
  refine ⟨64118396968186025047204961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42745597978790683364803307 64118396968186025047204961)
  ·
    refine ⟨48088797726139518785403721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64118396968186025047204961 48088797726139518785403721)
    ·
      refine ⟨36066598294604639089052791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48088797726139518785403721 36066598294604639089052791)
      ·
        refine ⟨54099897441906958633579187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36066598294604639089052791 54099897441906958633579187)
        ·
          refine ⟨81149846162860437950368781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54099897441906958633579187 81149846162860437950368781)
          ·
            refine ⟨30431192311072664231388293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81149846162860437950368781 30431192311072664231388293)
            ·
              refine ⟨5705848558326124543385305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30431192311072664231388293 5705848558326124543385305)
              ·
                refine ⟨4279386418744593407538979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5705848558326124543385305 4279386418744593407538979)
                ·
                  refine ⟨6419079628116890111308469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4279386418744593407538979 6419079628116890111308469)
                  ·
                    refine ⟨601788715135958447935169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6419079628116890111308469 601788715135958447935169)
                    ·
                      rfl

theorem cell22_1757969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_1757969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757969 prefixEnd_1757969 := by exact prefixLift 1757969
  have htrace : WordTrace (prefixWord ++ tailWord_1757969) baseStart_1757969 baseEnd_1757969 := by
    simpa [prefixWord, tailWord_1757969, baseEnd_1757969] using wordTrace_append hprefix tailTrace_1757969
  have hstable : (prefixWord ++ tailWord_1757969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757969).length < 2 ^ (prefixWord ++ tailWord_1757969).sum := by decide
  have hdescent : baseEnd_1757969 < baseStart_1757969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757971 : List Nat := [1, 1, 1, 2, 1, 3, 6, 3, 4]
def baseStart_1757971 : Nat := 118140960795 + 1757971 * 2 ^ 59
def prefixEnd_1757971 : Nat := 4983230072969 + 3 ^ 40 * 1757971 * 2
def baseEnd_1757971 : Nat := 200596466592277036461721

theorem tailTrace_1757971 : CollatzResearch.WordTrace tailWord_1757971 prefixEnd_1757971 200596466592277036461721 := by
  unfold tailWord_1757971
  simp only [CollatzResearch.WordTrace]
  refine ⟨64118469914178779388777767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42745646609452519592518511 64118469914178779388777767)
  ·
    refine ⟨96177704871268169083166651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64118469914178779388777767 96177704871268169083166651)
    ·
      refine ⟨144266557306902253624749977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96177704871268169083166651 144266557306902253624749977)
      ·
        refine ⟨108199917980176690218562483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144266557306902253624749977 108199917980176690218562483)
        ·
          refine ⟨162299876970265035327843725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108199917980176690218562483 162299876970265035327843725)
          ·
            refine ⟨60862453863849388247941397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162299876970265035327843725 60862453863849388247941397)
            ·
              refine ⟨2852927524867940074122253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60862453863849388247941397 2852927524867940074122253)
              ·
                refine ⟨1069847821825477527795845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2852927524867940074122253 1069847821825477527795845)
                ·
                  refine ⟨200596466592277036461721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1069847821825477527795845 200596466592277036461721)
                  ·
                    rfl

theorem cell22_1757971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 4].length) (baseStart_1757971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1757971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1757971 prefixEnd_1757971 := by exact prefixLift 1757971
  have htrace : WordTrace (prefixWord ++ tailWord_1757971) baseStart_1757971 baseEnd_1757971 := by
    simpa [prefixWord, tailWord_1757971, baseEnd_1757971] using wordTrace_append hprefix tailTrace_1757971
  have hstable : (prefixWord ++ tailWord_1757971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757971).length < 2 ^ (prefixWord ++ tailWord_1757971).sum := by decide
  have hdescent : baseEnd_1757971 < baseStart_1757971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758059 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 2, 5]
def baseStart_1758059 : Nat := 118140960795 + 1758059 * 2 ^ 59
def prefixEnd_1758059 : Nat := 4983230072969 + 3 ^ 40 * 1758059 * 2
def baseEnd_1758059 : Nat := 601819523975228213184893

theorem tailTrace_1758059 : CollatzResearch.WordTrace tailWord_1758059 prefixEnd_1758059 601819523975228213184893 := by
  unfold tailWord_1758059
  simp only [CollatzResearch.WordTrace]
  refine ⟨64121679537859970417981231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42747786358573313611987487 64121679537859970417981231)
  ·
    refine ⟨96182519306789955626971847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64121679537859970417981231 96182519306789955626971847)
    ·
      refine ⟨144273778960184933440457771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96182519306789955626971847 144273778960184933440457771)
      ·
        refine ⟨216410668440277400160686657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144273778960184933440457771 216410668440277400160686657)
        ·
          refine ⟨162308001330208050120514993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216410668440277400160686657 162308001330208050120514993)
          ·
            refine ⟨121731000997656037590386245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162308001330208050120514993 121731000997656037590386245)
            ·
              refine ⟨22824562687060507048197421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121731000997656037590386245 22824562687060507048197421)
              ·
                refine ⟨8559211007647690143074033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22824562687060507048197421 8559211007647690143074033)
                ·
                  refine ⟨6419408255735767607305525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8559211007647690143074033 6419408255735767607305525)
                  ·
                    refine ⟨601819523975228213184893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6419408255735767607305525 601819523975228213184893)
                    ·
                      rfl

theorem cell22_1758059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 5].length) (baseStart_1758059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758059 prefixEnd_1758059 := by exact prefixLift 1758059
  have htrace : WordTrace (prefixWord ++ tailWord_1758059) baseStart_1758059 baseEnd_1758059 := by
    simpa [prefixWord, tailWord_1758059, baseEnd_1758059] using wordTrace_append hprefix tailTrace_1758059
  have hstable : (prefixWord ++ tailWord_1758059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758059).length < 2 ^ (prefixWord ++ tailWord_1758059).sum := by decide
  have hdescent : baseEnd_1758059 < baseStart_1758059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758091 : List Nat := [1, 1, 1, 1, 4, 2, 2, 5, 1, 4]
def baseStart_1758091 : Nat := 118140960795 + 1758091 * 2 ^ 59
def prefixEnd_1758091 : Nat := 4983230072969 + 3 ^ 40 * 1758091 * 2
def baseEnd_1758091 : Nat := 601830478229190796384795

theorem tailTrace_1758091 : CollatzResearch.WordTrace tailWord_1758091 prefixEnd_1758091 601830478229190796384795 := by
  unfold tailWord_1758091
  simp only [CollatzResearch.WordTrace]
  refine ⟨64122846673744039883146127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42748564449162693255430751 64122846673744039883146127)
  ·
    refine ⟨96184270010616059824719191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64122846673744039883146127 96184270010616059824719191)
    ·
      refine ⟨144276405015924089737078787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96184270010616059824719191 144276405015924089737078787)
      ·
        refine ⟨216414607523886134605618181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144276405015924089737078787 216414607523886134605618181)
        ·
          refine ⟨40577738910728650238553409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216414607523886134605618181 40577738910728650238553409)
          ·
            refine ⟨30433304183046487678915057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40577738910728650238553409 30433304183046487678915057)
            ·
              refine ⟨22824978137284865759186293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30433304183046487678915057 22824978137284865759186293)
              ·
                refine ⟨2139841700370456164923715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22824978137284865759186293 2139841700370456164923715)
                ·
                  refine ⟨3209762550555684247385573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2139841700370456164923715 3209762550555684247385573)
                  ·
                    refine ⟨601830478229190796384795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3209762550555684247385573 601830478229190796384795)
                    ·
                      rfl

theorem cell22_1758091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 4].length) (baseStart_1758091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758091 prefixEnd_1758091 := by exact prefixLift 1758091
  have htrace : WordTrace (prefixWord ++ tailWord_1758091) baseStart_1758091 baseEnd_1758091 := by
    simpa [prefixWord, tailWord_1758091, baseEnd_1758091] using wordTrace_append hprefix tailTrace_1758091
  have hstable : (prefixWord ++ tailWord_1758091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758091).length < 2 ^ (prefixWord ++ tailWord_1758091).sum := by decide
  have hdescent : baseEnd_1758091 < baseStart_1758091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758121 : List Nat := [1, 2, 1, 1, 1, 1, 8, 1, 1, 5]
def baseStart_1758121 : Nat := 118140960795 + 1758121 * 2 ^ 59
def prefixEnd_1758121 : Nat := 4983230072969 + 3 ^ 40 * 1758121 * 2
def baseEnd_1758121 : Nat := 601840747842280718134703

theorem tailTrace_1758121 : CollatzResearch.WordTrace tailWord_1758121 prefixEnd_1758121 601840747842280718134703 := by
  unfold tailWord_1758121
  simp only [CollatzResearch.WordTrace]
  refine ⟨64123940863635355006738217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42749293909090236671158811 64123940863635355006738217)
  ·
    refine ⟨48092955647726516255053663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64123940863635355006738217 48092955647726516255053663)
    ·
      refine ⟨72139433471589774382580495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48092955647726516255053663 72139433471589774382580495)
      ·
        refine ⟨108209150207384661573870743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72139433471589774382580495 108209150207384661573870743)
        ·
          refine ⟨162313725311076992360806115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108209150207384661573870743 162313725311076992360806115)
          ·
            refine ⟨243470587966615488541209173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162313725311076992360806115 243470587966615488541209173)
            ·
              refine ⟨2853170952733775256342295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 243470587966615488541209173 2853170952733775256342295)
              ·
                refine ⟨4279756429100662884513443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2853170952733775256342295 4279756429100662884513443)
                ·
                  refine ⟨6419634643650994326770165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4279756429100662884513443 6419634643650994326770165)
                  ·
                    refine ⟨601840747842280718134703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6419634643650994326770165 601840747842280718134703)
                    ·
                      rfl

theorem cell22_1758121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 5].length) (baseStart_1758121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758121 prefixEnd_1758121 := by exact prefixLift 1758121
  have htrace : WordTrace (prefixWord ++ tailWord_1758121) baseStart_1758121 baseEnd_1758121 := by
    simpa [prefixWord, tailWord_1758121, baseEnd_1758121] using wordTrace_append hprefix tailTrace_1758121
  have hstable : (prefixWord ++ tailWord_1758121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758121).length < 2 ^ (prefixWord ++ tailWord_1758121).sum := by decide
  have hdescent : baseEnd_1758121 < baseStart_1758121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758136 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 1, 6]
def baseStart_1758136 : Nat := 118140960795 + 1758136 * 2 ^ 59
def prefixEnd_1758136 : Nat := 4983230072969 + 3 ^ 40 * 1758136 * 2
def baseEnd_1758136 : Nat := 601845882648825679009657

theorem tailTrace_1758136 : CollatzResearch.WordTrace tailWord_1758136 prefixEnd_1758136 601845882648825679009657 := by
  unfold tailWord_1758136
  simp only [CollatzResearch.WordTrace]
  refine ⟨32062243979290506284267131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42749658639054008379022841 32062243979290506284267131)
  ·
    refine ⟨48093365968935759426400697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32062243979290506284267131 48093365968935759426400697)
    ·
      refine ⟨36070024476701819569800523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48093365968935759426400697 36070024476701819569800523)
      ·
        refine ⟨54105036715052729354700785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36070024476701819569800523 54105036715052729354700785)
        ·
          refine ⟨40578777536289547016025589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54105036715052729354700785 40578777536289547016025589)
          ·
            refine ⟨3804260394027145032752399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40578777536289547016025589 3804260394027145032752399)
            ·
              refine ⟨5706390591040717549128599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3804260394027145032752399 5706390591040717549128599)
              ·
                refine ⟨8559585886561076323692899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5706390591040717549128599 8559585886561076323692899)
                ·
                  refine ⟨12839378829841614485539349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8559585886561076323692899 12839378829841614485539349)
                  ·
                    refine ⟨601845882648825679009657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12839378829841614485539349 601845882648825679009657)
                    ·
                      rfl

theorem cell22_1758136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_1758136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758136 prefixEnd_1758136 := by exact prefixLift 1758136
  have htrace : WordTrace (prefixWord ++ tailWord_1758136) baseStart_1758136 baseEnd_1758136 := by
    simpa [prefixWord, tailWord_1758136, baseEnd_1758136] using wordTrace_append hprefix tailTrace_1758136
  have hstable : (prefixWord ++ tailWord_1758136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758136).length < 2 ^ (prefixWord ++ tailWord_1758136).sum := by decide
  have hdescent : baseEnd_1758136 < baseStart_1758136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758155 : List Nat := [1, 1, 1, 1, 3, 7, 1, 2, 2, 3]
def baseStart_1758155 : Nat := 118140960795 + 1758155 * 2 ^ 59
def prefixEnd_1758155 : Nat := 4983230072969 + 3 ^ 40 * 1758155 * 2
def baseEnd_1758155 : Nat := 601852386737115962784599

theorem tailTrace_1758155 : CollatzResearch.WordTrace tailWord_1758155 prefixEnd_1758155 601852386737115962784599 := by
  unfold tailWord_1758155
  simp only [CollatzResearch.WordTrace]
  refine ⟨64125180945512178813475919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42750120630341452542317279 64125180945512178813475919)
  ·
    refine ⟨96187771418268268220213879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64125180945512178813475919 96187771418268268220213879)
    ·
      refine ⟨144281657127402402330320819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96187771418268268220213879 144281657127402402330320819)
      ·
        refine ⟨216422485691103603495481229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144281657127402402330320819 216422485691103603495481229)
        ·
          refine ⟨81158432134163851310805461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216422485691103603495481229 81158432134163851310805461)
          ·
            refine ⟨1902150753144465265097003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 81158432134163851310805461 1902150753144465265097003)
            ·
              refine ⟨2853226129716697897645505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1902150753144465265097003 2853226129716697897645505)
              ·
                refine ⟨2139919597287523423234129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2853226129716697897645505 2139919597287523423234129)
                ·
                  refine ⟨1604939697965642567425597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2139919597287523423234129 1604939697965642567425597)
                  ·
                    refine ⟨601852386737115962784599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1604939697965642567425597 601852386737115962784599)
                    ·
                      rfl

theorem cell22_1758155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 3].length) (baseStart_1758155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758155 prefixEnd_1758155 := by exact prefixLift 1758155
  have htrace : WordTrace (prefixWord ++ tailWord_1758155) baseStart_1758155 baseEnd_1758155 := by
    simpa [prefixWord, tailWord_1758155, baseEnd_1758155] using wordTrace_append hprefix tailTrace_1758155
  have hstable : (prefixWord ++ tailWord_1758155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758155).length < 2 ^ (prefixWord ++ tailWord_1758155).sum := by decide
  have hdescent : baseEnd_1758155 < baseStart_1758155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758243 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 3, 4]
def baseStart_1758243 : Nat := 118140960795 + 1758243 * 2 ^ 59
def prefixEnd_1758243 : Nat := 4983230072969 + 3 ^ 40 * 1758243 * 2
def baseEnd_1758243 : Nat := 601882510935513066584329

theorem tailTrace_1758243 : CollatzResearch.WordTrace tailWord_1758243 prefixEnd_1758243 601882510935513066584329 := by
  unfold tailWord_1758243
  simp only [CollatzResearch.WordTrace]
  refine ⟨64128390569193369842679383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42752260379462246561786255 64128390569193369842679383)
  ·
    refine ⟨96192585853790054764019075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64128390569193369842679383 96192585853790054764019075)
    ·
      refine ⟨144288878780685082146028613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96192585853790054764019075 144288878780685082146028613)
      ·
        refine ⟨27054164771378452902380365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144288878780685082146028613 27054164771378452902380365)
        ·
          refine ⟨10145311789266919838392637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27054164771378452902380365 10145311789266919838392637)
          ·
            refine ⟨3804491920975094939397239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10145311789266919838392637 3804491920975094939397239)
            ·
              refine ⟨5706737881462642409095859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3804491920975094939397239 5706737881462642409095859)
              ·
                refine ⟨8560106822193963613643789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5706737881462642409095859 8560106822193963613643789)
                ·
                  refine ⟨3210040058322736355116421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8560106822193963613643789 3210040058322736355116421)
                  ·
                    refine ⟨601882510935513066584329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3210040058322736355116421 601882510935513066584329)
                    ·
                      rfl

theorem cell22_1758243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 4].length) (baseStart_1758243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758243 prefixEnd_1758243 := by exact prefixLift 1758243
  have htrace : WordTrace (prefixWord ++ tailWord_1758243) baseStart_1758243 baseEnd_1758243 := by
    simpa [prefixWord, tailWord_1758243, baseEnd_1758243] using wordTrace_append hprefix tailTrace_1758243
  have hstable : (prefixWord ++ tailWord_1758243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758243).length < 2 ^ (prefixWord ++ tailWord_1758243).sum := by decide
  have hdescent : baseEnd_1758243 < baseStart_1758243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758271 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 3, 6]
def baseStart_1758271 : Nat := 118140960795 + 1758271 * 2 ^ 59
def prefixEnd_1758271 : Nat := 4983230072969 + 3 ^ 40 * 1758271 * 2
def baseEnd_1758271 : Nat := 601892095907730326884243

theorem tailTrace_1758271 : CollatzResearch.WordTrace tailWord_1758271 prefixEnd_1758271 601892095907730326884243 := by
  unfold tailWord_1758271
  simp only [CollatzResearch.WordTrace]
  refine ⟨64129411813091930624698667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42752941208727953749799111 64129411813091930624698667)
  ·
    refine ⟨96194117719637895937048001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64129411813091930624698667 96194117719637895937048001)
    ·
      refine ⟨72145588289728421952786001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96194117719637895937048001 72145588289728421952786001)
      ·
        refine ⟨54109191217296316464589501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72145588289728421952786001 54109191217296316464589501)
        ·
          refine ⟨20290946706486118674221063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54109191217296316464589501 20290946706486118674221063)
          ·
            refine ⟨30436420059729178011331595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20290946706486118674221063 30436420059729178011331595)
            ·
              refine ⟨45654630089593767016997393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30436420059729178011331595 45654630089593767016997393)
              ·
                refine ⟨34240972567195325262748045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45654630089593767016997393 34240972567195325262748045)
                ·
                  refine ⟨12840364712698246973530517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34240972567195325262748045 12840364712698246973530517)
                  ·
                    refine ⟨601892095907730326884243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12840364712698246973530517 601892095907730326884243)
                    ·
                      rfl

theorem cell22_1758271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_1758271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758271 prefixEnd_1758271 := by exact prefixLift 1758271
  have htrace : WordTrace (prefixWord ++ tailWord_1758271) baseStart_1758271 baseEnd_1758271 := by
    simpa [prefixWord, tailWord_1758271, baseEnd_1758271] using wordTrace_append hprefix tailTrace_1758271
  have hstable : (prefixWord ++ tailWord_1758271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758271).length < 2 ^ (prefixWord ++ tailWord_1758271).sum := by decide
  have hdescent : baseEnd_1758271 < baseStart_1758271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758290 : List Nat := [3, 2, 2, 1, 3, 2, 2, 1, 1, 5]
def baseStart_1758290 : Nat := 118140960795 + 1758290 * 2 ^ 59
def prefixEnd_1758290 : Nat := 4983230072969 + 3 ^ 40 * 1758290 * 2
def baseEnd_1758290 : Nat := 601898599996020610659185

theorem tailTrace_1758290 : CollatzResearch.WordTrace tailWord_1758290 prefixEnd_1758290 601898599996020610659185 := by
  unfold tailWord_1758290
  simp only [CollatzResearch.WordTrace]
  refine ⟨16032526200005774217410081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42753403200015397913093549 16032526200005774217410081)
  ·
    refine ⟨12024394650004330663057561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16032526200005774217410081 12024394650004330663057561)
    ·
      refine ⟨9018295987503247997293171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12024394650004330663057561 9018295987503247997293171)
      ·
        refine ⟨13527443981254871995939757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9018295987503247997293171 13527443981254871995939757)
        ·
          refine ⟨5072791492970576998477409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13527443981254871995939757 5072791492970576998477409)
          ·
            refine ⟨3804593619727932748858057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5072791492970576998477409 3804593619727932748858057)
            ·
              refine ⟨2853445214795949561643543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3804593619727932748858057 2853445214795949561643543)
              ·
                refine ⟨4280167822193924342465315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2853445214795949561643543 4280167822193924342465315)
                ·
                  refine ⟨6420251733290886513697973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4280167822193924342465315 6420251733290886513697973)
                  ·
                    refine ⟨601898599996020610659185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6420251733290886513697973 601898599996020610659185)
                    ·
                      rfl

theorem cell22_1758290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_1758290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758290 prefixEnd_1758290 := by exact prefixLift 1758290
  have htrace : WordTrace (prefixWord ++ tailWord_1758290) baseStart_1758290 baseEnd_1758290 := by
    simpa [prefixWord, tailWord_1758290, baseEnd_1758290] using wordTrace_append hprefix tailTrace_1758290
  have hstable : (prefixWord ++ tailWord_1758290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758290).length < 2 ^ (prefixWord ++ tailWord_1758290).sum := by decide
  have hdescent : baseEnd_1758290 < baseStart_1758290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758303 : List Nat := [1, 1, 2, 3, 1, 1, 7, 6]
def baseStart_1758303 : Nat := 118140960795 + 1758303 * 2 ^ 59
def prefixEnd_1758303 : Nat := 4983230072969 + 3 ^ 40 * 1758303 * 2
def baseEnd_1758303 : Nat := 66878116684632545564905

theorem tailTrace_1758303 : CollatzResearch.WordTrace tailWord_1758303 prefixEnd_1758303 66878116684632545564905 := by
  unfold tailWord_1758303
  simp only [CollatzResearch.WordTrace]
  refine ⟨64130578948976000089863563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42753719299317333393242375 64130578948976000089863563)
  ·
    refine ⟨96195868423464000134795345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64130578948976000089863563 96195868423464000134795345)
    ·
      refine ⟨72146901317598000101096509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96195868423464000134795345 72146901317598000101096509)
      ·
        refine ⟨27055087994099250037911191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72146901317598000101096509 27055087994099250037911191)
        ·
          refine ⟨40582631991148875056866787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27055087994099250037911191 40582631991148875056866787)
          ·
            refine ⟨60873947986723312585300181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40582631991148875056866787 60873947986723312585300181)
            ·
              refine ⟨1426733155938827638717973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 60873947986723312585300181 1426733155938827638717973)
              ·
                refine ⟨66878116684632545564905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1426733155938827638717973 66878116684632545564905)
                ·
                  rfl

theorem cell22_1758303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 6].length) (baseStart_1758303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758303 prefixEnd_1758303 := by exact prefixLift 1758303
  have htrace : WordTrace (prefixWord ++ tailWord_1758303) baseStart_1758303 baseEnd_1758303 := by
    simpa [prefixWord, tailWord_1758303, baseEnd_1758303] using wordTrace_append hprefix tailTrace_1758303
  have hstable : (prefixWord ++ tailWord_1758303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758303).length < 2 ^ (prefixWord ++ tailWord_1758303).sum := by decide
  have hdescent : baseEnd_1758303 < baseStart_1758303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758348 : List Nat := [2, 2, 1, 2, 1, 1, 1, 7, 5]
def baseStart_1758348 : Nat := 118140960795 + 1758348 * 2 ^ 59
def prefixEnd_1758348 : Nat := 4983230072969 + 3 ^ 40 * 1758348 * 2
def baseEnd_1758348 : Nat := 200639484860442597569669

theorem tailTrace_1758348 : CollatzResearch.WordTrace tailWord_1758348 prefixEnd_1758348 200639484860442597569669 := by
  unfold tailWord_1758348
  simp only [CollatzResearch.WordTrace]
  refine ⟨32066110116906486387625849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42754813489208648516834465 32066110116906486387625849)
  ·
    refine ⟨24049582587679864790719387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32066110116906486387625849 24049582587679864790719387)
    ·
      refine ⟨36074373881519797186079081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24049582587679864790719387 36074373881519797186079081)
      ·
        refine ⟨27055780411139847889559311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36074373881519797186079081 27055780411139847889559311)
        ·
          refine ⟨40583670616709771834338967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27055780411139847889559311 40583670616709771834338967)
          ·
            refine ⟨60875505925064657751508451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40583670616709771834338967 60875505925064657751508451)
            ·
              refine ⟨91313258887596986627262677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60875505925064657751508451 91313258887596986627262677)
              ·
                refine ⟨2140154505178054374076469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 91313258887596986627262677 2140154505178054374076469)
                ·
                  refine ⟨200639484860442597569669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2140154505178054374076469 200639484860442597569669)
                  ·
                    rfl

theorem cell22_1758348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_1758348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758348 prefixEnd_1758348 := by exact prefixLift 1758348
  have htrace : WordTrace (prefixWord ++ tailWord_1758348) baseStart_1758348 baseEnd_1758348 := by
    simpa [prefixWord, tailWord_1758348, baseEnd_1758348] using wordTrace_append hprefix tailTrace_1758348
  have hstable : (prefixWord ++ tailWord_1758348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758348).length < 2 ^ (prefixWord ++ tailWord_1758348).sum := by decide
  have hdescent : baseEnd_1758348 < baseStart_1758348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758423 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 1, 6]
def baseStart_1758423 : Nat := 118140960795 + 1758423 * 2 ^ 59
def prefixEnd_1758423 : Nat := 4983230072969 + 3 ^ 40 * 1758423 * 2
def baseEnd_1758423 : Nat := 601944128614052597083777

theorem tailTrace_1758423 : CollatzResearch.WordTrace tailWord_1758423 prefixEnd_1758423 601944128614052597083777 := by
  unfold tailWord_1758423
  simp only [CollatzResearch.WordTrace]
  refine ⟨64134955708541260584231923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42756637139027507056154615 64134955708541260584231923)
  ·
    refine ⟨96202433562811890876347885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64134955708541260584231923 96202433562811890876347885)
    ·
      refine ⟨36075912586054459078630457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96202433562811890876347885 36075912586054459078630457)
      ·
        refine ⟨27056934439540844308972843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36075912586054459078630457 27056934439540844308972843)
        ·
          refine ⟨40585401659311266463459265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27056934439540844308972843 40585401659311266463459265)
          ·
            refine ⟨30439051244483449847594449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40585401659311266463459265 30439051244483449847594449)
            ·
              refine ⟨22829288433362587385695837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30439051244483449847594449 22829288433362587385695837)
              ·
                refine ⟨8560983162510970269635939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22829288433362587385695837 8560983162510970269635939)
                ·
                  refine ⟨12841474743766455404453909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8560983162510970269635939 12841474743766455404453909)
                  ·
                    refine ⟨601944128614052597083777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12841474743766455404453909 601944128614052597083777)
                    ·
                      rfl

theorem cell22_1758423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_1758423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758423 prefixEnd_1758423 := by exact prefixLift 1758423
  have htrace : WordTrace (prefixWord ++ tailWord_1758423) baseStart_1758423 baseEnd_1758423 := by
    simpa [prefixWord, tailWord_1758423, baseEnd_1758423] using wordTrace_append hprefix tailTrace_1758423
  have hstable : (prefixWord ++ tailWord_1758423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758423).length < 2 ^ (prefixWord ++ tailWord_1758423).sum := by decide
  have hdescent : baseEnd_1758423 < baseStart_1758423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758440 : List Nat := [2, 1, 4, 1, 2, 1, 1, 4, 2, 4]
def baseStart_1758440 : Nat := 118140960795 + 1758440 * 2 ^ 59
def prefixEnd_1758440 : Nat := 4983230072969 + 3 ^ 40 * 1758440 * 2
def baseEnd_1758440 : Nat := 601949948061470219408725

theorem tailTrace_1758440 : CollatzResearch.WordTrace tailWord_1758440 prefixEnd_1758440 601949948061470219408725 := by
  unfold tailWord_1758440
  simp only [CollatzResearch.WordTrace]
  refine ⟨32067787874739836243800387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42757050499653114991733849 32067787874739836243800387)
  ·
    refine ⟨48101681812109754365700581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32067787874739836243800387 48101681812109754365700581)
    ·
      refine ⟨9019065339770578943568859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48101681812109754365700581 9019065339770578943568859)
      ·
        refine ⟨13528598009655868415353289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9019065339770578943568859 13528598009655868415353289)
        ·
          refine ⟨10146448507241901311514967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13528598009655868415353289 10146448507241901311514967)
          ·
            refine ⟨15219672760862851967272451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10146448507241901311514967 15219672760862851967272451)
            ·
              refine ⟨22829509141294277950908677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15219672760862851967272451 22829509141294277950908677)
              ·
                refine ⟨4280532963992677115795377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22829509141294277950908677 4280532963992677115795377)
                ·
                  refine ⟨3210399722994507836846533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4280532963992677115795377 3210399722994507836846533)
                  ·
                    refine ⟨601949948061470219408725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3210399722994507836846533 601949948061470219408725)
                    ·
                      rfl

theorem cell22_1758440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_1758440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758440 prefixEnd_1758440 := by exact prefixLift 1758440
  have htrace : WordTrace (prefixWord ++ tailWord_1758440) baseStart_1758440 baseEnd_1758440 := by
    simpa [prefixWord, tailWord_1758440, baseEnd_1758440] using wordTrace_append hprefix tailTrace_1758440
  have hstable : (prefixWord ++ tailWord_1758440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758440).length < 2 ^ (prefixWord ++ tailWord_1758440).sum := by decide
  have hdescent : baseEnd_1758440 < baseStart_1758440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758442 : List Nat := [3, 1, 3, 1, 1, 3, 1, 4, 2, 3]
def baseStart_1758442 : Nat := 118140960795 + 1758442 * 2 ^ 59
def prefixEnd_1758442 : Nat := 4983230072969 + 3 ^ 40 * 1758442 * 2
def baseEnd_1758442 : Nat := 601950632702342880858719

theorem tailTrace_1758442 : CollatzResearch.WordTrace tailWord_1758442 prefixEnd_1758442 601950632702342880858719 := by
  unfold tailWord_1758442
  simp only [CollatzResearch.WordTrace]
  refine ⟨16033912173868106707293395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42757099130314951219449053 16033912173868106707293395)
  ·
    refine ⟨24050868260802160060940093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16033912173868106707293395 24050868260802160060940093)
    ·
      refine ⟨9019075597800810022852535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24050868260802160060940093 9019075597800810022852535)
      ·
        refine ⟨13528613396701215034278803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9019075597800810022852535 13528613396701215034278803)
        ·
          refine ⟨20292920095051822551418205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13528613396701215034278803 20292920095051822551418205)
          ·
            refine ⟨7609845035644433456781827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20292920095051822551418205 7609845035644433456781827)
            ·
              refine ⟨11414767553466650185172741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7609845035644433456781827 11414767553466650185172741)
              ·
                refine ⟨2140268916274996909719889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11414767553466650185172741 2140268916274996909719889)
                ·
                  refine ⟨1605201687206247682289917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2140268916274996909719889 1605201687206247682289917)
                  ·
                    refine ⟨601950632702342880858719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1605201687206247682289917 601950632702342880858719)
                    ·
                      rfl

theorem cell22_1758442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_1758442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758442 prefixEnd_1758442 := by exact prefixLift 1758442
  have htrace : WordTrace (prefixWord ++ tailWord_1758442) baseStart_1758442 baseEnd_1758442 := by
    simpa [prefixWord, tailWord_1758442, baseEnd_1758442] using wordTrace_append hprefix tailTrace_1758442
  have hstable : (prefixWord ++ tailWord_1758442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758442).length < 2 ^ (prefixWord ++ tailWord_1758442).sum := by decide
  have hdescent : baseEnd_1758442 < baseStart_1758442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758444 : List Nat := [2, 2, 1, 1, 2, 6, 2, 2, 4]
def baseStart_1758444 : Nat := 118140960795 + 1758444 * 2 ^ 59
def prefixEnd_1758444 : Nat := 4983230072969 + 3 ^ 40 * 1758444 * 2
def baseEnd_1758444 : Nat := 200650439114405180769571

theorem tailTrace_1758444 : CollatzResearch.WordTrace tailWord_1758444 prefixEnd_1758444 200650439114405180769571 := by
  unfold tailWord_1758444
  simp only [CollatzResearch.WordTrace]
  refine ⟨32067860820732590585373193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42757147760976787447164257 32067860820732590585373193)
  ·
    refine ⟨24050895615549442939029895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32067860820732590585373193 24050895615549442939029895)
    ·
      refine ⟨36076343423324164408544843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24050895615549442939029895 36076343423324164408544843)
      ·
        refine ⟨54114515134986246612817265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36076343423324164408544843 54114515134986246612817265)
        ·
          refine ⟨40585886351239684959612949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54114515134986246612817265 40585886351239684959612949)
          ·
            refine ⟨1902463422714360232481857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40585886351239684959612949 1902463422714360232481857)
            ·
              refine ⟨1426847567035770174361393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1902463422714360232481857 1426847567035770174361393)
              ·
                refine ⟨1070135675276827630771045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1426847567035770174361393 1070135675276827630771045)
                ·
                  refine ⟨200650439114405180769571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1070135675276827630771045 200650439114405180769571)
                  ·
                    rfl

theorem cell22_1758444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 4].length) (baseStart_1758444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758444 prefixEnd_1758444 := by exact prefixLift 1758444
  have htrace : WordTrace (prefixWord ++ tailWord_1758444) baseStart_1758444 baseEnd_1758444 := by
    simpa [prefixWord, tailWord_1758444, baseEnd_1758444] using wordTrace_append hprefix tailTrace_1758444
  have hstable : (prefixWord ++ tailWord_1758444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758444).length < 2 ^ (prefixWord ++ tailWord_1758444).sum := by decide
  have hdescent : baseEnd_1758444 < baseStart_1758444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758472 : List Nat := [2, 1, 3, 2, 4, 1, 3, 6]
def baseStart_1758472 : Nat := 118140960795 + 1758472 * 2 ^ 59
def prefixEnd_1758472 : Nat := 4983230072969 + 3 ^ 40 * 1758472 * 2
def baseEnd_1758472 : Nat := 66884544701714755845403

theorem tailTrace_1758472 : CollatzResearch.WordTrace tailWord_1758472 prefixEnd_1758472 66884544701714755845403 := by
  unfold tailWord_1758472
  simp only [CollatzResearch.WordTrace]
  refine ⟨32068371442681870976382835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42757828590242494635177113 32068371442681870976382835)
  ·
    refine ⟨48102557164022806464574253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32068371442681870976382835 48102557164022806464574253)
    ·
      refine ⟨18038458936508552424215345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48102557164022806464574253 18038458936508552424215345)
      ·
        refine ⟨13528844202381414318161509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18038458936508552424215345 13528844202381414318161509)
        ·
          refine ⟨2536658287946515184655283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13528844202381414318161509 2536658287946515184655283)
          ·
            refine ⟨3804987431919772776982925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2536658287946515184655283 3804987431919772776982925)
            ·
              refine ⟨1426870286969914791368597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3804987431919772776982925 1426870286969914791368597)
              ·
                refine ⟨66884544701714755845403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1426870286969914791368597 66884544701714755845403)
                ·
                  rfl

theorem cell22_1758472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 6].length) (baseStart_1758472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758472 prefixEnd_1758472 := by exact prefixLift 1758472
  have htrace : WordTrace (prefixWord ++ tailWord_1758472) baseStart_1758472 baseEnd_1758472 := by
    simpa [prefixWord, tailWord_1758472, baseEnd_1758472] using wordTrace_append hprefix tailTrace_1758472
  have hstable : (prefixWord ++ tailWord_1758472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758472).length < 2 ^ (prefixWord ++ tailWord_1758472).sum := by decide
  have hdescent : baseEnd_1758472 < baseStart_1758472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758500 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 7]
def baseStart_1758500 : Nat := 118140960795 + 1758500 * 2 ^ 59
def prefixEnd_1758500 : Nat := 4983230072969 + 3 ^ 40 * 1758500 * 2
def baseEnd_1758500 : Nat := 200656829095883354302847

theorem tailTrace_1758500 : CollatzResearch.WordTrace tailWord_1758500 prefixEnd_1758500 200656829095883354302847 := by
  unfold tailWord_1758500
  simp only [CollatzResearch.WordTrace]
  refine ⟨32068882064631151367392477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42758509419508201823189969 32068882064631151367392477)
  ·
    refine ⟨12025830774236681762772179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32068882064631151367392477 12025830774236681762772179)
    ·
      refine ⟨18038746161355022644158269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12025830774236681762772179 18038746161355022644158269)
      ·
        refine ⟨6764529810508133491559351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18038746161355022644158269 6764529810508133491559351)
        ·
          refine ⟨10146794715762200237339027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6764529810508133491559351 10146794715762200237339027)
          ·
            refine ⟨15220192073643300356008541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10146794715762200237339027 15220192073643300356008541)
            ·
              refine ⟨5707572027616237633503203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15220192073643300356008541 5707572027616237633503203)
              ·
                refine ⟨8561358041424356450254805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5707572027616237633503203 8561358041424356450254805)
                ·
                  refine ⟨200656829095883354302847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8561358041424356450254805 200656829095883354302847)
                  ·
                    rfl

theorem cell22_1758500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_1758500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758500 prefixEnd_1758500 := by exact prefixLift 1758500
  have htrace : WordTrace (prefixWord ++ tailWord_1758500) baseStart_1758500 baseEnd_1758500 := by
    simpa [prefixWord, tailWord_1758500, baseEnd_1758500] using wordTrace_append hprefix tailTrace_1758500
  have hstable : (prefixWord ++ tailWord_1758500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758500).length < 2 ^ (prefixWord ++ tailWord_1758500).sum := by decide
  have hdescent : baseEnd_1758500 < baseStart_1758500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758504 : List Nat := [2, 1, 5, 1, 2, 2, 2, 1, 3, 3]
def baseStart_1758504 : Nat := 118140960795 + 1758504 * 2 ^ 59
def prefixEnd_1758504 : Nat := 4983230072969 + 3 ^ 40 * 1758504 * 2
def baseEnd_1758504 : Nat := 601971856569395385808529

theorem tailTrace_1758504 : CollatzResearch.WordTrace tailWord_1758504 prefixEnd_1758504 601971856569395385808529 := by
  unfold tailWord_1758504
  simp only [CollatzResearch.WordTrace]
  refine ⟨32068955010623905708965283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42758606680831874278620377 32068955010623905708965283)
  ·
    refine ⟨48103432515935858563447925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32068955010623905708965283 48103432515935858563447925)
    ·
      refine ⟨4509696798368986740323243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48103432515935858563447925 4509696798368986740323243)
      ·
        refine ⟨6764545197553480110484865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4509696798368986740323243 6764545197553480110484865)
        ·
          refine ⟨5073408898165110082863649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6764545197553480110484865 5073408898165110082863649)
          ·
            refine ⟨3805056673623832562147737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5073408898165110082863649 3805056673623832562147737)
            ·
              refine ⟨2853792505217874421610803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3805056673623832562147737 2853792505217874421610803)
              ·
                refine ⟨4280688757826811632416205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2853792505217874421610803 4280688757826811632416205)
                ·
                  refine ⟨1605258284185054362156077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4280688757826811632416205 1605258284185054362156077)
                  ·
                    refine ⟨601971856569395385808529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1605258284185054362156077 601971856569395385808529)
                    ·
                      rfl

theorem cell22_1758504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_1758504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758504 prefixEnd_1758504 := by exact prefixLift 1758504
  have htrace : WordTrace (prefixWord ++ tailWord_1758504) baseStart_1758504 baseEnd_1758504 := by
    simpa [prefixWord, tailWord_1758504, baseEnd_1758504] using wordTrace_append hprefix tailTrace_1758504
  have hstable : (prefixWord ++ tailWord_1758504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758504).length < 2 ^ (prefixWord ++ tailWord_1758504).sum := by decide
  have hdescent : baseEnd_1758504 < baseStart_1758504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758515 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 2, 5]
def baseStart_1758515 : Nat := 118140960795 + 1758515 * 2 ^ 59
def prefixEnd_1758515 : Nat := 4983230072969 + 3 ^ 40 * 1758515 * 2
def baseEnd_1758515 : Nat := 601975622094195023783495

theorem tailTrace_1758515 : CollatzResearch.WordTrace tailWord_1758515 prefixEnd_1758515 601975622094195023783495 := by
  unfold tailWord_1758515
  simp only [CollatzResearch.WordTrace]
  refine ⟨64138311224207960296580999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42758874149471973531053999 64138311224207960296580999)
  ·
    refine ⟨96207466836311940444871499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64138311224207960296580999 96207466836311940444871499)
    ·
      refine ⟨144311200254467910667307249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96207466836311940444871499 144311200254467910667307249)
      ·
        refine ⟨108233400190850933000480437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144311200254467910667307249 108233400190850933000480437)
        ·
          refine ⟨10146881267892274968795041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108233400190850933000480437 10146881267892274968795041)
          ·
            refine ⟨7610160950919206226596281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10146881267892274968795041 7610160950919206226596281)
            ·
              refine ⟨5707620713189404669947211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7610160950919206226596281 5707620713189404669947211)
              ·
                refine ⟨8561431069784107004920817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5707620713189404669947211 8561431069784107004920817)
                ·
                  refine ⟨6421073302338080253690613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8561431069784107004920817 6421073302338080253690613)
                  ·
                    refine ⟨601975622094195023783495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6421073302338080253690613 601975622094195023783495)
                    ·
                      rfl

theorem cell22_1758515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 5].length) (baseStart_1758515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758515 prefixEnd_1758515 := by exact prefixLift 1758515
  have htrace : WordTrace (prefixWord ++ tailWord_1758515) baseStart_1758515 baseEnd_1758515 := by
    simpa [prefixWord, tailWord_1758515, baseEnd_1758515] using wordTrace_append hprefix tailTrace_1758515
  have hstable : (prefixWord ++ tailWord_1758515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758515).length < 2 ^ (prefixWord ++ tailWord_1758515).sum := by decide
  have hdescent : baseEnd_1758515 < baseStart_1758515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758575 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 4, 4]
def baseStart_1758575 : Nat := 118140960795 + 1758575 * 2 ^ 59
def prefixEnd_1758575 : Nat := 4983230072969 + 3 ^ 40 * 1758575 * 2
def baseEnd_1758575 : Nat := 601996161320374867283311

theorem tailTrace_1758575 : CollatzResearch.WordTrace tailWord_1758575 prefixEnd_1758575 601996161320374867283311 := by
  unfold tailWord_1758575
  simp only [CollatzResearch.WordTrace]
  refine ⟨64140499603990590543765179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42760333069327060362510119 64140499603990590543765179)
  ·
    refine ⟨96210749405985885815647769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64140499603990590543765179 96210749405985885815647769)
    ·
      refine ⟨72158062054489414361735827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96210749405985885815647769 72158062054489414361735827)
      ·
        refine ⟨108237093081734121542603741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72158062054489414361735827 108237093081734121542603741)
        ·
          refine ⟨40588909905650295578476403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108237093081734121542603741 40588909905650295578476403)
          ·
            refine ⟨60883364858475443367714605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40588909905650295578476403 60883364858475443367714605)
            ·
              refine ⟨22831261821928291262892977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60883364858475443367714605 22831261821928291262892977)
              ·
                refine ⟨17123446366446218447169733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22831261821928291262892977 17123446366446218447169733)
                ·
                  refine ⟨3210646193708665958844325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17123446366446218447169733 3210646193708665958844325)
                  ·
                    refine ⟨601996161320374867283311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3210646193708665958844325 601996161320374867283311)
                    ·
                      rfl

theorem cell22_1758575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 4].length) (baseStart_1758575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758575 prefixEnd_1758575 := by exact prefixLift 1758575
  have htrace : WordTrace (prefixWord ++ tailWord_1758575) baseStart_1758575 baseEnd_1758575 := by
    simpa [prefixWord, tailWord_1758575, baseEnd_1758575] using wordTrace_append hprefix tailTrace_1758575
  have hstable : (prefixWord ++ tailWord_1758575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758575).length < 2 ^ (prefixWord ++ tailWord_1758575).sum := by decide
  have hdescent : baseEnd_1758575 < baseStart_1758575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758581 : List Nat := [1, 3, 4, 1, 3, 2, 1, 2, 1, 4]
def baseStart_1758581 : Nat := 118140960795 + 1758581 * 2 ^ 59
def prefixEnd_1758581 : Nat := 4983230072969 + 3 ^ 40 * 1758581 * 2
def baseEnd_1758581 : Nat := 601998215242992851633293

theorem tailTrace_1758581 : CollatzResearch.WordTrace tailWord_1758581 prefixEnd_1758581 601998215242992851633293 := by
  unfold tailWord_1758581
  simp only [CollatzResearch.WordTrace]
  refine ⟨64140718441968853568483597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42760478961312569045655731 64140718441968853568483597)
  ·
    refine ⟨24052769415738320088181349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64140718441968853568483597 24052769415738320088181349)
    ·
      refine ⟨4509894265450935016534003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24052769415738320088181349 4509894265450935016534003)
      ·
        refine ⟨6764841398176402524801005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4509894265450935016534003 6764841398176402524801005)
        ·
          refine ⟨2536815524316150946800377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6764841398176402524801005 2536815524316150946800377)
          ·
            refine ⟨1902611643237113210100283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2536815524316150946800377 1902611643237113210100283)
            ·
              refine ⟨2853917464855669815150425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1902611643237113210100283 2853917464855669815150425)
              ·
                refine ⟨2140438098641752361362819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2853917464855669815150425 2140438098641752361362819)
                ·
                  refine ⟨3210657147962628542044229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2140438098641752361362819 3210657147962628542044229)
                  ·
                    refine ⟨601998215242992851633293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3210657147962628542044229 601998215242992851633293)
                    ·
                      rfl

theorem cell22_1758581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_1758581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758581 prefixEnd_1758581 := by exact prefixLift 1758581
  have htrace : WordTrace (prefixWord ++ tailWord_1758581) baseStart_1758581 baseEnd_1758581 := by
    simpa [prefixWord, tailWord_1758581, baseEnd_1758581] using wordTrace_append hprefix tailTrace_1758581
  have hstable : (prefixWord ++ tailWord_1758581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758581).length < 2 ^ (prefixWord ++ tailWord_1758581).sum := by decide
  have hdescent : baseEnd_1758581 < baseStart_1758581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758594 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_1758594 : Nat := 118140960795 + 1758594 * 2 ^ 59
def prefixEnd_1758594 : Nat := 4983230072969 + 3 ^ 40 * 1758594 * 2
def baseEnd_1758594 : Nat := 602002665408665151058253

theorem tailTrace_1758594 : CollatzResearch.WordTrace tailWord_1758594 prefixEnd_1758594 602002665408665151058253 := by
  unfold tailWord_1758594
  simp only [CollatzResearch.WordTrace]
  refine ⟨16035298147730439197176709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42760795060614504525804557 16035298147730439197176709)
  ·
    refine ⟨3006618402699457349470633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16035298147730439197176709 3006618402699457349470633)
    ·
      refine ⟨2254963802024593012102975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3006618402699457349470633 2254963802024593012102975)
      ·
        refine ⟨3382445703036889518154463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2254963802024593012102975 3382445703036889518154463)
        ·
          refine ⟨5073668554555334277231695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3382445703036889518154463 5073668554555334277231695)
          ·
            refine ⟨7610502831833001415847543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5073668554555334277231695 7610502831833001415847543)
            ·
              refine ⟨11415754247749502123771315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7610502831833001415847543 11415754247749502123771315)
              ·
                refine ⟨17123631371624253185656973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11415754247749502123771315 17123631371624253185656973)
                ·
                  refine ⟨6421361764359094944621365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17123631371624253185656973 6421361764359094944621365)
                  ·
                    refine ⟨602002665408665151058253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6421361764359094944621365 602002665408665151058253)
                    ·
                      rfl

theorem cell22_1758594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_1758594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758594 prefixEnd_1758594 := by exact prefixLift 1758594
  have htrace : WordTrace (prefixWord ++ tailWord_1758594) baseStart_1758594 baseEnd_1758594 := by
    simpa [prefixWord, tailWord_1758594, baseEnd_1758594] using wordTrace_append hprefix tailTrace_1758594
  have hstable : (prefixWord ++ tailWord_1758594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758594).length < 2 ^ (prefixWord ++ tailWord_1758594).sum := by decide
  have hdescent : baseEnd_1758594 < baseStart_1758594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758658 : List Nat := [3, 5, 2, 1, 1, 1, 9]
def baseStart_1758658 : Nat := 118140960795 + 1758658 * 2 ^ 59
def prefixEnd_1758658 : Nat := 4983230072969 + 3 ^ 40 * 1758658 * 2
def baseEnd_1758658 : Nat := 22297206441355196942891

theorem tailTrace_1758658 : CollatzResearch.WordTrace tailWord_1758658 prefixEnd_1758658 22297206441355196942891 := by
  unfold tailWord_1758658
  simp only [CollatzResearch.WordTrace]
  refine ⟨16035881715672473929759157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42762351241793263812691085 16035881715672473929759157)
  ·
    refine ⟨1503363910844294430914921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16035881715672473929759157 1503363910844294430914921)
    ·
      refine ⟨1127522933133220823186191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1503363910844294430914921 1127522933133220823186191)
      ·
        refine ⟨1691284399699831234779287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1127522933133220823186191 1691284399699831234779287)
        ·
          refine ⟨2536926599549746852168931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1691284399699831234779287 2536926599549746852168931)
          ·
            refine ⟨3805389899324620278253397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2536926599549746852168931 3805389899324620278253397)
            ·
              refine ⟨22297206441355196942891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3805389899324620278253397 22297206441355196942891)
              ·
                rfl

theorem cell22_1758658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 9].length) (baseStart_1758658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758658 prefixEnd_1758658 := by exact prefixLift 1758658
  have htrace : WordTrace (prefixWord ++ tailWord_1758658) baseStart_1758658 baseEnd_1758658 := by
    simpa [prefixWord, tailWord_1758658, baseEnd_1758658] using wordTrace_append hprefix tailTrace_1758658
  have hstable : (prefixWord ++ tailWord_1758658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758658).length < 2 ^ (prefixWord ++ tailWord_1758658).sum := by decide
  have hdescent : baseEnd_1758658 < baseStart_1758658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758729 : List Nat := [1, 2, 1, 1, 3, 1, 4, 4, 2, 3]
def baseStart_1758729 : Nat := 118140960795 + 1758729 * 2 ^ 59
def prefixEnd_1758729 : Nat := 4983230072969 + 3 ^ 40 * 1758729 * 2
def baseEnd_1758729 : Nat := 602048878667569798932839

theorem tailTrace_1758729 : CollatzResearch.WordTrace tailWord_1758729 prefixEnd_1758729 602048878667569798932839 := by
  unfold tailWord_1758729
  simp only [CollatzResearch.WordTrace]
  refine ⟨64146116445432674844871241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42764077630288449896580827 64146116445432674844871241)
  ·
    refine ⟨48109587334074506133653431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64146116445432674844871241 48109587334074506133653431)
    ·
      refine ⟨72164381001111759200480147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48109587334074506133653431 72164381001111759200480147)
      ·
        refine ⟨108246571501667638800720221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72164381001111759200480147 108246571501667638800720221)
        ·
          refine ⟨40592464313125364550270083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108246571501667638800720221 40592464313125364550270083)
          ·
            refine ⟨60888696469688046825405125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40592464313125364550270083 60888696469688046825405125)
            ·
              refine ⟨11416630588066508779763461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60888696469688046825405125 11416630588066508779763461)
              ·
                refine ⟨2140618235262470396205649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11416630588066508779763461 2140618235262470396205649)
                ·
                  refine ⟨1605463676446852797154237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2140618235262470396205649 1605463676446852797154237)
                  ·
                    refine ⟨602048878667569798932839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1605463676446852797154237 602048878667569798932839)
                    ·
                      rfl

theorem cell22_1758729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 3].length) (baseStart_1758729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758729 prefixEnd_1758729 := by exact prefixLift 1758729
  have htrace : WordTrace (prefixWord ++ tailWord_1758729) baseStart_1758729 baseEnd_1758729 := by
    simpa [prefixWord, tailWord_1758729, baseEnd_1758729] using wordTrace_append hprefix tailTrace_1758729
  have hstable : (prefixWord ++ tailWord_1758729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758729).length < 2 ^ (prefixWord ++ tailWord_1758729).sum := by decide
  have hdescent : baseEnd_1758729 < baseStart_1758729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758731 : List Nat := [1, 1, 1, 1, 9, 1, 1, 1, 6]
def baseStart_1758731 : Nat := 118140960795 + 1758731 * 2 ^ 59
def prefixEnd_1758731 : Nat := 4983230072969 + 3 ^ 40 * 1758731 * 2
def baseEnd_1758731 : Nat := 200683187769480820127611

theorem tailTrace_1758731 : CollatzResearch.WordTrace tailWord_1758731 prefixEnd_1758731 200683187769480820127611 := by
  unfold tailWord_1758731
  simp only [CollatzResearch.WordTrace]
  refine ⟨64146189391425429186444047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42764126260950286124296031 64146189391425429186444047)
  ·
    refine ⟨96219284087138143779666071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64146189391425429186444047 96219284087138143779666071)
    ·
      refine ⟨144328926130707215669499107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96219284087138143779666071 144328926130707215669499107)
      ·
        refine ⟨216493389196060823504248661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144328926130707215669499107 216493389196060823504248661)
        ·
          refine ⟨1268515952320668887720207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 216493389196060823504248661 1268515952320668887720207)
          ·
            refine ⟨1902773928481003331580311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268515952320668887720207 1902773928481003331580311)
            ·
              refine ⟨2854160892721504997370467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1902773928481003331580311 2854160892721504997370467)
              ·
                refine ⟨4281241339082257496055701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2854160892721504997370467 4281241339082257496055701)
                ·
                  refine ⟨200683187769480820127611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4281241339082257496055701 200683187769480820127611)
                  ·
                    rfl

theorem cell22_1758731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 6].length) (baseStart_1758731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758731 prefixEnd_1758731 := by exact prefixLift 1758731
  have htrace : WordTrace (prefixWord ++ tailWord_1758731) baseStart_1758731 baseEnd_1758731 := by
    simpa [prefixWord, tailWord_1758731, baseEnd_1758731] using wordTrace_append hprefix tailTrace_1758731
  have hstable : (prefixWord ++ tailWord_1758731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758731).length < 2 ^ (prefixWord ++ tailWord_1758731).sum := by decide
  have hdescent : baseEnd_1758731 < baseStart_1758731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758750 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_1758750 : Nat := 118140960795 + 1758750 * 2 ^ 59
def prefixEnd_1758750 : Nat := 4983230072969 + 3 ^ 40 * 1758750 * 2
def baseEnd_1758750 : Nat := 602056067396732744157775

theorem tailTrace_1758750 : CollatzResearch.WordTrace tailWord_1758750 prefixEnd_1758750 602056067396732744157775 := by
  unfold tailWord_1758750
  simp only [CollatzResearch.WordTrace]
  refine ⟨8018360297294574428923213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42764588252237730287590469 8018360297294574428923213)
  ·
    refine ⟨3006885111485465410846205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8018360297294574428923213 3006885111485465410846205)
    ·
      refine ⟨1127581916807049529067327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3006885111485465410846205 1127581916807049529067327)
      ·
        refine ⟨1691372875210574293600991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1127581916807049529067327 1691372875210574293600991)
        ·
          refine ⟨2537059312815861440401487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1691372875210574293600991 2537059312815861440401487)
          ·
            refine ⟨3805588969223792160602231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2537059312815861440401487 3805588969223792160602231)
            ·
              refine ⟨5708383453835688240903347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3805588969223792160602231 5708383453835688240903347)
              ·
                refine ⟨8562575180753532361355021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5708383453835688240903347 8562575180753532361355021)
                ·
                  refine ⟨3210965692782574635508133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8562575180753532361355021 3210965692782574635508133)
                  ·
                    refine ⟨602056067396732744157775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3210965692782574635508133 602056067396732744157775)
                    ·
                      rfl

theorem cell22_1758750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_1758750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758750 prefixEnd_1758750 := by exact prefixLift 1758750
  have htrace : WordTrace (prefixWord ++ tailWord_1758750) baseStart_1758750 baseEnd_1758750 := by
    simpa [prefixWord, tailWord_1758750, baseEnd_1758750] using wordTrace_append hprefix tailTrace_1758750
  have hstable : (prefixWord ++ tailWord_1758750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758750).length < 2 ^ (prefixWord ++ tailWord_1758750).sum := by decide
  have hdescent : baseEnd_1758750 < baseStart_1758750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758804 : List Nat := [2, 4, 1, 1, 1, 2, 1, 5, 5]
def baseStart_1758804 : Nat := 118140960795 + 1758804 * 2 ^ 59
def prefixEnd_1758804 : Nat := 4983230072969 + 3 ^ 40 * 1758804 * 2
def baseEnd_1758804 : Nat := 200691517566764867769203

theorem tailTrace_1758804 : CollatzResearch.WordTrace tailWord_1758804 prefixEnd_1758804 200691517566764867769203 := by
  unfold tailWord_1758804
  simp only [CollatzResearch.WordTrace]
  refine ⟨32074425960080481326925733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42765901280107308435900977 32074425960080481326925733)
  ·
    refine ⟨6013954867515090248798575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32074425960080481326925733 6013954867515090248798575)
    ·
      refine ⟨9020932301272635373197863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6013954867515090248798575 9020932301272635373197863)
      ·
        refine ⟨13531398451908953059796795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9020932301272635373197863 13531398451908953059796795)
        ·
          refine ⟨20297097677863429589695193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13531398451908953059796795 20297097677863429589695193)
          ·
            refine ⟨15222823258397572192271395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20297097677863429589695193 15222823258397572192271395)
            ·
              refine ⟨22834234887596358288407093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15222823258397572192271395 22834234887596358288407093)
              ·
                refine ⟨2140709520712158589538165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22834234887596358288407093 2140709520712158589538165)
                ·
                  refine ⟨200691517566764867769203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2140709520712158589538165 200691517566764867769203)
                  ·
                    rfl

theorem cell22_1758804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_1758804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758804 prefixEnd_1758804 := by exact prefixLift 1758804
  have htrace : WordTrace (prefixWord ++ tailWord_1758804) baseStart_1758804 baseEnd_1758804 := by
    simpa [prefixWord, tailWord_1758804, baseEnd_1758804] using wordTrace_append hprefix tailTrace_1758804
  have hstable : (prefixWord ++ tailWord_1758804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758804).length < 2 ^ (prefixWord ++ tailWord_1758804).sum := by decide
  have hdescent : baseEnd_1758804 < baseStart_1758804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758838 : List Nat := [5, 1, 1, 2, 2, 3, 1, 2, 5]
def baseStart_1758838 : Nat := 118140960795 + 1758838 * 2 ^ 59
def prefixEnd_1758838 : Nat := 4983230072969 + 3 ^ 40 * 1758838 * 2
def baseEnd_1758838 : Nat := 200695397198376615985835

theorem tailTrace_1758838 : CollatzResearch.WordTrace tailWord_1758838 prefixEnd_1758838 200695397198376615985835 := by
  unfold tailWord_1758838
  simp only [CollatzResearch.WordTrace]
  refine ⟨4009380750127361653786823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42766728001358524307059445 4009380750127361653786823)
  ·
    refine ⟨6014071125191042480680235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4009380750127361653786823 6014071125191042480680235)
    ·
      refine ⟨9021106687786563721020353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6014071125191042480680235 9021106687786563721020353)
      ·
        refine ⟨6765830015839922790765265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9021106687786563721020353 6765830015839922790765265)
        ·
          refine ⟨5074372511879942093073949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6765830015839922790765265 5074372511879942093073949)
          ·
            refine ⟨1902889691954978284902731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5074372511879942093073949 1902889691954978284902731)
            ·
              refine ⟨2854334537932467427354097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1902889691954978284902731 2854334537932467427354097)
              ·
                refine ⟨2140750903449350570515573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2854334537932467427354097 2140750903449350570515573)
                ·
                  refine ⟨200695397198376615985835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2140750903449350570515573 200695397198376615985835)
                  ·
                    rfl

theorem cell22_1758838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_1758838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758838 prefixEnd_1758838 := by exact prefixLift 1758838
  have htrace : WordTrace (prefixWord ++ tailWord_1758838) baseStart_1758838 baseEnd_1758838 := by
    simpa [prefixWord, tailWord_1758838, baseEnd_1758838] using wordTrace_append hprefix tailTrace_1758838
  have hstable : (prefixWord ++ tailWord_1758838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758838).length < 2 ^ (prefixWord ++ tailWord_1758838).sum := by decide
  have hdescent : baseEnd_1758838 < baseStart_1758838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758849 : List Nat := [1, 2, 4, 2, 1, 2, 1, 3, 6]
def baseStart_1758849 : Nat := 118140960795 + 1758849 * 2 ^ 59
def prefixEnd_1758849 : Nat := 4983230072969 + 3 ^ 40 * 1758849 * 2
def baseEnd_1758849 : Nat := 200696652373309828644157

theorem tailTrace_1758849 : CollatzResearch.WordTrace tailWord_1758849 prefixEnd_1758849 200696652373309828644157 := by
  unfold tailWord_1758849
  simp only [CollatzResearch.WordTrace]
  refine ⟨64150493204997935339239601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42766995469998623559493067 64150493204997935339239601)
  ·
    refine ⟨48112869903748451504429701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64150493204997935339239601 48112869903748451504429701)
    ·
      refine ⟨9021163106952834657080569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48112869903748451504429701 9021163106952834657080569)
      ·
        refine ⟨6765872330214625992810427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9021163106952834657080569 6765872330214625992810427)
        ·
          refine ⟨10148808495321938989215641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6765872330214625992810427 10148808495321938989215641)
          ·
            refine ⟨7611606371491454241911731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10148808495321938989215641 7611606371491454241911731)
            ·
              refine ⟨11417409557237181362867597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7611606371491454241911731 11417409557237181362867597)
              ·
                refine ⟨4281528583963943011075349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11417409557237181362867597 4281528583963943011075349)
                ·
                  refine ⟨200696652373309828644157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4281528583963943011075349 200696652373309828644157)
                  ·
                    rfl

theorem cell22_1758849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 6].length) (baseStart_1758849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758849 prefixEnd_1758849 := by exact prefixLift 1758849
  have htrace : WordTrace (prefixWord ++ tailWord_1758849) baseStart_1758849 baseEnd_1758849 := by
    simpa [prefixWord, tailWord_1758849, baseEnd_1758849] using wordTrace_append hprefix tailTrace_1758849
  have hstable : (prefixWord ++ tailWord_1758849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758849).length < 2 ^ (prefixWord ++ tailWord_1758849).sum := by decide
  have hdescent : baseEnd_1758849 < baseStart_1758849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758881 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 4, 3]
def baseStart_1758881 : Nat := 118140960795 + 1758881 * 2 ^ 59
def prefixEnd_1758881 : Nat := 4983230072969 + 3 ^ 40 * 1758881 * 2
def baseEnd_1758881 : Nat := 602100911373892069132373

theorem tailTrace_1758881 : CollatzResearch.WordTrace tailWord_1758881 prefixEnd_1758881 602100911373892069132373 := by
  unfold tailWord_1758881
  simp only [CollatzResearch.WordTrace]
  refine ⟨64151660340882004804404497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42767773560588003202936331 64151660340882004804404497)
  ·
    refine ⟨48113745255661503603303373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64151660340882004804404497 48113745255661503603303373)
    ·
      refine ⟨18042654470873063851238765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48113745255661503603303373 18042654470873063851238765)
      ·
        refine ⟨6765995426577398944214537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18042654470873063851238765 6765995426577398944214537)
        ·
          refine ⟨5074496569933049208160903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6765995426577398944214537 5074496569933049208160903)
          ·
            refine ⟨7611744854899573812241355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5074496569933049208160903 7611744854899573812241355)
            ·
              refine ⟨11417617282349360718362033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7611744854899573812241355 11417617282349360718362033)
              ·
                refine ⟨8563212961762020538771525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11417617282349360718362033 8563212961762020538771525)
                ·
                  refine ⟨1605602430330378851019661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8563212961762020538771525 1605602430330378851019661)
                  ·
                    refine ⟨602100911373892069132373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1605602430330378851019661 602100911373892069132373)
                    ·
                      rfl

theorem cell22_1758881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_1758881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758881 prefixEnd_1758881 := by exact prefixLift 1758881
  have htrace : WordTrace (prefixWord ++ tailWord_1758881) baseStart_1758881 baseEnd_1758881 := by
    simpa [prefixWord, tailWord_1758881, baseEnd_1758881] using wordTrace_append hprefix tailTrace_1758881
  have hstable : (prefixWord ++ tailWord_1758881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758881).length < 2 ^ (prefixWord ++ tailWord_1758881).sum := by decide
  have hdescent : baseEnd_1758881 < baseStart_1758881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758926 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 5, 3]
def baseStart_1758926 : Nat := 118140960795 + 1758926 * 2 ^ 59
def prefixEnd_1758926 : Nat := 4983230072969 + 3 ^ 40 * 1758926 * 2
def baseEnd_1758926 : Nat := 602116315793526951757235

theorem tailTrace_1758926 : CollatzResearch.WordTrace tailWord_1758926 prefixEnd_1758926 602116315793526951757235 := by
  unfold tailWord_1758926
  simp only [CollatzResearch.WordTrace]
  refine ⟨8019162703214872186224079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42768867750479318326528421 8019162703214872186224079)
  ·
    refine ⟨12028744054822308279336119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8019162703214872186224079 12028744054822308279336119)
    ·
      refine ⟨18043116082233462419004179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12028744054822308279336119 18043116082233462419004179)
      ·
        refine ⟨27064674123350193628506269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18043116082233462419004179 27064674123350193628506269)
        ·
          refine ⟨10149252796256322610689851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27064674123350193628506269 10149252796256322610689851)
          ·
            refine ⟨15223879194384483916034777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10149252796256322610689851 15223879194384483916034777)
            ·
              refine ⟨11417909395788362937026083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15223879194384483916034777 11417909395788362937026083)
              ·
                refine ⟨17126864093682544405539125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11417909395788362937026083 17126864093682544405539125)
                ·
                  refine ⟨1605643508782738538019293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17126864093682544405539125 1605643508782738538019293)
                  ·
                    refine ⟨602116315793526951757235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1605643508782738538019293 602116315793526951757235)
                    ·
                      rfl

theorem cell22_1758926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_1758926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758926 prefixEnd_1758926 := by exact prefixLift 1758926
  have htrace : WordTrace (prefixWord ++ tailWord_1758926) baseStart_1758926 baseEnd_1758926 := by
    simpa [prefixWord, tailWord_1758926, baseEnd_1758926] using wordTrace_append hprefix tailTrace_1758926
  have hstable : (prefixWord ++ tailWord_1758926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758926).length < 2 ^ (prefixWord ++ tailWord_1758926).sum := by decide
  have hdescent : baseEnd_1758926 < baseStart_1758926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758943 : List Nat := [1, 1, 2, 3, 2, 2, 2, 5, 1, 3]
def baseStart_1758943 : Nat := 118140960795 + 1758943 * 2 ^ 59
def prefixEnd_1758943 : Nat := 4983230072969 + 3 ^ 40 * 1758943 * 2
def baseEnd_1758943 : Nat := 602122135240944574082183

theorem tailTrace_1758943 : CollatzResearch.WordTrace tailWord_1758943 prefixEnd_1758943 602122135240944574082183 := by
  unfold tailWord_1758943
  simp only [CollatzResearch.WordTrace]
  refine ⟨64153921666657389393161483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42769281111104926262107655 64153921666657389393161483)
  ·
    refine ⟨96230882499986084089742225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64153921666657389393161483 96230882499986084089742225)
    ·
      refine ⟨72173161874989563067306669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96230882499986084089742225 72173161874989563067306669)
      ·
        refine ⟨27064935703121086150240001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72173161874989563067306669 27064935703121086150240001)
        ·
          refine ⟨20298701777340814612680001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27064935703121086150240001 20298701777340814612680001)
          ·
            refine ⟨15224026333005610959510001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20298701777340814612680001 15224026333005610959510001)
            ·
              refine ⟨11418019749754208219632501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15224026333005610959510001 11418019749754208219632501)
              ·
                refine ⟨1070439351539457020590547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11418019749754208219632501 1070439351539457020590547)
                ·
                  refine ⟨1605659027309185530885821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1070439351539457020590547 1605659027309185530885821)
                  ·
                    refine ⟨602122135240944574082183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1605659027309185530885821 602122135240944574082183)
                    ·
                      rfl

theorem cell22_1758943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 1, 3].length) (baseStart_1758943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758943 prefixEnd_1758943 := by exact prefixLift 1758943
  have htrace : WordTrace (prefixWord ++ tailWord_1758943) baseStart_1758943 baseEnd_1758943 := by
    simpa [prefixWord, tailWord_1758943, baseEnd_1758943] using wordTrace_append hprefix tailTrace_1758943
  have hstable : (prefixWord ++ tailWord_1758943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758943).length < 2 ^ (prefixWord ++ tailWord_1758943).sum := by decide
  have hdescent : baseEnd_1758943 < baseStart_1758943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758986 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 3, 4]
def baseStart_1758986 : Nat := 118140960795 + 1758986 * 2 ^ 59
def prefixEnd_1758986 : Nat := 4983230072969 + 3 ^ 40 * 1758986 * 2
def baseEnd_1758986 : Nat := 602136855019706795257051

theorem tailTrace_1758986 : CollatzResearch.WordTrace tailWord_1758986 prefixEnd_1758986 602136855019706795257051 := by
  unfold tailWord_1758986
  simp only [CollatzResearch.WordTrace]
  refine ⟨16038872501375401934244203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42770326670334405157984541 16038872501375401934244203)
  ·
    refine ⟨24058308752063102901366305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16038872501375401934244203 24058308752063102901366305)
    ·
      refine ⟨18043731564047327176024729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24058308752063102901366305 18043731564047327176024729)
      ·
        refine ⟨13532798673035495382018547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18043731564047327176024729 13532798673035495382018547)
        ·
          refine ⟨20299198009553243073027821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13532798673035495382018547 20299198009553243073027821)
          ·
            refine ⟨7612199253582466152385433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20299198009553243073027821 7612199253582466152385433)
            ·
              refine ⟨5709149440186849614289075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7612199253582466152385433 5709149440186849614289075)
              ·
                refine ⟨8563724160280274421433613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5709149440186849614289075 8563724160280274421433613)
                ·
                  refine ⟨3211396560105102908037605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8563724160280274421433613 3211396560105102908037605)
                  ·
                    refine ⟨602136855019706795257051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3211396560105102908037605 602136855019706795257051)
                    ·
                      rfl

theorem cell22_1758986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_1758986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1758986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1758986 prefixEnd_1758986 := by exact prefixLift 1758986
  have htrace : WordTrace (prefixWord ++ tailWord_1758986) baseStart_1758986 baseEnd_1758986 := by
    simpa [prefixWord, tailWord_1758986, baseEnd_1758986] using wordTrace_append hprefix tailTrace_1758986
  have hstable : (prefixWord ++ tailWord_1758986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758986).length < 2 ^ (prefixWord ++ tailWord_1758986).sum := by decide
  have hdescent : baseEnd_1758986 < baseStart_1758986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759052 : List Nat := [2, 2, 1, 3, 5, 1, 1, 3, 4]
def baseStart_1759052 : Nat := 118140960795 + 1759052 * 2 ^ 59
def prefixEnd_1759052 : Nat := 4983230072969 + 3 ^ 40 * 1759052 * 2
def baseEnd_1759052 : Nat := 200719816056168207702283

theorem tailTrace_1759052 : CollatzResearch.WordTrace tailWord_1759052 prefixEnd_1759052 200719816056168207702283 := by
  unfold tailWord_1759052
  simp only [CollatzResearch.WordTrace]
  refine ⟨32078948611631250504439705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42771931482175000672586273 32078948611631250504439705)
  ·
    refine ⟨24059211458723437878329779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32078948611631250504439705 24059211458723437878329779)
    ·
      refine ⟨36088817188085156817494669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24059211458723437878329779 36088817188085156817494669)
      ·
        refine ⟨13533306445531933806560501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36088817188085156817494669 13533306445531933806560501)
        ·
          refine ⟨1268747479268618794365047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13533306445531933806560501 1268747479268618794365047)
          ·
            refine ⟨1903121218902928191547571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268747479268618794365047 1903121218902928191547571)
            ·
              refine ⟨2854681828354392287321357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1903121218902928191547571 2854681828354392287321357)
              ·
                refine ⟨1070505685632897107745509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2854681828354392287321357 1070505685632897107745509)
                ·
                  refine ⟨200719816056168207702283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1070505685632897107745509 200719816056168207702283)
                  ·
                    rfl

theorem cell22_1759052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 4].length) (baseStart_1759052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759052 prefixEnd_1759052 := by exact prefixLift 1759052
  have htrace : WordTrace (prefixWord ++ tailWord_1759052) baseStart_1759052 baseEnd_1759052 := by
    simpa [prefixWord, tailWord_1759052, baseEnd_1759052] using wordTrace_append hprefix tailTrace_1759052
  have hstable : (prefixWord ++ tailWord_1759052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759052).length < 2 ^ (prefixWord ++ tailWord_1759052).sum := by decide
  have hdescent : baseEnd_1759052 < baseStart_1759052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759059 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 3, 8]
def baseStart_1759059 : Nat := 118140960795 + 1759059 * 2 ^ 59
def prefixEnd_1759059 : Nat := 4983230072969 + 3 ^ 40 * 1759059 * 2
def baseEnd_1759059 : Nat := 602161844411558938181827

theorem tailTrace_1759059 : CollatzResearch.WordTrace tailWord_1759059 prefixEnd_1759059 602161844411558938181827 := by
  unfold tailWord_1759059
  simp only [CollatzResearch.WordTrace]
  refine ⟨64158152534237141204384231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42772101689491427469589487 64158152534237141204384231)
  ·
    refine ⟨96237228801355711806576347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64158152534237141204384231 96237228801355711806576347)
    ·
      refine ⟨144355843202033567709864521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96237228801355711806576347 144355843202033567709864521)
      ·
        refine ⟨108266882401525175782398391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144355843202033567709864521 108266882401525175782398391)
        ·
          refine ⟨162400323602287763673597587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108266882401525175782398391 162400323602287763673597587)
          ·
            refine ⟨243600485403431645510396381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162400323602287763673597587 243600485403431645510396381)
            ·
              refine ⟨91350182026286867066398643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243600485403431645510396381 91350182026286867066398643)
              ·
                refine ⟨137025273039430300599597965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91350182026286867066398643 137025273039430300599597965)
                ·
                  refine ⟨51384477389786362724849237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137025273039430300599597965 51384477389786362724849237)
                  ·
                    refine ⟨602161844411558938181827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51384477389786362724849237 602161844411558938181827)
                    ·
                      rfl

theorem cell22_1759059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 8].length) (baseStart_1759059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759059 prefixEnd_1759059 := by exact prefixLift 1759059
  have htrace : WordTrace (prefixWord ++ tailWord_1759059) baseStart_1759059 baseEnd_1759059 := by
    simpa [prefixWord, tailWord_1759059, baseEnd_1759059] using wordTrace_append hprefix tailTrace_1759059
  have hstable : (prefixWord ++ tailWord_1759059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759059).length < 2 ^ (prefixWord ++ tailWord_1759059).sum := by decide
  have hdescent : baseEnd_1759059 < baseStart_1759059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759063 : List Nat := [1, 1, 3, 2, 6, 1, 8]
def baseStart_1759063 : Nat := 118140960795 + 1759063 * 2 ^ 59
def prefixEnd_1759063 : Nat := 4983230072969 + 3 ^ 40 * 1759063 * 2
def baseEnd_1759063 : Nat := 22302341247900157817845

theorem tailTrace_1759063 : CollatzResearch.WordTrace tailWord_1759063 prefixEnd_1759063 22302341247900157817845 := by
  unfold tailWord_1759063
  simp only [CollatzResearch.WordTrace]
  refine ⟨64158298426222649887529843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42772198950815099925019895 64158298426222649887529843)
  ·
    refine ⟨96237447639333974831294765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64158298426222649887529843 96237447639333974831294765)
    ·
      refine ⟨36089042864750240561735537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96237447639333974831294765 36089042864750240561735537)
      ·
        refine ⟨27066782148562680421301653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36089042864750240561735537 27066782148562680421301653)
        ·
          refine ⟨1268755413213875644748515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27066782148562680421301653 1268755413213875644748515)
          ·
            refine ⟨1903133119820813467122773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268755413213875644748515 1903133119820813467122773)
            ·
              refine ⟨22302341247900157817845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1903133119820813467122773 22302341247900157817845)
              ·
                rfl

theorem cell22_1759063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 8].length) (baseStart_1759063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759063 prefixEnd_1759063 := by exact prefixLift 1759063
  have htrace : WordTrace (prefixWord ++ tailWord_1759063) baseStart_1759063 baseEnd_1759063 := by
    simpa [prefixWord, tailWord_1759063, baseEnd_1759063] using wordTrace_append hprefix tailTrace_1759063
  have hstable : (prefixWord ++ tailWord_1759063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759063).length < 2 ^ (prefixWord ++ tailWord_1759063).sum := by decide
  have hdescent : baseEnd_1759063 < baseStart_1759063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759136 : List Nat := [2, 1, 1, 4, 1, 1, 1, 5, 6]
def baseStart_1759136 : Nat := 118140960795 + 1759136 * 2 ^ 59
def prefixEnd_1759136 : Nat := 4983230072969 + 3 ^ 40 * 1759136 * 2
def baseEnd_1759136 : Nat := 200729401028385468002197

theorem tailTrace_1759136 : CollatzResearch.WordTrace tailWord_1759136 prefixEnd_1759136 200729401028385468002197 := by
  unfold tailWord_1759136
  simp only [CollatzResearch.WordTrace]
  refine ⟨32080480477479091677468631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42773973969972122236624841 32080480477479091677468631)
  ·
    refine ⟨48120720716218637516202947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32080480477479091677468631 48120720716218637516202947)
    ·
      refine ⟨72181081074327956274304421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48120720716218637516202947 72181081074327956274304421)
      ·
        refine ⟨13533952701436491801432079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72181081074327956274304421 13533952701436491801432079)
        ·
          refine ⟨20300929052154737702148119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13533952701436491801432079 20300929052154737702148119)
          ·
            refine ⟨30451393578232106553222179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20300929052154737702148119 30451393578232106553222179)
            ·
              refine ⟨45677090367348159829833269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30451393578232106553222179 45677090367348159829833269)
              ·
                refine ⟨4282227221938889984046869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45677090367348159829833269 4282227221938889984046869)
                ·
                  refine ⟨200729401028385468002197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4282227221938889984046869 200729401028385468002197)
                  ·
                    rfl

theorem cell22_1759136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 6].length) (baseStart_1759136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759136 prefixEnd_1759136 := by exact prefixLift 1759136
  have htrace : WordTrace (prefixWord ++ tailWord_1759136) baseStart_1759136 baseEnd_1759136 := by
    simpa [prefixWord, tailWord_1759136, baseEnd_1759136] using wordTrace_append hprefix tailTrace_1759136
  have hstable : (prefixWord ++ tailWord_1759136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759136).length < 2 ^ (prefixWord ++ tailWord_1759136).sum := by decide
  have hdescent : baseEnd_1759136 < baseStart_1759136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759153 : List Nat := [1, 2, 2, 4, 2, 2, 1, 2, 6]
def baseStart_1759153 : Nat := 118140960795 + 1759153 * 2 ^ 59
def prefixEnd_1759153 : Nat := 4983230072969 + 3 ^ 40 * 1759153 * 2
def baseEnd_1759153 : Nat := 200731340844191342110513

theorem tailTrace_1759153 : CollatzResearch.WordTrace tailWord_1759153 prefixEnd_1759153 200731340844191342110513 := by
  unfold tailWord_1759153
  simp only [CollatzResearch.WordTrace]
  refine ⟨64161580995896595258306113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42774387330597730172204075 64161580995896595258306113)
  ·
    refine ⟨48121185746922446443729585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64161580995896595258306113 48121185746922446443729585)
    ·
      refine ⟨36090889310191834832797189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48121185746922446443729585 36090889310191834832797189)
      ·
        refine ⟨6767041745660969031149473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36090889310191834832797189 6767041745660969031149473)
        ·
          refine ⟨5075281309245726773362105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6767041745660969031149473 5075281309245726773362105)
          ·
            refine ⟨3806460981934295080021579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5075281309245726773362105 3806460981934295080021579)
            ·
              refine ⟨5709691472901442620032369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3806460981934295080021579 5709691472901442620032369)
              ·
                refine ⟨4282268604676081965024277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5709691472901442620032369 4282268604676081965024277)
                ·
                  refine ⟨200731340844191342110513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4282268604676081965024277 200731340844191342110513)
                  ·
                    rfl

theorem cell22_1759153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 6].length) (baseStart_1759153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759153 prefixEnd_1759153 := by exact prefixLift 1759153
  have htrace : WordTrace (prefixWord ++ tailWord_1759153) baseStart_1759153 baseEnd_1759153 := by
    simpa [prefixWord, tailWord_1759153, baseEnd_1759153] using wordTrace_append hprefix tailTrace_1759153
  have hstable : (prefixWord ++ tailWord_1759153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759153).length < 2 ^ (prefixWord ++ tailWord_1759153).sum := by decide
  have hdescent : baseEnd_1759153 < baseStart_1759153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759168 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 4, 3]
def baseStart_1759168 : Nat := 118140960795 + 1759168 * 2 ^ 59
def prefixEnd_1759168 : Nat := 4983230072969 + 3 ^ 40 * 1759168 * 2
def baseEnd_1759168 : Nat := 602199157339118987206493

theorem tailTrace_1759168 : CollatzResearch.WordTrace tailWord_1759168 prefixEnd_1759168 602199157339118987206493 := by
  unfold tailWord_1759168
  simp only [CollatzResearch.WordTrace]
  refine ⟨32081064045421126410051079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42774752060561501880068105 32081064045421126410051079)
  ·
    refine ⟨48121596068131689615076619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32081064045421126410051079 48121596068131689615076619)
    ·
      refine ⟨72182394102197534422614929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48121596068131689615076619 72182394102197534422614929)
      ·
        refine ⟨54136795576648150816961197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72182394102197534422614929 54136795576648150816961197)
        ·
          refine ⟨20301298341243056556360449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54136795576648150816961197 20301298341243056556360449)
          ·
            refine ⟨15225973755932292417270337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20301298341243056556360449 15225973755932292417270337)
            ·
              refine ⟨11419480316949219312952753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15225973755932292417270337 11419480316949219312952753)
              ·
                refine ⟨8564610237711914484714565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11419480316949219312952753 8564610237711914484714565)
                ·
                  refine ⟨1605864419570983965883981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8564610237711914484714565 1605864419570983965883981)
                  ·
                    refine ⟨602199157339118987206493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1605864419570983965883981 602199157339118987206493)
                    ·
                      rfl

theorem cell22_1759168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 4, 3].length) (baseStart_1759168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759168 prefixEnd_1759168 := by exact prefixLift 1759168
  have htrace : WordTrace (prefixWord ++ tailWord_1759168) baseStart_1759168 baseEnd_1759168 := by
    simpa [prefixWord, tailWord_1759168, baseEnd_1759168] using wordTrace_append hprefix tailTrace_1759168
  have hstable : (prefixWord ++ tailWord_1759168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759168).length < 2 ^ (prefixWord ++ tailWord_1759168).sum := by decide
  have hdescent : baseEnd_1759168 < baseStart_1759168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759211 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 2, 6]
def baseStart_1759211 : Nat := 118140960795 + 1759211 * 2 ^ 59
def prefixEnd_1759211 : Nat := 4983230072969 + 3 ^ 40 * 1759211 * 2
def baseEnd_1759211 : Nat := 602213877117881208381361

theorem tailTrace_1759211 : CollatzResearch.WordTrace tailWord_1759211 prefixEnd_1759211 602213877117881208381361 := by
  unfold tailWord_1759211
  simp only [CollatzResearch.WordTrace]
  refine ⟨64163696429686471163917487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42775797619790980775944991 64163696429686471163917487)
  ·
    refine ⟨96245544644529706745876231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64163696429686471163917487 96245544644529706745876231)
    ·
      refine ⟨144368316966794560118814347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96245544644529706745876231 144368316966794560118814347)
      ·
        refine ⟨216552475450191840178221521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144368316966794560118814347 216552475450191840178221521)
        ·
          refine ⟨162414356587643880133666141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216552475450191840178221521 162414356587643880133666141)
          ·
            refine ⟨60905383720366455050124803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162414356587643880133666141 60905383720366455050124803)
            ·
              refine ⟨91358075580549682575187205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60905383720366455050124803 91358075580549682575187205)
              ·
                refine ⟨17129639171353065482847601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91358075580549682575187205 17129639171353065482847601)
                ·
                  refine ⟨12847229378514799112135701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17129639171353065482847601 12847229378514799112135701)
                  ·
                    refine ⟨602213877117881208381361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12847229378514799112135701 602213877117881208381361)
                    ·
                      rfl

theorem cell22_1759211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 6].length) (baseStart_1759211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759211 prefixEnd_1759211 := by exact prefixLift 1759211
  have htrace : WordTrace (prefixWord ++ tailWord_1759211) baseStart_1759211 baseEnd_1759211 := by
    simpa [prefixWord, tailWord_1759211, baseEnd_1759211] using wordTrace_append hprefix tailTrace_1759211
  have hstable : (prefixWord ++ tailWord_1759211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759211).length < 2 ^ (prefixWord ++ tailWord_1759211).sum := by decide
  have hdescent : baseEnd_1759211 < baseStart_1759211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759238 : List Nat := [6, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_1759238 : Nat := 118140960795 + 1759238 * 2 ^ 59
def prefixEnd_1759238 : Nat := 4983230072969 + 3 ^ 40 * 1759238 * 2
def baseEnd_1759238 : Nat := 200741039923220712652093

theorem tailTrace_1759238 : CollatzResearch.WordTrace tailWord_1759238 prefixEnd_1759238 200741039923220712652093 := by
  unfold tailWord_1759238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2005146287518395461723449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42776454133725769850100245 2005146287518395461723449)
  ·
    refine ⟨1503859715638796596292587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2005146287518395461723449 1503859715638796596292587)
    ·
      refine ⟨2255789573458194894438881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1503859715638796596292587 2255789573458194894438881)
      ·
        refine ⟨1691842180093646170829161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2255789573458194894438881 1691842180093646170829161)
        ·
          refine ⟨1268881635070234628121871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1691842180093646170829161 1268881635070234628121871)
          ·
            refine ⟨1903322452605351942182807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268881635070234628121871 1903322452605351942182807)
            ·
              refine ⟨2854983678908027913274211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1903322452605351942182807 2854983678908027913274211)
              ·
                refine ⟨4282475518362041869911317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2854983678908027913274211 4282475518362041869911317)
                ·
                  refine ⟨200741039923220712652093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4282475518362041869911317 200741039923220712652093)
                  ·
                    rfl

theorem cell22_1759238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_1759238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759238 prefixEnd_1759238 := by exact prefixLift 1759238
  have htrace : WordTrace (prefixWord ++ tailWord_1759238) baseStart_1759238 baseEnd_1759238 := by
    simpa [prefixWord, tailWord_1759238, baseEnd_1759238] using wordTrace_append hprefix tailTrace_1759238
  have hstable : (prefixWord ++ tailWord_1759238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759238).length < 2 ^ (prefixWord ++ tailWord_1759238).sum := by decide
  have hdescent : baseEnd_1759238 < baseStart_1759238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759243 : List Nat := [1, 1, 1, 1, 6, 1, 2, 4, 5]
def baseStart_1759243 : Nat := 118140960795 + 1759243 * 2 ^ 59
def prefixEnd_1759243 : Nat := 4983230072969 + 3 ^ 40 * 1759243 * 2
def baseEnd_1759243 : Nat := 200741610457281263860421

theorem tailTrace_1759243 : CollatzResearch.WordTrace tailWord_1759243 prefixEnd_1759243 200741610457281263860421 := by
  unfold tailWord_1759243
  simp only [CollatzResearch.WordTrace]
  refine ⟨64164863565570540629082383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42776575710380360419388255 64164863565570540629082383)
  ·
    refine ⟨96247295348355810943623575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64164863565570540629082383 96247295348355810943623575)
    ·
      refine ⟨144370943022533716415435363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96247295348355810943623575 144370943022533716415435363)
      ·
        refine ⟨216556414533800574623153045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144370943022533716415435363 216556414533800574623153045)
        ·
          refine ⟨10151081931271901935460299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 216556414533800574623153045 10151081931271901935460299)
          ·
            refine ⟨15226622896907852903190449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10151081931271901935460299 15226622896907852903190449)
            ·
              refine ⟨11419967172680889677392837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15226622896907852903190449 11419967172680889677392837)
              ·
                refine ⟨2141243844877666814511157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11419967172680889677392837 2141243844877666814511157)
                ·
                  refine ⟨200741610457281263860421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2141243844877666814511157 200741610457281263860421)
                  ·
                    rfl

theorem cell22_1759243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 5].length) (baseStart_1759243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759243 prefixEnd_1759243 := by exact prefixLift 1759243
  have htrace : WordTrace (prefixWord ++ tailWord_1759243) baseStart_1759243 baseEnd_1759243 := by
    simpa [prefixWord, tailWord_1759243, baseEnd_1759243] using wordTrace_append hprefix tailTrace_1759243
  have hstable : (prefixWord ++ tailWord_1759243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759243).length < 2 ^ (prefixWord ++ tailWord_1759243).sum := by decide
  have hdescent : baseEnd_1759243 < baseStart_1759243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759260 : List Nat := [2, 2, 3, 1, 3, 2, 1, 3, 5]
def baseStart_1759260 : Nat := 118140960795 + 1759260 * 2 ^ 59
def prefixEnd_1759260 : Nat := 4983230072969 + 3 ^ 40 * 1759260 * 2
def baseEnd_1759260 : Nat := 200743550273087137968737

theorem tailTrace_1759260 : CollatzResearch.WordTrace tailWord_1759260 prefixEnd_1759260 200743550273087137968737 := by
  unfold tailWord_1759260
  simp only [CollatzResearch.WordTrace]
  refine ⟨32082741803254476266225617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42776989071005968354967489 32082741803254476266225617)
  ·
    refine ⟨24062056352440857199669213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32082741803254476266225617 24062056352440857199669213)
    ·
      refine ⟨9023271132165321449875955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24062056352440857199669213 9023271132165321449875955)
      ·
        refine ⟨13534906698247982174813933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9023271132165321449875955 13534906698247982174813933)
        ·
          refine ⟨5075590011842993315555225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13534906698247982174813933 5075590011842993315555225)
          ·
            refine ⟨3806692508882244986666419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5075590011842993315555225 3806692508882244986666419)
            ·
              refine ⟨5710038763323367479999629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3806692508882244986666419 5710038763323367479999629)
              ·
                refine ⟨2141264536246262804999861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5710038763323367479999629 2141264536246262804999861)
                ·
                  refine ⟨200743550273087137968737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2141264536246262804999861 200743550273087137968737)
                  ·
                    rfl

theorem cell22_1759260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_1759260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759260 prefixEnd_1759260 := by exact prefixLift 1759260
  have htrace : WordTrace (prefixWord ++ tailWord_1759260) baseStart_1759260 baseEnd_1759260 := by
    simpa [prefixWord, tailWord_1759260, baseEnd_1759260] using wordTrace_append hprefix tailTrace_1759260
  have hstable : (prefixWord ++ tailWord_1759260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759260).length < 2 ^ (prefixWord ++ tailWord_1759260).sum := by decide
  have hdescent : baseEnd_1759260 < baseStart_1759260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759303 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 3, 5]
def baseStart_1759303 : Nat := 118140960795 + 1759303 * 2 ^ 59
def prefixEnd_1759303 : Nat := 4983230072969 + 3 ^ 40 * 1759303 * 2
def baseEnd_1759303 : Nat := 602245370598023635081079

theorem tailTrace_1759303 : CollatzResearch.WordTrace tailWord_1759303 prefixEnd_1759303 602245370598023635081079 := by
  unfold tailWord_1759303
  simp only [CollatzResearch.WordTrace]
  refine ⟨64167051945353170876266563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42778034630235447250844375 64167051945353170876266563)
  ·
    refine ⟨96250577918029756314399845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64167051945353170876266563 96250577918029756314399845)
    ·
      refine ⟨18046983359630579308949971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96250577918029756314399845 18046983359630579308949971)
      ·
        refine ⟨27070475039445868963424957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18046983359630579308949971 27070475039445868963424957)
        ·
          refine ⟨10151428139792200861284359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27070475039445868963424957 10151428139792200861284359)
          ·
            refine ⟨15227142209688301291926539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10151428139792200861284359 15227142209688301291926539)
            ·
              refine ⟨22840713314532451937889809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15227142209688301291926539 22840713314532451937889809)
              ·
                refine ⟨17130534985899338953417357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22840713314532451937889809 17130534985899338953417357)
                ·
                  refine ⟨6423950619712252107531509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17130534985899338953417357 6423950619712252107531509)
                  ·
                    refine ⟨602245370598023635081079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6423950619712252107531509 602245370598023635081079)
                    ·
                      rfl

theorem cell22_1759303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_1759303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759303 prefixEnd_1759303 := by exact prefixLift 1759303
  have htrace : WordTrace (prefixWord ++ tailWord_1759303) baseStart_1759303 baseEnd_1759303 := by
    simpa [prefixWord, tailWord_1759303, baseEnd_1759303] using wordTrace_append hprefix tailTrace_1759303
  have hstable : (prefixWord ++ tailWord_1759303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759303).length < 2 ^ (prefixWord ++ tailWord_1759303).sum := by decide
  have hdescent : baseEnd_1759303 < baseStart_1759303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759305 : List Nat := [1, 2, 1, 1, 2, 2, 5, 4, 4]
def baseStart_1759305 : Nat := 118140960795 + 1759305 * 2 ^ 59
def prefixEnd_1759305 : Nat := 4983230072969 + 3 ^ 40 * 1759305 * 2
def baseEnd_1759305 : Nat := 200748685079632098843691

theorem tailTrace_1759305 : CollatzResearch.WordTrace tailWord_1759305 prefixEnd_1759305 200748685079632098843691 := by
  unfold tailWord_1759305
  simp only [CollatzResearch.WordTrace]
  refine ⟨64167124891345925217839369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42778083260897283478559579 64167124891345925217839369)
  ·
    refine ⟨48125343668509443913379527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64167124891345925217839369 48125343668509443913379527)
    ·
      refine ⟨72188015502764165870069291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48125343668509443913379527 72188015502764165870069291)
      ·
        refine ⟨108282023254146248805103937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72188015502764165870069291 108282023254146248805103937)
        ·
          refine ⟨81211517440609686603827953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108282023254146248805103937 81211517440609686603827953)
          ·
            refine ⟨60908638080457264952870965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81211517440609686603827953 60908638080457264952870965)
            ·
              refine ⟨5710184820042868589331653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60908638080457264952870965 5710184820042868589331653)
              ·
                refine ⟨1070659653758037860499685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5710184820042868589331653 1070659653758037860499685)
                ·
                  refine ⟨200748685079632098843691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1070659653758037860499685 200748685079632098843691)
                  ·
                    rfl

theorem cell22_1759305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 4].length) (baseStart_1759305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759305 prefixEnd_1759305 := by exact prefixLift 1759305
  have htrace : WordTrace (prefixWord ++ tailWord_1759305) baseStart_1759305 baseEnd_1759305 := by
    simpa [prefixWord, tailWord_1759305, baseEnd_1759305] using wordTrace_append hprefix tailTrace_1759305
  have hstable : (prefixWord ++ tailWord_1759305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759305).length < 2 ^ (prefixWord ++ tailWord_1759305).sum := by decide
  have hdescent : baseEnd_1759305 < baseStart_1759305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759320 : List Nat := [2, 1, 2, 2, 1, 5, 2, 1, 1, 5]
def baseStart_1759320 : Nat := 118140960795 + 1759320 * 2 ^ 59
def prefixEnd_1759320 : Nat := 4983230072969 + 3 ^ 40 * 1759320 * 2
def baseEnd_1759320 : Nat := 602251190045441257406027

theorem tailTrace_1759320 : CollatzResearch.WordTrace tailWord_1759320 prefixEnd_1759320 602251190045441257406027 := by
  unfold tailWord_1759320
  simp only [CollatzResearch.WordTrace]
  refine ⟨32083835993145791389817707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42778447990861055186423609 32083835993145791389817707)
  ·
    refine ⟨48125753989718687084726561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32083835993145791389817707 48125753989718687084726561)
    ·
      refine ⟨36094315492289015313544921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48125753989718687084726561 36094315492289015313544921)
      ·
        refine ⟨27070736619216761485158691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36094315492289015313544921 27070736619216761485158691)
        ·
          refine ⟨40606104928825142227738037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27070736619216761485158691 40606104928825142227738037)
          ·
            refine ⟨3806822337077357083850441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40606104928825142227738037 3806822337077357083850441)
            ·
              refine ⟨2855116752808017812887831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3806822337077357083850441 2855116752808017812887831)
              ·
                refine ⟨4282675129212026719331747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855116752808017812887831 4282675129212026719331747)
                ·
                  refine ⟨6424012693818040078997621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4282675129212026719331747 6424012693818040078997621)
                  ·
                    refine ⟨602251190045441257406027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6424012693818040078997621 602251190045441257406027)
                    ·
                      rfl

theorem cell22_1759320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_1759320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759320 prefixEnd_1759320 := by exact prefixLift 1759320
  have htrace : WordTrace (prefixWord ++ tailWord_1759320) baseStart_1759320 baseEnd_1759320 := by
    simpa [prefixWord, tailWord_1759320, baseEnd_1759320] using wordTrace_append hprefix tailTrace_1759320
  have hstable : (prefixWord ++ tailWord_1759320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759320).length < 2 ^ (prefixWord ++ tailWord_1759320).sum := by decide
  have hdescent : baseEnd_1759320 < baseStart_1759320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759350 : List Nat := [5, 1, 1, 2, 1, 3, 9]
def baseStart_1759350 : Nat := 118140960795 + 1759350 * 2 ^ 59
def prefixEnd_1759350 : Nat := 4983230072969 + 3 ^ 40 * 1759350 * 2
def baseEnd_1759350 : Nat := 22305979987353006635405

theorem tailTrace_1759350 : CollatzResearch.WordTrace tailWord_1759350 prefixEnd_1759350 22305979987353006635405 := by
  unfold tailWord_1759350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4010547886011431118951719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42779177450788598602151669 4010547886011431118951719)
  ·
    refine ⟨6015821829017146678427579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4010547886011431118951719 6015821829017146678427579)
    ·
      refine ⟨9023732743525720017641369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6015821829017146678427579 9023732743525720017641369)
      ·
        refine ⟨6767799557644290013231027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9023732743525720017641369 6767799557644290013231027)
        ·
          refine ⟨10151699336466435019846541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6767799557644290013231027 10151699336466435019846541)
          ·
            refine ⟨3806887251174913132442453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10151699336466435019846541 3806887251174913132442453)
            ·
              refine ⟨22305979987353006635405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3806887251174913132442453 22305979987353006635405)
              ·
                rfl

theorem cell22_1759350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 9].length) (baseStart_1759350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759350 prefixEnd_1759350 := by exact prefixLift 1759350
  have htrace : WordTrace (prefixWord ++ tailWord_1759350) baseStart_1759350 baseEnd_1759350 := by
    simpa [prefixWord, tailWord_1759350, baseEnd_1759350] using wordTrace_append hprefix tailTrace_1759350
  have hstable : (prefixWord ++ tailWord_1759350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759350).length < 2 ^ (prefixWord ++ tailWord_1759350).sum := by decide
  have hdescent : baseEnd_1759350 < baseStart_1759350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759384 : List Nat := [2, 1, 2, 4, 4, 1, 2, 6]
def baseStart_1759384 : Nat := 118140960795 + 1759384 * 2 ^ 59
def prefixEnd_1759384 : Nat := 4983230072969 + 3 ^ 40 * 1759384 * 2
def baseEnd_1759384 : Nat := 66919233172596269311759

theorem tailTrace_1759384 : CollatzResearch.WordTrace tailWord_1759384 prefixEnd_1759384 66919233172596269311759 := by
  unfold tailWord_1759384
  simp only [CollatzResearch.WordTrace]
  refine ⟨32085003129029860854982603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42780004172039814473310137 32085003129029860854982603)
  ·
    refine ⟨48127504693544791282473905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32085003129029860854982603 48127504693544791282473905)
    ·
      refine ⟨36095628520158593461855429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48127504693544791282473905 36095628520158593461855429)
      ·
        refine ⟨6767930347529736274097893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36095628520158593461855429 6767930347529736274097893)
        ·
          refine ⟨1268986940161825551393355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6767930347529736274097893 1268986940161825551393355)
          ·
            refine ⟨1903480410242738327090033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268986940161825551393355 1903480410242738327090033)
            ·
              refine ⟨1427610307682053745317525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1903480410242738327090033 1427610307682053745317525)
              ·
                refine ⟨66919233172596269311759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1427610307682053745317525 66919233172596269311759)
                ·
                  rfl

theorem cell22_1759384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 6].length) (baseStart_1759384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759384 prefixEnd_1759384 := by exact prefixLift 1759384
  have htrace : WordTrace (prefixWord ++ tailWord_1759384) baseStart_1759384 baseEnd_1759384 := by
    simpa [prefixWord, tailWord_1759384, baseEnd_1759384] using wordTrace_append hprefix tailTrace_1759384
  have hstable : (prefixWord ++ tailWord_1759384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759384).length < 2 ^ (prefixWord ++ tailWord_1759384).sum := by decide
  have hdescent : baseEnd_1759384 < baseStart_1759384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759442 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 3, 4]
def baseStart_1759442 : Nat := 118140960795 + 1759442 * 2 ^ 59
def prefixEnd_1759442 : Nat := 4983230072969 + 3 ^ 40 * 1759442 * 2
def baseEnd_1759442 : Nat := 602292953138673605855653

theorem tailTrace_1759442 : CollatzResearch.WordTrace tailWord_1759442 prefixEnd_1759442 602292953138673605855653 := by
  unfold tailWord_1759442
  simp only [CollatzResearch.WordTrace]
  refine ⟨16043030422962399403894145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42781414461233065077051053 16043030422962399403894145)
  ·
    refine ⟨12032272817221799552920609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16043030422962399403894145 12032272817221799552920609)
    ·
      refine ⟨9024204612916349664690457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12032272817221799552920609 9024204612916349664690457)
      ·
        refine ⟨6768153459687262248517843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9024204612916349664690457 6768153459687262248517843)
        ·
          refine ⟨10152230189530893372776765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6768153459687262248517843 10152230189530893372776765)
          ·
            refine ⟨3807086321074085014791287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10152230189530893372776765 3807086321074085014791287)
            ·
              refine ⟨5710629481611127522186931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3807086321074085014791287 5710629481611127522186931)
              ·
                refine ⟨8565944222416691283280397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5710629481611127522186931 8565944222416691283280397)
                ·
                  refine ⟨3212229083406259231230149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8565944222416691283280397 3212229083406259231230149)
                  ·
                    refine ⟨602292953138673605855653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3212229083406259231230149 602292953138673605855653)
                    ·
                      rfl

theorem cell22_1759442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_1759442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759442 prefixEnd_1759442 := by exact prefixLift 1759442
  have htrace : WordTrace (prefixWord ++ tailWord_1759442) baseStart_1759442 baseEnd_1759442 := by
    simpa [prefixWord, tailWord_1759442, baseEnd_1759442] using wordTrace_append hprefix tailTrace_1759442
  have hstable : (prefixWord ++ tailWord_1759442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759442).length < 2 ^ (prefixWord ++ tailWord_1759442).sum := by decide
  have hdescent : baseEnd_1759442 < baseStart_1759442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759457 : List Nat := [1, 2, 3, 1, 3, 1, 2, 5, 4]
def baseStart_1759457 : Nat := 118140960795 + 1759457 * 2 ^ 59
def prefixEnd_1759457 : Nat := 4983230072969 + 3 ^ 40 * 1759457 * 2
def baseEnd_1759457 : Nat := 200766029315072855576869

theorem tailTrace_1759457 : CollatzResearch.WordTrace tailWord_1759457 prefixEnd_1759457 200766029315072855576869 := by
  unfold tailWord_1759457
  simp only [CollatzResearch.WordTrace]
  refine ⟨64172668786795255177372625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42781779191196836784915083 64172668786795255177372625)
  ·
    refine ⟨48129501590096441383029469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64172668786795255177372625 48129501590096441383029469)
    ·
      refine ⟨18048563096286165518636051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48129501590096441383029469 18048563096286165518636051)
      ·
        refine ⟨27072844644429248277954077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18048563096286165518636051 27072844644429248277954077)
        ·
          refine ⟨10152316741660968104232779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27072844644429248277954077 10152316741660968104232779)
          ·
            refine ⟨15228475112491452156349169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10152316741660968104232779 15228475112491452156349169)
            ·
              refine ⟨11421356334368589117261877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15228475112491452156349169 11421356334368589117261877)
              ·
                refine ⟨1070752156347055229743301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11421356334368589117261877 1070752156347055229743301)
                ·
                  refine ⟨200766029315072855576869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1070752156347055229743301 200766029315072855576869)
                  ·
                    rfl

theorem cell22_1759457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 4].length) (baseStart_1759457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759457 prefixEnd_1759457 := by exact prefixLift 1759457
  have htrace : WordTrace (prefixWord ++ tailWord_1759457) baseStart_1759457 baseEnd_1759457 := by
    simpa [prefixWord, tailWord_1759457, baseEnd_1759457] using wordTrace_append hprefix tailTrace_1759457
  have hstable : (prefixWord ++ tailWord_1759457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759457).length < 2 ^ (prefixWord ++ tailWord_1759457).sum := by decide
  have hdescent : baseEnd_1759457 < baseStart_1759457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759470 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 3, 6]
def baseStart_1759470 : Nat := 118140960795 + 1759470 * 2 ^ 59
def prefixEnd_1759470 : Nat := 4983230072969 + 3 ^ 40 * 1759470 * 2
def baseEnd_1759470 : Nat := 602302538110890866155567

theorem tailTrace_1759470 : CollatzResearch.WordTrace tailWord_1759470 prefixEnd_1759470 602302538110890866155567 := by
  unfold tailWord_1759470
  simp only [CollatzResearch.WordTrace]
  refine ⟨8021642866968519799699483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42782095290498772265063909 8021642866968519799699483)
  ·
    refine ⟨12032464300452779699549225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8021642866968519799699483 12032464300452779699549225)
    ·
      refine ⟨9024348225339584774661919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12032464300452779699549225 9024348225339584774661919)
      ·
        refine ⟨13536522338009377161992879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9024348225339584774661919 13536522338009377161992879)
        ·
          refine ⟨20304783507014065742989319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13536522338009377161992879 20304783507014065742989319)
          ·
            refine ⟨30457175260521098614483979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20304783507014065742989319 30457175260521098614483979)
            ·
              refine ⟨45685762890781647921725969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30457175260521098614483979 45685762890781647921725969)
              ·
                refine ⟨34264322168086235941294477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45685762890781647921725969 34264322168086235941294477)
                ·
                  refine ⟨12849120813032338477985429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34264322168086235941294477 12849120813032338477985429)
                  ·
                    refine ⟨602302538110890866155567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12849120813032338477985429 602302538110890866155567)
                    ·
                      rfl

theorem cell22_1759470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_1759470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759470 prefixEnd_1759470 := by exact prefixLift 1759470
  have htrace : WordTrace (prefixWord ++ tailWord_1759470) baseStart_1759470 baseEnd_1759470 := by
    simpa [prefixWord, tailWord_1759470, baseEnd_1759470] using wordTrace_append hprefix tailTrace_1759470
  have hstable : (prefixWord ++ tailWord_1759470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759470).length < 2 ^ (prefixWord ++ tailWord_1759470).sum := by decide
  have hdescent : baseEnd_1759470 < baseStart_1759470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759474 : List Nat := [3, 2, 1, 3, 2, 2, 1, 4, 4]
def baseStart_1759474 : Nat := 118140960795 + 1759474 * 2 ^ 59
def prefixEnd_1759474 : Nat := 4983230072969 + 3 ^ 40 * 1759474 * 2
def baseEnd_1759474 : Nat := 200767969130878729685185

theorem tailTrace_1759474 : CollatzResearch.WordTrace tailWord_1759474 prefixEnd_1759474 200767969130878729685185 := by
  unfold tailWord_1759474
  simp only [CollatzResearch.WordTrace]
  refine ⟨16043322206933416770185369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42782192551822444720494317 16043322206933416770185369)
  ·
    refine ⟨12032491655200062577639027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16043322206933416770185369 12032491655200062577639027)
    ·
      refine ⟨18048737482800093866458541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12032491655200062577639027 18048737482800093866458541)
      ·
        refine ⟨6768276556050035199921953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18048737482800093866458541 6768276556050035199921953)
        ·
          refine ⟨5076207417037526399941465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6768276556050035199921953 5076207417037526399941465)
          ·
            refine ⟨3807155562778144799956099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5076207417037526399941465 3807155562778144799956099)
            ·
              refine ⟨5710733344167217199934149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3807155562778144799956099 5710733344167217199934149)
              ·
                refine ⟨1070762502031353224987653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5710733344167217199934149 1070762502031353224987653)
                ·
                  refine ⟨200767969130878729685185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1070762502031353224987653 200767969130878729685185)
                  ·
                    rfl

theorem cell22_1759474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_1759474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759474 prefixEnd_1759474 := by exact prefixLift 1759474
  have htrace : WordTrace (prefixWord ++ tailWord_1759474) baseStart_1759474 baseEnd_1759474 := by
    simpa [prefixWord, tailWord_1759474, baseEnd_1759474] using wordTrace_append hprefix tailTrace_1759474
  have hstable : (prefixWord ++ tailWord_1759474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759474).length < 2 ^ (prefixWord ++ tailWord_1759474).sum := by decide
  have hdescent : baseEnd_1759474 < baseStart_1759474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759502 : List Nat := [4, 1, 1, 2, 1, 2, 5, 6]
def baseStart_1759502 : Nat := 118140960795 + 1759502 * 2 ^ 59
def prefixEnd_1759502 : Nat := 4983230072969 + 3 ^ 40 * 1759502 * 2
def baseEnd_1759502 : Nat := 66923721373872605483941

theorem tailTrace_1759502 : CollatzResearch.WordTrace tailWord_1759502 prefixEnd_1759502 66923721373872605483941 := by
  unfold tailWord_1759502
  simp only [CollatzResearch.WordTrace]
  refine ⟨8021788758954028482845095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42782873381088151908507173 8021788758954028482845095)
  ·
    refine ⟨12032683138431042724267643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8021788758954028482845095 12032683138431042724267643)
    ·
      refine ⟨18049024707646564086401465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12032683138431042724267643 18049024707646564086401465)
      ·
        refine ⟨13536768530734923064801099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18049024707646564086401465 13536768530734923064801099)
        ·
          refine ⟨20305152796102384597201649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13536768530734923064801099 20305152796102384597201649)
          ·
            refine ⟨15228864597076788447901237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20305152796102384597201649 15228864597076788447901237)
            ·
              refine ⟨1427706055975948916990741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15228864597076788447901237 1427706055975948916990741)
              ·
                refine ⟨66923721373872605483941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1427706055975948916990741 66923721373872605483941)
                ·
                  rfl

theorem cell22_1759502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_1759502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759502 prefixEnd_1759502 := by exact prefixLift 1759502
  have htrace : WordTrace (prefixWord ++ tailWord_1759502) baseStart_1759502 baseEnd_1759502 := by
    simpa [prefixWord, tailWord_1759502, baseEnd_1759502] using wordTrace_append hprefix tailTrace_1759502
  have hstable : (prefixWord ++ tailWord_1759502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759502).length < 2 ^ (prefixWord ++ tailWord_1759502).sum := by decide
  have hdescent : baseEnd_1759502 < baseStart_1759502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759607 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 6, 3]
def baseStart_1759607 : Nat := 118140960795 + 1759607 * 2 ^ 59
def prefixEnd_1759607 : Nat := 4983230072969 + 3 ^ 40 * 1759607 * 2
def baseEnd_1759607 : Nat := 602349436010668175480147

theorem tailTrace_1759607 : CollatzResearch.WordTrace tailWord_1759607 prefixEnd_1759607 602349436010668175480147 := by
  unfold tailWord_1759607
  simp only [CollatzResearch.WordTrace]
  refine ⟨64178139736251830795333075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42785426490834553863555383 64178139736251830795333075)
  ·
    refine ⟨96267209604377746192999613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64178139736251830795333075 96267209604377746192999613)
    ·
      refine ⟨36100203601641654822374855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96267209604377746192999613 36100203601641654822374855)
      ·
        refine ⟨54150305402462482233562283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36100203601641654822374855 54150305402462482233562283)
        ·
          refine ⟨81225458103693723350343425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54150305402462482233562283 81225458103693723350343425)
          ·
            refine ⟨60919093577770292512757569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81225458103693723350343425 60919093577770292512757569)
            ·
              refine ⟨45689320183327719384568177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60919093577770292512757569 45689320183327719384568177)
              ·
                refine ⟨34266990137495789538426133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45689320183327719384568177 34266990137495789538426133)
                ·
                  refine ⟨1606265162695115134613725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34266990137495789538426133 1606265162695115134613725)
                  ·
                    refine ⟨602349436010668175480147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1606265162695115134613725 602349436010668175480147)
                    ·
                      rfl

theorem cell22_1759607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 3].length) (baseStart_1759607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759607 prefixEnd_1759607 := by exact prefixLift 1759607
  have htrace : WordTrace (prefixWord ++ tailWord_1759607) baseStart_1759607 baseEnd_1759607 := by
    simpa [prefixWord, tailWord_1759607, baseEnd_1759607] using wordTrace_append hprefix tailTrace_1759607
  have hstable : (prefixWord ++ tailWord_1759607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759607).length < 2 ^ (prefixWord ++ tailWord_1759607).sum := by decide
  have hdescent : baseEnd_1759607 < baseStart_1759607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759780 : List Nat := [2, 3, 1, 5, 1, 2, 1, 2, 1, 4]
def baseStart_1759780 : Nat := 118140960795 + 1759780 * 2 ^ 59
def prefixEnd_1759780 : Nat := 4983230072969 + 3 ^ 40 * 1759780 * 2
def baseEnd_1759780 : Nat := 602408657446153390904617

theorem tailTrace_1759780 : CollatzResearch.WordTrace tailWord_1759780 prefixEnd_1759780 602408657446153390904617 := by
  unfold tailWord_1759780
  simp only [CollatzResearch.WordTrace]
  refine ⟨32092224782312540670690397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42789633043083387560920529 32092224782312540670690397)
  ·
    refine ⟨12034584293367202751508899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32092224782312540670690397 12034584293367202751508899)
    ·
      refine ⟨18051876440050804127263349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12034584293367202751508899 18051876440050804127263349)
      ·
        refine ⟨1692363416254762886930939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18051876440050804127263349 1692363416254762886930939)
        ·
          refine ⟨2538545124382144330396409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1692363416254762886930939 2538545124382144330396409)
          ·
            refine ⟨1903908843286608247797307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2538545124382144330396409 1903908843286608247797307)
            ·
              refine ⟨2855863264929912371695961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1903908843286608247797307 2855863264929912371695961)
              ·
                refine ⟨2141897448697434278771971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2855863264929912371695961 2141897448697434278771971)
                ·
                  refine ⟨3212846173046151418157957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2141897448697434278771971 3212846173046151418157957)
                  ·
                    refine ⟨602408657446153390904617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3212846173046151418157957 602408657446153390904617)
                    ·
                      rfl

theorem cell22_1759780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_1759780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759780 prefixEnd_1759780 := by exact prefixLift 1759780
  have htrace : WordTrace (prefixWord ++ tailWord_1759780) baseStart_1759780 baseEnd_1759780 := by
    simpa [prefixWord, tailWord_1759780, baseEnd_1759780] using wordTrace_append hprefix tailTrace_1759780
  have hstable : (prefixWord ++ tailWord_1759780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759780).length < 2 ^ (prefixWord ++ tailWord_1759780).sum := by decide
  have hdescent : baseEnd_1759780 < baseStart_1759780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759787 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 2, 7]
def baseStart_1759787 : Nat := 118140960795 + 1759787 * 2 ^ 59
def prefixEnd_1759787 : Nat := 4983230072969 + 3 ^ 40 * 1759787 * 2
def baseEnd_1759787 : Nat := 602411053689207705979595

theorem tailTrace_1759787 : CollatzResearch.WordTrace tailWord_1759787 prefixEnd_1759787 602411053689207705979595 := by
  unfold tailWord_1759787
  simp only [CollatzResearch.WordTrace]
  refine ⟨64184704875599721536885615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42789803250399814357923743 64184704875599721536885615)
  ·
    refine ⟨96277057313399582305328423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64184704875599721536885615 96277057313399582305328423)
    ·
      refine ⟨144415585970099373457992635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96277057313399582305328423 144415585970099373457992635)
      ·
        refine ⟨216623378955149060186988953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144415585970099373457992635 216623378955149060186988953)
        ·
          refine ⟨162467534216361795140241715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216623378955149060186988953 162467534216361795140241715)
          ·
            refine ⟨243701301324542692710362573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162467534216361795140241715 243701301324542692710362573)
            ·
              refine ⟨91387987996703509766385965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243701301324542692710362573 91387987996703509766385965)
              ·
                refine ⟨34270495498763816162394737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91387987996703509766385965 34270495498763816162394737)
                ·
                  refine ⟨25702871624072862121796053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34270495498763816162394737 25702871624072862121796053)
                  ·
                    refine ⟨602411053689207705979595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25702871624072862121796053 602411053689207705979595)
                    ·
                      rfl

theorem cell22_1759787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 7].length) (baseStart_1759787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759787 prefixEnd_1759787 := by exact prefixLift 1759787
  have htrace : WordTrace (prefixWord ++ tailWord_1759787) baseStart_1759787 baseEnd_1759787 := by
    simpa [prefixWord, tailWord_1759787, baseEnd_1759787] using wordTrace_append hprefix tailTrace_1759787
  have hstable : (prefixWord ++ tailWord_1759787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759787).length < 2 ^ (prefixWord ++ tailWord_1759787).sum := by decide
  have hdescent : baseEnd_1759787 < baseStart_1759787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759806 : List Nat := [4, 2, 1, 4, 1, 10]
def baseStart_1759806 : Nat := 118140960795 + 1759806 * 2 ^ 59
def prefixEnd_1759806 : Nat := 4983230072969 + 3 ^ 40 * 1759806 * 2
def baseEnd_1759806 : Nat := 7437253799722197404377

theorem tailTrace_1759806 : CollatzResearch.WordTrace tailWord_1759806 prefixEnd_1759806 7437253799722197404377 := by
  unfold tailWord_1759806
  simp only [CollatzResearch.WordTrace]
  refine ⟨8023174732816360972728409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42790265241687258521218181 8023174732816360972728409)
  ·
    refine ⟨6017381049612270729546307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8023174732816360972728409 6017381049612270729546307)
    ·
      refine ⟨9026071574418406094319461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6017381049612270729546307 9026071574418406094319461)
      ·
        refine ⟨1692388420203451142684899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9026071574418406094319461 1692388420203451142684899)
        ·
          refine ⟨2538582630305176714027349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1692388420203451142684899 2538582630305176714027349)
          ·
            refine ⟨7437253799722197404377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2538582630305176714027349 7437253799722197404377)
            ·
              rfl

theorem cell22_1759806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 10].length) (baseStart_1759806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759806 prefixEnd_1759806 := by exact prefixLift 1759806
  have htrace : WordTrace (prefixWord ++ tailWord_1759806) baseStart_1759806 baseEnd_1759806 := by
    simpa [prefixWord, tailWord_1759806, baseEnd_1759806] using wordTrace_append hprefix tailTrace_1759806
  have hstable : (prefixWord ++ tailWord_1759806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759806).length < 2 ^ (prefixWord ++ tailWord_1759806).sum := by decide
  have hdescent : baseEnd_1759806 < baseStart_1759806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759812 : List Nat := [2, 3, 5, 1, 1, 1, 1, 4, 4]
def baseStart_1759812 : Nat := 118140960795 + 1759812 * 2 ^ 59
def prefixEnd_1759812 : Nat := 4983230072969 + 3 ^ 40 * 1759812 * 2
def baseEnd_1759812 : Nat := 200806537233371991368173

theorem tailTrace_1759812 : CollatzResearch.WordTrace tailWord_1759812 prefixEnd_1759812 200806537233371991368173 := by
  unfold tailWord_1759812
  simp only [CollatzResearch.WordTrace]
  refine ⟨32092808350254575403272845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42790411133672767204363793 32092808350254575403272845)
  ·
    refine ⟨12034803131345465776227317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32092808350254575403272845 12034803131345465776227317)
    ·
      refine ⟨1128262793563637416521311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12034803131345465776227317 1128262793563637416521311)
      ·
        refine ⟨1692394190345456124781967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1128262793563637416521311 1692394190345456124781967)
        ·
          refine ⟨2538591285518184187172951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1692394190345456124781967 2538591285518184187172951)
          ·
            refine ⟨3807886928277276280759427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2538591285518184187172951 3807886928277276280759427)
            ·
              refine ⟨5711830392415914421139141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3807886928277276280759427 5711830392415914421139141)
              ·
                refine ⟨1070968198577983953963589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5711830392415914421139141 1070968198577983953963589)
                ·
                  refine ⟨200806537233371991368173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1070968198577983953963589 200806537233371991368173)
                  ·
                    rfl

theorem cell22_1759812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_1759812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759812 prefixEnd_1759812 := by exact prefixLift 1759812
  have htrace : WordTrace (prefixWord ++ tailWord_1759812) baseStart_1759812 baseEnd_1759812 := by
    simpa [prefixWord, tailWord_1759812, baseEnd_1759812] using wordTrace_append hprefix tailTrace_1759812
  have hstable : (prefixWord ++ tailWord_1759812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759812).length < 2 ^ (prefixWord ++ tailWord_1759812).sum := by decide
  have hdescent : baseEnd_1759812 < baseStart_1759812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759842 : List Nat := [3, 3, 2, 3, 2, 1, 1, 1, 2, 4]
def baseStart_1759842 : Nat := 118140960795 + 1759842 * 2 ^ 59
def prefixEnd_1759842 : Nat := 4983230072969 + 3 ^ 40 * 1759842 * 2
def baseEnd_1759842 : Nat := 602429881313205895854427

theorem tailTrace_1759842 : CollatzResearch.WordTrace tailWord_1759842 prefixEnd_1759842 602429881313205895854427 := by
  unfold tailWord_1759842
  simp only [CollatzResearch.WordTrace]
  refine ⟨16046677722600116482534445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42791140593600310620091853 16046677722600116482534445)
  ·
    refine ⟨6017504145975043680950417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16046677722600116482534445 6017504145975043680950417)
    ·
      refine ⟨4513128109481282760712813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6017504145975043680950417 4513128109481282760712813)
      ·
        refine ⟨1692423041055481035267305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4513128109481282760712813 1692423041055481035267305)
        ·
          refine ⟨1269317280791610776450479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1692423041055481035267305 1269317280791610776450479)
          ·
            refine ⟨1903975921187416164675719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1269317280791610776450479 1903975921187416164675719)
            ·
              refine ⟨2855963881781124247013579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1903975921187416164675719 2855963881781124247013579)
              ·
                refine ⟨4283945822671686370520369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855963881781124247013579 4283945822671686370520369)
                ·
                  refine ⟨3212959367003764777890277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4283945822671686370520369 3212959367003764777890277)
                  ·
                    refine ⟨602429881313205895854427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3212959367003764777890277 602429881313205895854427)
                    ·
                      rfl

theorem cell22_1759842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_1759842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759842 prefixEnd_1759842 := by exact prefixLift 1759842
  have htrace : WordTrace (prefixWord ++ tailWord_1759842) baseStart_1759842 baseEnd_1759842 := by
    simpa [prefixWord, tailWord_1759842, baseEnd_1759842] using wordTrace_append hprefix tailTrace_1759842
  have hstable : (prefixWord ++ tailWord_1759842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759842).length < 2 ^ (prefixWord ++ tailWord_1759842).sum := by decide
  have hdescent : baseEnd_1759842 < baseStart_1759842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759949 : List Nat := [1, 6, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_1759949 : Nat := 118140960795 + 1759949 * 2 ^ 59
def prefixEnd_1759949 : Nat := 4983230072969 + 3 ^ 40 * 1759949 * 2
def baseEnd_1759949 : Nat := 602466509599893283429099

theorem tailTrace_1759949 : CollatzResearch.WordTrace tailWord_1759949 prefixEnd_1759949 602466509599893283429099 := by
  unfold tailWord_1759949
  simp only [CollatzResearch.WordTrace]
  refine ⟨64190613501012823204282901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42793742334008548802855267 64190613501012823204282901)
  ·
    refine ⟨3008935007859976087700761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 64190613501012823204282901 3008935007859976087700761)
    ·
      refine ⟨2256701255894982065775571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3008935007859976087700761 2256701255894982065775571)
      ·
        refine ⟨3385051883842473098663357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2256701255894982065775571 3385051883842473098663357)
        ·
          refine ⟨1269394456440927411998759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3385051883842473098663357 1269394456440927411998759)
          ·
            refine ⟨1904091684661391117998139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1269394456440927411998759 1904091684661391117998139)
            ·
              refine ⟨2856137526992086676997209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1904091684661391117998139 2856137526992086676997209)
              ·
                refine ⟨2142103145244065007747907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2856137526992086676997209 2142103145244065007747907)
                ·
                  refine ⟨3213154717866097511621861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2142103145244065007747907 3213154717866097511621861)
                  ·
                    refine ⟨602466509599893283429099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3213154717866097511621861 602466509599893283429099)
                    ·
                      rfl

theorem cell22_1759949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_1759949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1759949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1759949 prefixEnd_1759949 := by exact prefixLift 1759949
  have htrace : WordTrace (prefixWord ++ tailWord_1759949) baseStart_1759949 baseEnd_1759949 := by
    simpa [prefixWord, tailWord_1759949, baseEnd_1759949] using wordTrace_append hprefix tailTrace_1759949
  have hstable : (prefixWord ++ tailWord_1759949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759949).length < 2 ^ (prefixWord ++ tailWord_1759949).sum := by decide
  have hdescent : baseEnd_1759949 < baseStart_1759949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760033 : List Nat := [1, 2, 3, 2, 1, 2, 3, 3, 1, 4]
def baseStart_1760033 : Nat := 118140960795 + 1760033 * 2 ^ 59
def prefixEnd_1760033 : Nat := 4983230072969 + 3 ^ 40 * 1760033 * 2
def baseEnd_1760033 : Nat := 602495264516545064328841

theorem tailTrace_1760033 : CollatzResearch.WordTrace tailWord_1760033 prefixEnd_1760033 602495264516545064328841 := by
  unfold tailWord_1760033
  simp only [CollatzResearch.WordTrace]
  refine ⟨64193677232708505550340753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42795784821805670366893835 64193677232708505550340753)
  ·
    refine ⟨48145257924531379162755565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64193677232708505550340753 48145257924531379162755565)
    ·
      refine ⟨18054471721699267186033337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48145257924531379162755565 18054471721699267186033337)
      ·
        refine ⟨13540853791274450389525003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18054471721699267186033337 13540853791274450389525003)
        ·
          refine ⟨20311280686911675584287505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13540853791274450389525003 20311280686911675584287505)
          ·
            refine ⟨15233460515183756688215629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20311280686911675584287505 15233460515183756688215629)
            ·
              refine ⟨5712547693193908758080861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15233460515183756688215629 5712547693193908758080861)
              ·
                refine ⟨2142205384947715784280323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5712547693193908758080861 2142205384947715784280323)
                ·
                  refine ⟨3213308077421573676420485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2142205384947715784280323 3213308077421573676420485)
                  ·
                    refine ⟨602495264516545064328841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3213308077421573676420485 602495264516545064328841)
                    ·
                      rfl

theorem cell22_1760033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_1760033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760033 prefixEnd_1760033 := by exact prefixLift 1760033
  have htrace : WordTrace (prefixWord ++ tailWord_1760033) baseStart_1760033 baseEnd_1760033 := by
    simpa [prefixWord, tailWord_1760033, baseEnd_1760033] using wordTrace_append hprefix tailTrace_1760033
  have hstable : (prefixWord ++ tailWord_1760033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760033).length < 2 ^ (prefixWord ++ tailWord_1760033).sum := by decide
  have hdescent : baseEnd_1760033 < baseStart_1760033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760063 : List Nat := [1, 1, 2, 2, 5, 1, 3, 1, 1, 5]
def baseStart_1760063 : Nat := 118140960795 + 1760063 * 2 ^ 59
def prefixEnd_1760063 : Nat := 4983230072969 + 3 ^ 40 * 1760063 * 2
def baseEnd_1760063 : Nat := 602505534129634986078749

theorem tailTrace_1760063 : CollatzResearch.WordTrace tailWord_1760063 prefixEnd_1760063 602505534129634986078749 := by
  unfold tailWord_1760063
  simp only [CollatzResearch.WordTrace]
  refine ⟨64194771422599820673932843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42796514281733213782621895 64194771422599820673932843)
  ·
    refine ⟨96292157133899731010899265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64194771422599820673932843 96292157133899731010899265)
    ·
      refine ⟨72219117850424798258174449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96292157133899731010899265 72219117850424798258174449)
      ·
        refine ⟨54164338387818598693630837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72219117850424798258174449 54164338387818598693630837)
        ·
          refine ⟨5077906723857993627527891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54164338387818598693630837 5077906723857993627527891)
          ·
            refine ⟨7616860085786990441291837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5077906723857993627527891 7616860085786990441291837)
            ·
              refine ⟨2856322532170121415484439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7616860085786990441291837 2856322532170121415484439)
              ·
                refine ⟨4284483798255182123226659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2856322532170121415484439 4284483798255182123226659)
                ·
                  refine ⟨6426725697382773184839989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4284483798255182123226659 6426725697382773184839989)
                  ·
                    refine ⟨602505534129634986078749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6426725697382773184839989 602505534129634986078749)
                    ·
                      rfl

theorem cell22_1760063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 5].length) (baseStart_1760063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760063 prefixEnd_1760063 := by exact prefixLift 1760063
  have htrace : WordTrace (prefixWord ++ tailWord_1760063) baseStart_1760063 baseEnd_1760063 := by
    simpa [prefixWord, tailWord_1760063, baseEnd_1760063] using wordTrace_append hprefix tailTrace_1760063
  have hstable : (prefixWord ++ tailWord_1760063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760063).length < 2 ^ (prefixWord ++ tailWord_1760063).sum := by decide
  have hdescent : baseEnd_1760063 < baseStart_1760063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760110 : List Nat := [4, 1, 2, 3, 2, 1, 2, 7]
def baseStart_1760110 : Nat := 118140960795 + 1760110 * 2 ^ 59
def prefixEnd_1760110 : Nat := 4983230072969 + 3 ^ 40 * 1760110 * 2
def baseEnd_1760110 : Nat := 66946847021126947794845

theorem tailTrace_1760110 : CollatzResearch.WordTrace tailWord_1760110 prefixEnd_1760110 66946847021126947794845 := by
  unfold tailWord_1760110
  simp only [CollatzResearch.WordTrace]
  refine ⟨8024560706678693462611723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42797657102286365133929189 8024560706678693462611723)
  ·
    refine ⟨12036841060018040193917585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8024560706678693462611723 12036841060018040193917585)
    ·
      refine ⟨9027630795013530145438189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12036841060018040193917585 9027630795013530145438189)
      ·
        refine ⟨3385361548130073804539321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9027630795013530145438189 3385361548130073804539321)
        ·
          refine ⟨2539021161097555353404491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3385361548130073804539321 2539021161097555353404491)
          ·
            refine ⟨3808531741646333030106737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2539021161097555353404491 3808531741646333030106737)
            ·
              refine ⟨2856398806234749772580053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3808531741646333030106737 2856398806234749772580053)
              ·
                refine ⟨66946847021126947794845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2856398806234749772580053 66946847021126947794845)
                ·
                  rfl

theorem cell22_1760110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_1760110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760110 prefixEnd_1760110 := by exact prefixLift 1760110
  have htrace : WordTrace (prefixWord ++ tailWord_1760110) baseStart_1760110 baseEnd_1760110 := by
    simpa [prefixWord, tailWord_1760110, baseEnd_1760110] using wordTrace_append hprefix tailTrace_1760110
  have hstable : (prefixWord ++ tailWord_1760110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760110).length < 2 ^ (prefixWord ++ tailWord_1760110).sum := by decide
  have hdescent : baseEnd_1760110 < baseStart_1760110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760159 : List Nat := [1, 1, 2, 5, 2, 1, 4, 2, 1, 3]
def baseStart_1760159 : Nat := 118140960795 + 1760159 * 2 ^ 59
def prefixEnd_1760159 : Nat := 4983230072969 + 3 ^ 40 * 1760159 * 2
def baseEnd_1760159 : Nat := 602538396891522735678455

theorem tailTrace_1760159 : CollatzResearch.WordTrace tailWord_1760159 prefixEnd_1760159 602538396891522735678455 := by
  unfold tailWord_1760159
  simp only [CollatzResearch.WordTrace]
  refine ⟨64198272830252029069427531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42798848553501352712951687 64198272830252029069427531)
  ·
    refine ⟨96297409245378043604141297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64198272830252029069427531 96297409245378043604141297)
    ·
      refine ⟨72223056934033532703105973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96297409245378043604141297 72223056934033532703105973)
      ·
        refine ⟨6770911587565643690916185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72223056934033532703105973 6770911587565643690916185)
        ·
          refine ⟨5078183690674232768187139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6770911587565643690916185 5078183690674232768187139)
          ·
            refine ⟨7617275536011349152280709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5078183690674232768187139 7617275536011349152280709)
            ·
              refine ⟨1428239163002127966052633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7617275536011349152280709 1428239163002127966052633)
              ·
                refine ⟨1071179372251595974539475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1428239163002127966052633 1071179372251595974539475)
                ·
                  refine ⟨1606769058377393961809213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1071179372251595974539475 1606769058377393961809213)
                  ·
                    refine ⟨602538396891522735678455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1606769058377393961809213 602538396891522735678455)
                    ·
                      rfl

theorem cell22_1760159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 1, 3].length) (baseStart_1760159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760159 prefixEnd_1760159 := by exact prefixLift 1760159
  have htrace : WordTrace (prefixWord ++ tailWord_1760159) baseStart_1760159 baseEnd_1760159 := by
    simpa [prefixWord, tailWord_1760159, baseEnd_1760159] using wordTrace_append hprefix tailTrace_1760159
  have hstable : (prefixWord ++ tailWord_1760159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760159).length < 2 ^ (prefixWord ++ tailWord_1760159).sum := by decide
  have hdescent : baseEnd_1760159 < baseStart_1760159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760215 : List Nat := [1, 1, 3, 2, 1, 1, 2, 6, 2, 3]
def baseStart_1760215 : Nat := 118140960795 + 1760215 * 2 ^ 59
def prefixEnd_1760215 : Nat := 4983230072969 + 3 ^ 40 * 1760215 * 2
def baseEnd_1760215 : Nat := 602557566835957256278283

theorem tailTrace_1760215 : CollatzResearch.WordTrace tailWord_1760215 prefixEnd_1760215 602557566835957256278283 := by
  unfold tailWord_1760215
  simp only [CollatzResearch.WordTrace]
  refine ⟨64200315318049150633466099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42800210212032767088977399 64200315318049150633466099)
  ·
    refine ⟨96300472977073725950199149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64200315318049150633466099 96300472977073725950199149)
    ·
      refine ⟨36112677366402647231324681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96300472977073725950199149 36112677366402647231324681)
      ·
        refine ⟨27084508024801985423493511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36112677366402647231324681 27084508024801985423493511)
        ·
          refine ⟨40626762037202978135240267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27084508024801985423493511 40626762037202978135240267)
          ·
            refine ⟨60940143055804467202860401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40626762037202978135240267 60940143055804467202860401)
            ·
              refine ⟨45705107291853350402145301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60940143055804467202860401 45705107291853350402145301)
              ·
                refine ⟨2142426904305625800100561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45705107291853350402145301 2142426904305625800100561)
                ·
                  refine ⟨1606820178229219350075421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2142426904305625800100561 1606820178229219350075421)
                  ·
                    refine ⟨602557566835957256278283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1606820178229219350075421 602557566835957256278283)
                    ·
                      rfl

theorem cell22_1760215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 3].length) (baseStart_1760215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760215 prefixEnd_1760215 := by exact prefixLift 1760215
  have htrace : WordTrace (prefixWord ++ tailWord_1760215) baseStart_1760215 baseEnd_1760215 := by
    simpa [prefixWord, tailWord_1760215, baseEnd_1760215] using wordTrace_append hprefix tailTrace_1760215
  have hstable : (prefixWord ++ tailWord_1760215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760215).length < 2 ^ (prefixWord ++ tailWord_1760215).sum := by decide
  have hdescent : baseEnd_1760215 < baseStart_1760215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760277 : List Nat := [1, 3, 2, 1, 4, 1, 3, 1, 3, 3]
def baseStart_1760277 : Nat := 118140960795 + 1760277 * 2 ^ 59
def prefixEnd_1760277 : Nat := 4983230072969 + 3 ^ 40 * 1760277 * 2
def baseEnd_1760277 : Nat := 602578790703009761228093

theorem tailTrace_1760277 : CollatzResearch.WordTrace tailWord_1760277 prefixEnd_1760277 602578790703009761228093 := by
  unfold tailWord_1760277
  simp only [CollatzResearch.WordTrace]
  refine ⟨64202576643824535222223085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42801717762549690148148723 64202576643824535222223085)
  ·
    refine ⟨24075966241434200708333657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64202576643824535222223085 24075966241434200708333657)
    ·
      refine ⟨18056974681075650531250243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24075966241434200708333657 18056974681075650531250243)
      ·
        refine ⟨27085462021613475796875365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18056974681075650531250243 27085462021613475796875365)
        ·
          refine ⟨5078524129052526711914131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27085462021613475796875365 5078524129052526711914131)
          ·
            refine ⟨7617786193578790067871197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5078524129052526711914131 7617786193578790067871197)
            ·
              refine ⟨2856669822592046275451699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7617786193578790067871197 2856669822592046275451699)
              ·
                refine ⟨4285004733888069413177549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2856669822592046275451699 4285004733888069413177549)
                ·
                  refine ⟨1606876775208026029941581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4285004733888069413177549 1606876775208026029941581)
                  ·
                    refine ⟨602578790703009761228093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1606876775208026029941581 602578790703009761228093)
                    ·
                      rfl

theorem cell22_1760277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_1760277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760277 prefixEnd_1760277 := by exact prefixLift 1760277
  have htrace : WordTrace (prefixWord ++ tailWord_1760277) baseStart_1760277 baseEnd_1760277 := by
    simpa [prefixWord, tailWord_1760277, baseEnd_1760277] using wordTrace_append hprefix tailTrace_1760277
  have hstable : (prefixWord ++ tailWord_1760277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760277).length < 2 ^ (prefixWord ++ tailWord_1760277).sum := by decide
  have hdescent : baseEnd_1760277 < baseStart_1760277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760414 : List Nat := [4, 3, 1, 1, 2, 1, 4, 6]
def baseStart_1760414 : Nat := 118140960795 + 1760414 * 2 ^ 59
def prefixEnd_1760414 : Nat := 4983230072969 + 3 ^ 40 * 1760414 * 2
def baseEnd_1760414 : Nat := 66958409844754118950297

theorem tailTrace_1760414 : CollatzResearch.WordTrace tailWord_1760414 prefixEnd_1760414 66958409844754118950297 := by
  unfold tailWord_1760414
  simp only [CollatzResearch.WordTrace]
  refine ⟨8025946680541025952495037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42805048962885471746640197 8025946680541025952495037)
  ·
    refine ⟨3009730005202884732185639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8025946680541025952495037 3009730005202884732185639)
    ·
      refine ⟨4514595007804327098278459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3009730005202884732185639 4514595007804327098278459)
      ·
        refine ⟨6771892511706490647417689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4514595007804327098278459 6771892511706490647417689)
        ·
          refine ⟨5078919383779867985563267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6771892511706490647417689 5078919383779867985563267)
          ·
            refine ⟨7618379075669801978344901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5078919383779867985563267 7618379075669801978344901)
            ·
              refine ⟨1428446076688087870939669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7618379075669801978344901 1428446076688087870939669)
              ·
                refine ⟨66958409844754118950297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1428446076688087870939669 66958409844754118950297)
                ·
                  rfl

theorem cell22_1760414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_1760414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760414 prefixEnd_1760414 := by exact prefixLift 1760414
  have htrace : WordTrace (prefixWord ++ tailWord_1760414) baseStart_1760414 baseEnd_1760414 := by
    simpa [prefixWord, tailWord_1760414, baseEnd_1760414] using wordTrace_append hprefix tailTrace_1760414
  have hstable : (prefixWord ++ tailWord_1760414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760414).length < 2 ^ (prefixWord ++ tailWord_1760414).sum := by decide
  have hdescent : baseEnd_1760414 < baseStart_1760414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760440 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 2, 5]
def baseStart_1760440 : Nat := 118140960795 + 1760440 * 2 ^ 59
def prefixEnd_1760440 : Nat := 4983230072969 + 3 ^ 40 * 1760440 * 2
def baseEnd_1760440 : Nat := 602634588934131669402593

theorem tailTrace_1760440 : CollatzResearch.WordTrace tailWord_1760440 prefixEnd_1760440 602634588934131669402593 := by
  unfold tailWord_1760440
  simp only [CollatzResearch.WordTrace]
  refine ⟨32104260871117007030203387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42805681161489342706937849 32104260871117007030203387)
  ·
    refine ⟨48156391306675510545305081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32104260871117007030203387 48156391306675510545305081)
    ·
      refine ⟨36117293480006632908978811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48156391306675510545305081 36117293480006632908978811)
      ·
        refine ⟨54175940220009949363468217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36117293480006632908978811 54175940220009949363468217)
        ·
          refine ⟨40631955165007462022601163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54175940220009949363468217 40631955165007462022601163)
          ·
            refine ⟨60947932747511193033901745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40631955165007462022601163 60947932747511193033901745)
            ·
              refine ⟨45710949560633394775426309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60947932747511193033901745 45710949560633394775426309)
              ·
                refine ⟨8570803042618761520392433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45710949560633394775426309 8570803042618761520392433)
                ·
                  refine ⟨6428102281964071140294325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8570803042618761520392433 6428102281964071140294325)
                  ·
                    refine ⟨602634588934131669402593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6428102281964071140294325 602634588934131669402593)
                    ·
                      rfl

theorem cell22_1760440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_1760440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760440 prefixEnd_1760440 := by exact prefixLift 1760440
  have htrace : WordTrace (prefixWord ++ tailWord_1760440) baseStart_1760440 baseEnd_1760440 := by
    simpa [prefixWord, tailWord_1760440, baseEnd_1760440] using wordTrace_append hprefix tailTrace_1760440
  have hstable : (prefixWord ++ tailWord_1760440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760440).length < 2 ^ (prefixWord ++ tailWord_1760440).sum := by decide
  have hdescent : baseEnd_1760440 < baseStart_1760440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760446 : List Nat := [4, 2, 1, 1, 3, 3, 1, 1, 3, 3]
def baseStart_1760446 : Nat := 118140960795 + 1760446 * 2 ^ 59
def prefixEnd_1760446 : Nat := 4983230072969 + 3 ^ 40 * 1760446 * 2
def baseEnd_1760446 : Nat := 602636642856749653752575

theorem tailTrace_1760446 : CollatzResearch.WordTrace tailWord_1760446 prefixEnd_1760446 602636642856749653752575 := by
  unfold tailWord_1760446
  simp only [CollatzResearch.WordTrace]
  refine ⟨8026092572526534635640649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42805827053474851390083461 8026092572526534635640649)
  ·
    refine ⟨6019569429394900976730487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8026092572526534635640649 6019569429394900976730487)
    ·
      refine ⟨9029354144092351465095731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6019569429394900976730487 9029354144092351465095731)
      ·
        refine ⟨13544031216138527197643597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9029354144092351465095731 13544031216138527197643597)
        ·
          refine ⟨5079011706051947699116349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13544031216138527197643597 5079011706051947699116349)
          ·
            refine ⟨1904629389769480387168631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5079011706051947699116349 1904629389769480387168631)
            ·
              refine ⟨2856944084654220580752947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1904629389769480387168631 2856944084654220580752947)
              ·
                refine ⟨4285416126981330871129421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2856944084654220580752947 4285416126981330871129421)
                ·
                  refine ⟨1607031047617999076673533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4285416126981330871129421 1607031047617999076673533)
                  ·
                    refine ⟨602636642856749653752575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1607031047617999076673533 602636642856749653752575)
                    ·
                      rfl

theorem cell22_1760446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_1760446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760446 prefixEnd_1760446 := by exact prefixLift 1760446
  have htrace : WordTrace (prefixWord ++ tailWord_1760446) baseStart_1760446 baseEnd_1760446 := by
    simpa [prefixWord, tailWord_1760446, baseEnd_1760446] using wordTrace_append hprefix tailTrace_1760446
  have hstable : (prefixWord ++ tailWord_1760446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760446).length < 2 ^ (prefixWord ++ tailWord_1760446).sum := by decide
  have hdescent : baseEnd_1760446 < baseStart_1760446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760502 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_1760502 : Nat := 118140960795 + 1760502 * 2 ^ 59
def prefixEnd_1760502 : Nat := 4983230072969 + 3 ^ 40 * 1760502 * 2
def baseEnd_1760502 : Nat := 602655812801184174352403

theorem tailTrace_1760502 : CollatzResearch.WordTrace tailWord_1760502 prefixEnd_1760502 602655812801184174352403 := by
  unfold tailWord_1760502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4013173941750587415572735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42807188712006265766109173 4013173941750587415572735)
  ·
    refine ⟨6019760912625881123359103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4013173941750587415572735 6019760912625881123359103)
    ·
      refine ⟨9029641368938821685038655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6019760912625881123359103 9029641368938821685038655)
      ·
        refine ⟨13544462053408232527557983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9029641368938821685038655 13544462053408232527557983)
        ·
          refine ⟨20316693080112348791336975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13544462053408232527557983 20316693080112348791336975)
          ·
            refine ⟨30475039620168523187005463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20316693080112348791336975 30475039620168523187005463)
            ·
              refine ⟨45712559430252784780508195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30475039620168523187005463 45712559430252784780508195)
              ·
                refine ⟨68568839145379177170762293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45712559430252784780508195 68568839145379177170762293)
                ·
                  refine ⟨6428328669879297859758965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68568839145379177170762293 6428328669879297859758965)
                  ·
                    refine ⟨602655812801184174352403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6428328669879297859758965 602655812801184174352403)
                    ·
                      rfl

theorem cell22_1760502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_1760502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760502 prefixEnd_1760502 := by exact prefixLift 1760502
  have htrace : WordTrace (prefixWord ++ tailWord_1760502) baseStart_1760502 baseEnd_1760502 := by
    simpa [prefixWord, tailWord_1760502, baseEnd_1760502] using wordTrace_append hprefix tailTrace_1760502
  have hstable : (prefixWord ++ tailWord_1760502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760502).length < 2 ^ (prefixWord ++ tailWord_1760502).sum := by decide
  have hdescent : baseEnd_1760502 < baseStart_1760502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760607 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 5, 4]
def baseStart_1760607 : Nat := 118140960795 + 1760607 * 2 ^ 59
def prefixEnd_1760607 : Nat := 4983230072969 + 3 ^ 40 * 1760607 * 2
def baseEnd_1760607 : Nat := 602691756446998900477081

theorem tailTrace_1760607 : CollatzResearch.WordTrace tailWord_1760607 prefixEnd_1760607 602691756446998900477081 := by
  unfold tailWord_1760607
  simp only [CollatzResearch.WordTrace]
  refine ⟨64214612732629001581736075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42809741821752667721157383 64214612732629001581736075)
  ·
    refine ⟨96321919098943502372604113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64214612732629001581736075 96321919098943502372604113)
    ·
      refine ⟨72241439324207626779453085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96321919098943502372604113 72241439324207626779453085)
      ·
        refine ⟨27090539746577860042294907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72241439324207626779453085 27090539746577860042294907)
        ·
          refine ⟨40635809619866790063442361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27090539746577860042294907 40635809619866790063442361)
          ·
            refine ⟨30476857214900092547581771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40635809619866790063442361 30476857214900092547581771)
            ·
              refine ⟨45715285822350138821372657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30476857214900092547581771 45715285822350138821372657)
              ·
                refine ⟨34286464366762604116029493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45715285822350138821372657 34286464366762604116029493)
                ·
                  refine ⟨3214356034383994135877765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34286464366762604116029493 3214356034383994135877765)
                  ·
                    refine ⟨602691756446998900477081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3214356034383994135877765 602691756446998900477081)
                    ·
                      rfl

theorem cell22_1760607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 4].length) (baseStart_1760607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760607 prefixEnd_1760607 := by exact prefixLift 1760607
  have htrace : WordTrace (prefixWord ++ tailWord_1760607) baseStart_1760607 baseEnd_1760607 := by
    simpa [prefixWord, tailWord_1760607, baseEnd_1760607] using wordTrace_append hprefix tailTrace_1760607
  have hstable : (prefixWord ++ tailWord_1760607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760607).length < 2 ^ (prefixWord ++ tailWord_1760607).sum := by decide
  have hdescent : baseEnd_1760607 < baseStart_1760607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760615 : List Nat := [1, 1, 5, 1, 4, 1, 3, 2, 1, 3]
def baseStart_1760615 : Nat := 118140960795 + 1760615 * 2 ^ 59
def prefixEnd_1760615 : Nat := 4983230072969 + 3 ^ 40 * 1760615 * 2
def baseEnd_1760615 : Nat := 602694495010489546277057

theorem tailTrace_1760615 : CollatzResearch.WordTrace tailWord_1760615 prefixEnd_1760615 602694495010489546277057 := by
  unfold tailWord_1760615
  simp only [CollatzResearch.WordTrace]
  refine ⟨64214904516600018948027299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42809936344400012632018199 64214904516600018948027299)
  ·
    refine ⟨96322356774900028422040949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64214904516600018948027299 96322356774900028422040949)
    ·
      refine ⟨9030220947646877664566339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96322356774900028422040949 9030220947646877664566339)
      ·
        refine ⟨13545331421470316496849509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9030220947646877664566339 13545331421470316496849509)
        ·
          refine ⟨2539749641525684343159283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13545331421470316496849509 2539749641525684343159283)
          ·
            refine ⟨3809624462288526514738925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2539749641525684343159283 3809624462288526514738925)
            ·
              refine ⟨1428609173358197443027097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3809624462288526514738925 1428609173358197443027097)
              ·
                refine ⟨1071456880018648082270323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1428609173358197443027097 1071456880018648082270323)
                ·
                  refine ⟨1607185320027972123405485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1071456880018648082270323 1607185320027972123405485)
                  ·
                    refine ⟨602694495010489546277057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1607185320027972123405485 602694495010489546277057)
                    ·
                      rfl

theorem cell22_1760615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_1760615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760615 prefixEnd_1760615 := by exact prefixLift 1760615
  have htrace : WordTrace (prefixWord ++ tailWord_1760615) baseStart_1760615 baseEnd_1760615 := by
    simpa [prefixWord, tailWord_1760615, baseEnd_1760615] using wordTrace_append hprefix tailTrace_1760615
  have hstable : (prefixWord ++ tailWord_1760615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760615).length < 2 ^ (prefixWord ++ tailWord_1760615).sum := by decide
  have hdescent : baseEnd_1760615 < baseStart_1760615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760641 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 3, 4]
def baseStart_1760641 : Nat := 118140960795 + 1760641 * 2 ^ 59
def prefixEnd_1760641 : Nat := 4983230072969 + 3 ^ 40 * 1760641 * 2
def baseEnd_1760641 : Nat := 602703395341834145126977

theorem tailTrace_1760641 : CollatzResearch.WordTrace tailWord_1760641 prefixEnd_1760641 602703395341834145126977 := by
  unfold tailWord_1760641
  simp only [CollatzResearch.WordTrace]
  refine ⟨64215852814505825388473777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42810568543003883592315851 64215852814505825388473777)
  ·
    refine ⟨48161889610879369041355333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64215852814505825388473777 48161889610879369041355333)
    ·
      refine ⟨9030354302039881695254125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48161889610879369041355333 9030354302039881695254125)
      ·
        refine ⟨3386382863264955635720297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9030354302039881695254125 3386382863264955635720297)
        ·
          refine ⟨2539787147448716726790223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3386382863264955635720297 2539787147448716726790223)
          ·
            refine ⟨3809680721173075090185335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2539787147448716726790223 3809680721173075090185335)
            ·
              refine ⟨5714521081759612635278003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3809680721173075090185335 5714521081759612635278003)
              ·
                refine ⟨8571781622639418952917005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5714521081759612635278003 8571781622639418952917005)
                ·
                  refine ⟨3214418108489782107343877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8571781622639418952917005 3214418108489782107343877)
                  ·
                    refine ⟨602703395341834145126977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3214418108489782107343877 602703395341834145126977)
                    ·
                      rfl

theorem cell22_1760641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_1760641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760641 prefixEnd_1760641 := by exact prefixLift 1760641
  have htrace : WordTrace (prefixWord ++ tailWord_1760641) baseStart_1760641 baseEnd_1760641 := by
    simpa [prefixWord, tailWord_1760641, baseEnd_1760641] using wordTrace_append hprefix tailTrace_1760641
  have hstable : (prefixWord ++ tailWord_1760641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760641).length < 2 ^ (prefixWord ++ tailWord_1760641).sum := by decide
  have hdescent : baseEnd_1760641 < baseStart_1760641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760671 : List Nat := [1, 1, 2, 5, 1, 2, 1, 4, 2, 3]
def baseStart_1760671 : Nat := 118140960795 + 1760671 * 2 ^ 59
def prefixEnd_1760671 : Nat := 4983230072969 + 3 ^ 40 * 1760671 * 2
def baseEnd_1760671 : Nat := 602713664954924066876885

theorem tailTrace_1760671 : CollatzResearch.WordTrace tailWord_1760671 prefixEnd_1760671 602713664954924066876885 := by
  unfold tailWord_1760671
  simp only [CollatzResearch.WordTrace]
  refine ⟨64216947004397140512065867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42811298002931427008043911 64216947004397140512065867)
  ·
    refine ⟨96325420506595710768098801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64216947004397140512065867 96325420506595710768098801)
    ·
      refine ⟨72244065379946783076074101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96325420506595710768098801 72244065379946783076074101)
      ·
        refine ⟨6772881129370010913381947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72244065379946783076074101 6772881129370010913381947)
        ·
          refine ⟨10159321694055016370072921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6772881129370010913381947 10159321694055016370072921)
          ·
            refine ⟨7619491270541262277554691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10159321694055016370072921 7619491270541262277554691)
            ·
              refine ⟨11429236905811893416332037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7619491270541262277554691 11429236905811893416332037)
              ·
                refine ⟨2142981919839730015562257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11429236905811893416332037 2142981919839730015562257)
                ·
                  refine ⟨1607236439879797511671693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2142981919839730015562257 1607236439879797511671693)
                  ·
                    refine ⟨602713664954924066876885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1607236439879797511671693 602713664954924066876885)
                    ·
                      rfl

theorem cell22_1760671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 3].length) (baseStart_1760671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760671 prefixEnd_1760671 := by exact prefixLift 1760671
  have htrace : WordTrace (prefixWord ++ tailWord_1760671) baseStart_1760671 baseEnd_1760671 := by
    simpa [prefixWord, tailWord_1760671, baseEnd_1760671] using wordTrace_append hprefix tailTrace_1760671
  have hstable : (prefixWord ++ tailWord_1760671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760671).length < 2 ^ (prefixWord ++ tailWord_1760671).sum := by decide
  have hdescent : baseEnd_1760671 < baseStart_1760671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760729 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 7]
def baseStart_1760729 : Nat := 118140960795 + 1760729 * 2 ^ 59
def prefixEnd_1760729 : Nat := 4983230072969 + 3 ^ 40 * 1760729 * 2
def baseEnd_1760729 : Nat := 200911173180077082975569

theorem tailTrace_1760729 : CollatzResearch.WordTrace tailWord_1760729 prefixEnd_1760729 200911173180077082975569 := by
  unfold tailWord_1760729
  simp only [CollatzResearch.WordTrace]
  refine ⟨64219062438187016417677241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42812708292124677611784827 64219062438187016417677241)
  ·
    refine ⟨48164296828640262313257931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64219062438187016417677241 48164296828640262313257931)
    ·
      refine ⟨72246445242960393469886897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48164296828640262313257931 72246445242960393469886897)
      ·
        refine ⟨54184833932220295102415173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72246445242960393469886897 54184833932220295102415173)
        ·
          refine ⟨10159656362291305331702845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54184833932220295102415173 10159656362291305331702845)
          ·
            refine ⟨3809871135859239499388567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10159656362291305331702845 3809871135859239499388567)
            ·
              refine ⟨5714806703788859249082851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3809871135859239499388567 5714806703788859249082851)
              ·
                refine ⟨8572210055683288873624277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5714806703788859249082851 8572210055683288873624277)
                ·
                  refine ⟨200911173180077082975569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8572210055683288873624277 200911173180077082975569)
                  ·
                    rfl

theorem cell22_1760729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 7].length) (baseStart_1760729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760729 prefixEnd_1760729 := by exact prefixLift 1760729
  have htrace : WordTrace (prefixWord ++ tailWord_1760729) baseStart_1760729 baseEnd_1760729 := by
    simpa [prefixWord, tailWord_1760729, baseEnd_1760729] using wordTrace_append hprefix tailTrace_1760729
  have hstable : (prefixWord ++ tailWord_1760729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760729).length < 2 ^ (prefixWord ++ tailWord_1760729).sum := by decide
  have hdescent : baseEnd_1760729 < baseStart_1760729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760733 : List Nat := [1, 4, 3, 1, 1, 3, 2, 1, 3, 3]
def baseStart_1760733 : Nat := 118140960795 + 1760733 * 2 ^ 59
def prefixEnd_1760733 : Nat := 4983230072969 + 3 ^ 40 * 1760733 * 2
def baseEnd_1760733 : Nat := 602734888821976571826695

theorem tailTrace_1760733 : CollatzResearch.WordTrace tailWord_1760733 prefixEnd_1760733 602734888821976571826695 := by
  unfold tailWord_1760733
  simp only [CollatzResearch.WordTrace]
  refine ⟨64219208330172525100822853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42812805553448350067215235 64219208330172525100822853)
  ·
    refine ⟨12041101561907348456404285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64219208330172525100822853 12041101561907348456404285)
    ·
      refine ⟨4515413085715255671151607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12041101561907348456404285 4515413085715255671151607)
      ·
        refine ⟨6773119628572883506727411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4515413085715255671151607 6773119628572883506727411)
        ·
          refine ⟨10159679442859325260091117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6773119628572883506727411 10159679442859325260091117)
          ·
            refine ⟨3809879791072246972534169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10159679442859325260091117 3809879791072246972534169)
            ·
              refine ⟨2857409843304185229400627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3809879791072246972534169 2857409843304185229400627)
              ·
                refine ⟨4286114764956277844100941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2857409843304185229400627 4286114764956277844100941)
                ·
                  refine ⟨1607293036858604191537853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4286114764956277844100941 1607293036858604191537853)
                  ·
                    refine ⟨602734888821976571826695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1607293036858604191537853 602734888821976571826695)
                    ·
                      rfl

theorem cell22_1760733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_1760733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760733 prefixEnd_1760733 := by exact prefixLift 1760733
  have htrace : WordTrace (prefixWord ++ tailWord_1760733) baseStart_1760733 baseEnd_1760733 := by
    simpa [prefixWord, tailWord_1760733, baseEnd_1760733] using wordTrace_append hprefix tailTrace_1760733
  have hstable : (prefixWord ++ tailWord_1760733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760733).length < 2 ^ (prefixWord ++ tailWord_1760733).sum := by decide
  have hdescent : baseEnd_1760733 < baseStart_1760733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760744 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 2, 5]
def baseStart_1760744 : Nat := 118140960795 + 1760744 * 2 ^ 59
def prefixEnd_1760744 : Nat := 4983230072969 + 3 ^ 40 * 1760744 * 2
def baseEnd_1760744 : Nat := 602738654346776209801661

theorem tailTrace_1760744 : CollatzResearch.WordTrace tailWord_1760744 prefixEnd_1760744 602738654346776209801661 := by
  unfold tailWord_1760744
  simp only [CollatzResearch.WordTrace]
  refine ⟨32109804766566336989736643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42813073022088449319648857 32109804766566336989736643)
  ·
    refine ⟨48164707149849505484604965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32109804766566336989736643 48164707149849505484604965)
    ·
      refine ⟨9030882590596782278363431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48164707149849505484604965 9030882590596782278363431)
      ·
        refine ⟨13546323885895173417545147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9030882590596782278363431 13546323885895173417545147)
        ·
          refine ⟨20319485828842760126317721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13546323885895173417545147 20319485828842760126317721)
          ·
            refine ⟨15239614371632070094738291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20319485828842760126317721 15239614371632070094738291)
            ·
              refine ⟨22859421557448105142107437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15239614371632070094738291 22859421557448105142107437)
              ·
                refine ⟨8572283084043039428290289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22859421557448105142107437 8572283084043039428290289)
                ·
                  refine ⟨6429212313032279571217717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8572283084043039428290289 6429212313032279571217717)
                  ·
                    refine ⟨602738654346776209801661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6429212313032279571217717 602738654346776209801661)
                    ·
                      rfl

theorem cell22_1760744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_1760744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760744 prefixEnd_1760744 := by exact prefixLift 1760744
  have htrace : WordTrace (prefixWord ++ tailWord_1760744) baseStart_1760744 baseEnd_1760744 := by
    simpa [prefixWord, tailWord_1760744, baseEnd_1760744] using wordTrace_append hprefix tailTrace_1760744
  have hstable : (prefixWord ++ tailWord_1760744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760744).length < 2 ^ (prefixWord ++ tailWord_1760744).sum := by decide
  have hdescent : baseEnd_1760744 < baseStart_1760744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760776 : List Nat := [2, 1, 3, 2, 1, 1, 4, 3, 1, 4]
def baseStart_1760776 : Nat := 118140960795 + 1760776 * 2 ^ 59
def prefixEnd_1760776 : Nat := 4983230072969 + 3 ^ 40 * 1760776 * 2
def baseEnd_1760776 : Nat := 602749608600738793001563

theorem tailTrace_1760776 : CollatzResearch.WordTrace tailWord_1760776 prefixEnd_1760776 602749608600738793001563 := by
  unfold tailWord_1760776
  simp only [CollatzResearch.WordTrace]
  refine ⟨32110388334508371722319091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42813851112677828963092121 32110388334508371722319091)
  ·
    refine ⟨48165582501762557583478637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32110388334508371722319091 48165582501762557583478637)
    ·
      refine ⟨18062093438160959093804489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48165582501762557583478637 18062093438160959093804489)
      ·
        refine ⟨13546570078620719320353367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18062093438160959093804489 13546570078620719320353367)
        ·
          refine ⟨20319855117931078980530051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13546570078620719320353367 20319855117931078980530051)
          ·
            refine ⟨30479782676896618470795077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20319855117931078980530051 30479782676896618470795077)
            ·
              refine ⟨5714959251918115963274077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30479782676896618470795077 5714959251918115963274077)
              ·
                refine ⟨2143109719469293486227779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5714959251918115963274077 2143109719469293486227779)
                ·
                  refine ⟨3214664579203940229341669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2143109719469293486227779 3214664579203940229341669)
                  ·
                    refine ⟨602749608600738793001563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3214664579203940229341669 602749608600738793001563)
                    ·
                      rfl

theorem cell22_1760776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_1760776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760776 prefixEnd_1760776 := by exact prefixLift 1760776
  have htrace : WordTrace (prefixWord ++ tailWord_1760776) baseStart_1760776 baseEnd_1760776 := by
    simpa [prefixWord, tailWord_1760776, baseEnd_1760776] using wordTrace_append hprefix tailTrace_1760776
  have hstable : (prefixWord ++ tailWord_1760776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760776).length < 2 ^ (prefixWord ++ tailWord_1760776).sum := by decide
  have hdescent : baseEnd_1760776 < baseStart_1760776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760819 : List Nat := [1, 1, 1, 2, 4, 3, 2, 8]
def baseStart_1760819 : Nat := 118140960795 + 1760819 * 2 ^ 59
def prefixEnd_1760819 : Nat := 4983230072969 + 3 ^ 40 * 1760819 * 2
def baseEnd_1760819 : Nat := 66973814264389001575159

theorem tailTrace_1760819 : CollatzResearch.WordTrace tailWord_1760819 prefixEnd_1760819 66973814264389001575159 := by
  unfold tailWord_1760819
  simp only [CollatzResearch.WordTrace]
  refine ⟨64222345007860961788453511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42814896671907307858969007 64222345007860961788453511)
  ·
    refine ⟨96333517511791442682680267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64222345007860961788453511 96333517511791442682680267)
    ·
      refine ⟨144500276267687164024020401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96333517511791442682680267 144500276267687164024020401)
      ·
        refine ⟨108375207200765373018015301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144500276267687164024020401 108375207200765373018015301)
        ·
          refine ⟨20320351350143507440877869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108375207200765373018015301 20320351350143507440877869)
          ·
            refine ⟨7620131756303815290329201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20320351350143507440877869 7620131756303815290329201)
            ·
              refine ⟨5715098817227861467746901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7620131756303815290329201 5715098817227861467746901)
              ·
                refine ⟨66973814264389001575159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5715098817227861467746901 66973814264389001575159)
                ·
                  rfl

theorem cell22_1760819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 8].length) (baseStart_1760819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760819 prefixEnd_1760819 := by exact prefixLift 1760819
  have htrace : WordTrace (prefixWord ++ tailWord_1760819) baseStart_1760819 baseEnd_1760819 := by
    simpa [prefixWord, tailWord_1760819, baseEnd_1760819] using wordTrace_append hprefix tailTrace_1760819
  have hstable : (prefixWord ++ tailWord_1760819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760819).length < 2 ^ (prefixWord ++ tailWord_1760819).sum := by decide
  have hdescent : baseEnd_1760819 < baseStart_1760819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760821 : List Nat := [1, 3, 3, 1, 1, 3, 1, 3, 2, 4]
def baseStart_1760821 : Nat := 118140960795 + 1760821 * 2 ^ 59
def prefixEnd_1760821 : Nat := 4983230072969 + 3 ^ 40 * 1760821 * 2
def baseEnd_1760821 : Nat := 602765013020373675626425

theorem tailTrace_1760821 : CollatzResearch.WordTrace tailWord_1760821 prefixEnd_1760821 602765013020373675626425 := by
  unfold tailWord_1760821
  simp only [CollatzResearch.WordTrace]
  refine ⟨64222417953853716130026317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42814945302569144086684211 64222417953853716130026317)
  ·
    refine ⟨24083406732695143548759869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64222417953853716130026317 24083406732695143548759869)
    ·
      refine ⟨9031277524760678830784951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24083406732695143548759869 9031277524760678830784951)
      ·
        refine ⟨13546916287141018246177427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9031277524760678830784951 13546916287141018246177427)
        ·
          refine ⟨20320374430711527369266141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13546916287141018246177427 20320374430711527369266141)
          ·
            refine ⟨7620140411516822763474803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20320374430711527369266141 7620140411516822763474803)
            ·
              refine ⟨11430210617275234145212205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7620140411516822763474803 11430210617275234145212205)
              ·
                refine ⟨4286328981478212804454577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11430210617275234145212205 4286328981478212804454577)
                ·
                  refine ⟨3214746736108659603340933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4286328981478212804454577 3214746736108659603340933)
                  ·
                    refine ⟨602765013020373675626425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3214746736108659603340933 602765013020373675626425)
                    ·
                      rfl

theorem cell22_1760821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_1760821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760821 prefixEnd_1760821 := by exact prefixLift 1760821
  have htrace : WordTrace (prefixWord ++ tailWord_1760821) baseStart_1760821 baseEnd_1760821 := by
    simpa [prefixWord, tailWord_1760821, baseEnd_1760821] using wordTrace_append hprefix tailTrace_1760821
  have hstable : (prefixWord ++ tailWord_1760821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760821).length < 2 ^ (prefixWord ++ tailWord_1760821).sum := by decide
  have hdescent : baseEnd_1760821 < baseStart_1760821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760836 : List Nat := [2, 3, 5, 12]
def baseStart_1760836 : Nat := 118140960795 + 1760836 * 2 ^ 59
def prefixEnd_1760836 : Nat := 4983230072969 + 3 ^ 40 * 1760836 * 2
def baseEnd_1760836 : Nat := 826845195921699089851

theorem tailTrace_1760836 : CollatzResearch.WordTrace tailWord_1760836 prefixEnd_1760836 826845195921699089851 := by
  unfold tailWord_1760836
  simp only [CollatzResearch.WordTrace]
  refine ⟨32111482524399686845911181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42815310032532915794548241 32111482524399686845911181)
  ·
    refine ⟨12041805946649882567216693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32111482524399686845911181 12041805946649882567216693)
    ·
      refine ⟨1128919307498426490676565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12041805946649882567216693 1128919307498426490676565)
      ·
        refine ⟨826845195921699089851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1128919307498426490676565 826845195921699089851)
        ·
          rfl

theorem cell22_1760836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 12].length) (baseStart_1760836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760836 prefixEnd_1760836 := by exact prefixLift 1760836
  have htrace : WordTrace (prefixWord ++ tailWord_1760836) baseStart_1760836 baseEnd_1760836 := by
    simpa [prefixWord, tailWord_1760836, baseEnd_1760836] using wordTrace_append hprefix tailTrace_1760836
  have hstable : (prefixWord ++ tailWord_1760836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760836).length < 2 ^ (prefixWord ++ tailWord_1760836).sum := by decide
  have hdescent : baseEnd_1760836 < baseStart_1760836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760849 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 1, 8]
def baseStart_1760849 : Nat := 118140960795 + 1760849 * 2 ^ 59
def prefixEnd_1760849 : Nat := 4983230072969 + 3 ^ 40 * 1760849 * 2
def baseEnd_1760849 : Nat := 602774597992590935926339

theorem tailTrace_1760849 : CollatzResearch.WordTrace tailWord_1760849 prefixEnd_1760849 602774597992590935926339 := by
  unfold tailWord_1760849
  simp only [CollatzResearch.WordTrace]
  refine ⟨64223439197752276912045601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42815626131834851274697067 64223439197752276912045601)
  ·
    refine ⟨48167579398314207684034201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64223439197752276912045601 48167579398314207684034201)
    ·
      refine ⟨36125684548735655763025651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48167579398314207684034201 36125684548735655763025651)
      ·
        refine ⟨54188526823103483644538477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36125684548735655763025651 54188526823103483644538477)
        ·
          refine ⟨20320697558663806366701929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54188526823103483644538477 20320697558663806366701929)
          ·
            refine ⟨15240523168997854775026447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20320697558663806366701929 15240523168997854775026447)
            ·
              refine ⟨22860784753496782162539671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15240523168997854775026447 22860784753496782162539671)
              ·
                refine ⟨34291177130245173243809507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22860784753496782162539671 34291177130245173243809507)
                ·
                  refine ⟨51436765695367759865714261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34291177130245173243809507 51436765695367759865714261)
                  ·
                    refine ⟨602774597992590935926339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51436765695367759865714261 602774597992590935926339)
                    ·
                      rfl

theorem cell22_1760849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_1760849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760849 prefixEnd_1760849 := by exact prefixLift 1760849
  have htrace : WordTrace (prefixWord ++ tailWord_1760849) baseStart_1760849 baseEnd_1760849 := by
    simpa [prefixWord, tailWord_1760849, baseEnd_1760849] using wordTrace_append hprefix tailTrace_1760849
  have hstable : (prefixWord ++ tailWord_1760849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760849).length < 2 ^ (prefixWord ++ tailWord_1760849).sum := by decide
  have hdescent : baseEnd_1760849 < baseStart_1760849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760864 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 9]
def baseStart_1760864 : Nat := 118140960795 + 1760864 * 2 ^ 59
def prefixEnd_1760864 : Nat := 4983230072969 + 3 ^ 40 * 1760864 * 2
def baseEnd_1760864 : Nat := 200926577599711965600431

theorem tailTrace_1760864 : CollatzResearch.WordTrace tailWord_1760864 prefixEnd_1760864 200926577599711965600431 := by
  unfold tailWord_1760864
  simp only [CollatzResearch.WordTrace]
  refine ⟨32111993146348967236920823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42815990861798622982561097 32111993146348967236920823)
  ·
    refine ⟨48167989719523450855381235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32111993146348967236920823 48167989719523450855381235)
    ·
      refine ⟨72251984579285176283071853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48167989719523450855381235 72251984579285176283071853)
      ·
        refine ⟨27094494217231941106151945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72251984579285176283071853 27094494217231941106151945)
        ·
          refine ⟨20320870662923955829613959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27094494217231941106151945 20320870662923955829613959)
          ·
            refine ⟨30481305994385933744420939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20320870662923955829613959 30481305994385933744420939)
            ·
              refine ⟨45721958991578900616631409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30481305994385933744420939 45721958991578900616631409)
              ·
                refine ⟨34291469243684175462473557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45721958991578900616631409 34291469243684175462473557)
                ·
                  refine ⟨200926577599711965600431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34291469243684175462473557 200926577599711965600431)
                  ·
                    rfl

theorem cell22_1760864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 9].length) (baseStart_1760864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760864 prefixEnd_1760864 := by exact prefixLift 1760864
  have htrace : WordTrace (prefixWord ++ tailWord_1760864) baseStart_1760864 baseEnd_1760864 := by
    simpa [prefixWord, tailWord_1760864, baseEnd_1760864] using wordTrace_append hprefix tailTrace_1760864
  have hstable : (prefixWord ++ tailWord_1760864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760864).length < 2 ^ (prefixWord ++ tailWord_1760864).sum := by decide
  have hdescent : baseEnd_1760864 < baseStart_1760864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760868 : List Nat := [2, 3, 1, 1, 2, 4, 1, 2, 3, 3]
def baseStart_1760868 : Nat := 118140960795 + 1760868 * 2 ^ 59
def prefixEnd_1760868 : Nat := 4983230072969 + 3 ^ 40 * 1760868 * 2
def baseEnd_1760868 : Nat := 602781102080881219701281

theorem tailTrace_1760868 : CollatzResearch.WordTrace tailWord_1760868 prefixEnd_1760868 602781102080881219701281 := by
  unfold tailWord_1760868
  simp only [CollatzResearch.WordTrace]
  refine ⟨32112066092341721578493629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42816088123122295437991505 32112066092341721578493629)
  ·
    refine ⟨12042024784628145591935111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32112066092341721578493629 12042024784628145591935111)
    ·
      refine ⟨18063037176942218387902667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12042024784628145591935111 18063037176942218387902667)
      ·
        refine ⟨27094555765413327581854001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18063037176942218387902667 27094555765413327581854001)
        ·
          refine ⟨20320916824059995686390501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27094555765413327581854001 20320916824059995686390501)
          ·
            refine ⟨3810171904511249191198219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20320916824059995686390501 3810171904511249191198219)
            ·
              refine ⟨5715257856766873786797329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3810171904511249191198219 5715257856766873786797329)
              ·
                refine ⟨4286443392575155340097997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5715257856766873786797329 4286443392575155340097997)
                ·
                  refine ⟨1607416272215683252536749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4286443392575155340097997 1607416272215683252536749)
                  ·
                    refine ⟨602781102080881219701281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1607416272215683252536749 602781102080881219701281)
                    ·
                      rfl

theorem cell22_1760868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_1760868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760868 prefixEnd_1760868 := by exact prefixLift 1760868
  have htrace : WordTrace (prefixWord ++ tailWord_1760868) baseStart_1760868 baseEnd_1760868 := by
    simpa [prefixWord, tailWord_1760868, baseEnd_1760868] using wordTrace_append hprefix tailTrace_1760868
  have hstable : (prefixWord ++ tailWord_1760868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760868).length < 2 ^ (prefixWord ++ tailWord_1760868).sum := by decide
  have hdescent : baseEnd_1760868 < baseStart_1760868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760879 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 3, 7]
def baseStart_1760879 : Nat := 118140960795 + 1760879 * 2 ^ 59
def prefixEnd_1760879 : Nat := 4983230072969 + 3 ^ 40 * 1760879 * 2
def baseEnd_1760879 : Nat := 602784867605680857676247

theorem tailTrace_1760879 : CollatzResearch.WordTrace tailWord_1760879 prefixEnd_1760879 602784867605680857676247 := by
  unfold tailWord_1760879
  simp only [CollatzResearch.WordTrace]
  refine ⟨64224533387643592035637691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42816355591762394690425127 64224533387643592035637691)
  ·
    refine ⟨96336800081465388053456537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64224533387643592035637691 96336800081465388053456537)
    ·
      refine ⟨72252600061099041040092403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96336800081465388053456537 72252600061099041040092403)
      ·
        refine ⟨108378900091648561560138605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72252600061099041040092403 108378900091648561560138605)
        ·
          refine ⟨40642087534368210585051977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108378900091648561560138605 40642087534368210585051977)
          ·
            refine ⟨30481565650776157938788983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40642087534368210585051977 30481565650776157938788983)
            ·
              refine ⟨45722348476164236908183475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30481565650776157938788983 45722348476164236908183475)
              ·
                refine ⟨68583522714246355362275213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45722348476164236908183475 68583522714246355362275213)
                ·
                  refine ⟨25718821017842383260853205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68583522714246355362275213 25718821017842383260853205)
                  ·
                    refine ⟨602784867605680857676247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25718821017842383260853205 602784867605680857676247)
                    ·
                      rfl

theorem cell22_1760879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_1760879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760879 prefixEnd_1760879 := by exact prefixLift 1760879
  have htrace : WordTrace (prefixWord ++ tailWord_1760879) baseStart_1760879 baseEnd_1760879 := by
    simpa [prefixWord, tailWord_1760879, baseEnd_1760879] using wordTrace_append hprefix tailTrace_1760879
  have hstable : (prefixWord ++ tailWord_1760879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760879).length < 2 ^ (prefixWord ++ tailWord_1760879).sum := by decide
  have hdescent : baseEnd_1760879 < baseStart_1760879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760928 : List Nat := [2, 1, 1, 4, 3, 1, 1, 4, 1, 4]
def baseStart_1760928 : Nat := 118140960795 + 1760928 * 2 ^ 59
def prefixEnd_1760928 : Nat := 4983230072969 + 3 ^ 40 * 1760928 * 2
def baseEnd_1760928 : Nat := 602801641307061063201097

theorem tailTrace_1760928 : CollatzResearch.WordTrace tailWord_1760928 prefixEnd_1760928 602801641307061063201097 := by
  unfold tailWord_1760928
  simp only [CollatzResearch.WordTrace]
  refine ⟨32113160282233036702085719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42817547042977382269447625 32113160282233036702085719)
  ·
    refine ⟨48169740423349555053128579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32113160282233036702085719 48169740423349555053128579)
    ·
      refine ⟨72254610635024332579692869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48169740423349555053128579 72254610635024332579692869)
      ·
        refine ⟨13547739494067062358692413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72254610635024332579692869 13547739494067062358692413)
        ·
          refine ⟨5080402310275148384509655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13547739494067062358692413 5080402310275148384509655)
          ·
            refine ⟨7620603465412722576764483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5080402310275148384509655 7620603465412722576764483)
            ·
              refine ⟨11430905198119083865146725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7620603465412722576764483 11430905198119083865146725)
              ·
                refine ⟨2143294724647328224715011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11430905198119083865146725 2143294724647328224715011)
                ·
                  refine ⟨3214942086970992337072517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2143294724647328224715011 3214942086970992337072517)
                  ·
                    refine ⟨602801641307061063201097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3214942086970992337072517 602801641307061063201097)
                    ·
                      rfl

theorem cell22_1760928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 1, 4].length) (baseStart_1760928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760928 prefixEnd_1760928 := by exact prefixLift 1760928
  have htrace : WordTrace (prefixWord ++ tailWord_1760928) baseStart_1760928 baseEnd_1760928 := by
    simpa [prefixWord, tailWord_1760928, baseEnd_1760928] using wordTrace_append hprefix tailTrace_1760928
  have hstable : (prefixWord ++ tailWord_1760928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760928).length < 2 ^ (prefixWord ++ tailWord_1760928).sum := by decide
  have hdescent : baseEnd_1760928 < baseStart_1760928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760960 : List Nat := [2, 1, 1, 2, 4, 1, 5, 2, 4]
def baseStart_1760960 : Nat := 118140960795 + 1760960 * 2 ^ 59
def prefixEnd_1760960 : Nat := 4983230072969 + 3 ^ 40 * 1760960 * 2
def baseEnd_1760960 : Nat := 200937531853674548800333

theorem tailTrace_1760960 : CollatzResearch.WordTrace tailWord_1760960 prefixEnd_1760960 200937531853674548800333 := by
  unfold tailWord_1760960
  simp only [CollatzResearch.WordTrace]
  refine ⟨32113743850175071434668167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42818325133566761912890889 32113743850175071434668167)
  ·
    refine ⟨48170615775262607152002251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32113743850175071434668167 48170615775262607152002251)
    ·
      refine ⟨72255923662893910728003377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48170615775262607152002251 72255923662893910728003377)
      ·
        refine ⟨54191942747170433046002533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72255923662893910728003377 54191942747170433046002533)
        ·
          refine ⟨10160989265094456196125475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54191942747170433046002533 10160989265094456196125475)
          ·
            refine ⟨15241483897641684294188213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10160989265094456196125475 15241483897641684294188213)
            ·
              refine ⟨1428889115403907902580145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15241483897641684294188213 1428889115403907902580145)
              ·
                refine ⟨1071666836552930926935109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1428889115403907902580145 1071666836552930926935109)
                ·
                  refine ⟨200937531853674548800333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1071666836552930926935109 200937531853674548800333)
                  ·
                    rfl

theorem cell22_1760960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 4].length) (baseStart_1760960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1760960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1760960 prefixEnd_1760960 := by exact prefixLift 1760960
  have htrace : WordTrace (prefixWord ++ tailWord_1760960) baseStart_1760960 baseEnd_1760960 := by
    simpa [prefixWord, tailWord_1760960, baseEnd_1760960] using wordTrace_append hprefix tailTrace_1760960
  have hstable : (prefixWord ++ tailWord_1760960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760960).length < 2 ^ (prefixWord ++ tailWord_1760960).sum := by decide
  have hdescent : baseEnd_1760960 < baseStart_1760960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761022 : List Nat := [4, 2, 2, 1, 4, 1, 1, 7]
def baseStart_1761022 : Nat := 118140960795 + 1761022 * 2 ^ 59
def prefixEnd_1761022 : Nat := 4983230072969 + 3 ^ 40 * 1761022 * 2
def baseEnd_1761022 : Nat := 66981535492008461261201

theorem tailTrace_1761022 : CollatzResearch.WordTrace tailWord_1761022 prefixEnd_1761022 66981535492008461261201 := by
  unfold tailWord_1761022
  simp only [CollatzResearch.WordTrace]
  refine ⟨8028718628265690932261665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42819832684083684972062213 8028718628265690932261665)
  ·
    refine ⟨6021538971199268199196249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8028718628265690932261665 6021538971199268199196249)
    ·
      refine ⟨4516154228399451149397187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6021538971199268199196249 4516154228399451149397187)
      ·
        refine ⟨6774231342599176724095781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4516154228399451149397187 6774231342599176724095781)
        ·
          refine ⟨1270168376737345635767959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6774231342599176724095781 1270168376737345635767959)
          ·
            refine ⟨1905252565106018453651939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1270168376737345635767959 1905252565106018453651939)
            ·
              refine ⟨2857878847659027680477909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1905252565106018453651939 2857878847659027680477909)
              ·
                refine ⟨66981535492008461261201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2857878847659027680477909 66981535492008461261201)
                ·
                  rfl

theorem cell22_1761022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_1761022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1761022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1761022 prefixEnd_1761022 := by exact prefixLift 1761022
  have htrace : WordTrace (prefixWord ++ tailWord_1761022) baseStart_1761022 baseEnd_1761022 := by
    simpa [prefixWord, tailWord_1761022, baseEnd_1761022] using wordTrace_append hprefix tailTrace_1761022
  have hstable : (prefixWord ++ tailWord_1761022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761022).length < 2 ^ (prefixWord ++ tailWord_1761022).sum := by decide
  have hdescent : baseEnd_1761022 < baseStart_1761022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761174 : List Nat := [5, 3, 1, 1, 3, 9]
def baseStart_1761174 : Nat := 118140960795 + 1761174 * 2 ^ 59
def prefixEnd_1761174 : Nat := 4983230072969 + 3 ^ 40 * 1761174 * 2
def baseEnd_1761174 : Nat := 7443035211535782982103

theorem tailTrace_1761174 : CollatzResearch.WordTrace tailWord_1761174 prefixEnd_1761174 7443035211535782982103 := by
  unfold tailWord_1761174
  simp only [CollatzResearch.WordTrace]
  refine ⟨4014705807598428588601661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42823528614383238278417717 4014705807598428588601661)
  ·
    refine ⟨1505514677849410720725623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4014705807598428588601661 1505514677849410720725623)
    ·
      refine ⟨2258272016774116081088435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1505514677849410720725623 2258272016774116081088435)
      ·
        refine ⟨3387408025161174121632653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2258272016774116081088435 3387408025161174121632653)
        ·
          refine ⟨1270278009435440295612245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3387408025161174121632653 1270278009435440295612245)
          ·
            refine ⟨7443035211535782982103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1270278009435440295612245 7443035211535782982103)
            ·
              rfl

theorem cell22_1761174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 9].length) (baseStart_1761174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1761174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1761174 prefixEnd_1761174 := by exact prefixLift 1761174
  have htrace : WordTrace (prefixWord ++ tailWord_1761174) baseStart_1761174 baseEnd_1761174 := by
    simpa [prefixWord, tailWord_1761174, baseEnd_1761174] using wordTrace_append hprefix tailTrace_1761174
  have hstable : (prefixWord ++ tailWord_1761174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761174).length < 2 ^ (prefixWord ++ tailWord_1761174).sum := by decide
  have hdescent : baseEnd_1761174 < baseStart_1761174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761215 : List Nat := [1, 1, 2, 2, 2, 1, 4, 4, 1, 4]
def baseStart_1761215 : Nat := 118140960795 + 1761215 * 2 ^ 59
def prefixEnd_1761215 : Nat := 4983230072969 + 3 ^ 40 * 1761215 * 2
def baseEnd_1761215 : Nat := 602899887272287981275217

theorem tailTrace_1761215 : CollatzResearch.WordTrace tailWord_1761215 prefixEnd_1761215 602899887272287981275217 := by
  unfold tailWord_1761215
  simp only [CollatzResearch.WordTrace]
  refine ⟨64236788314426321419869099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42824525542950880946579399 64236788314426321419869099)
  ·
    refine ⟨96355182471639482129803649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64236788314426321419869099 96355182471639482129803649)
    ·
      refine ⟨72266386853729611597352737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96355182471639482129803649 72266386853729611597352737)
      ·
        refine ⟨54199790140297208698014553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72266386853729611597352737 54199790140297208698014553)
        ·
          refine ⟨40649842605222906523510915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54199790140297208698014553 40649842605222906523510915)
          ·
            refine ⟨60974763907834359785266373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40649842605222906523510915 60974763907834359785266373)
            ·
              refine ⟨11432768232718942459737445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60974763907834359785266373 11432768232718942459737445)
              ·
                refine ⟨2143644043634801711200771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11432768232718942459737445 2143644043634801711200771)
                ·
                  refine ⟨3215466065452202566801157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2143644043634801711200771 3215466065452202566801157)
                  ·
                    refine ⟨602899887272287981275217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3215466065452202566801157 602899887272287981275217)
                    ·
                      rfl

theorem cell22_1761215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 4].length) (baseStart_1761215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1761215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1761215 prefixEnd_1761215 := by exact prefixLift 1761215
  have htrace : WordTrace (prefixWord ++ tailWord_1761215) baseStart_1761215 baseEnd_1761215 := by
    simpa [prefixWord, tailWord_1761215, baseEnd_1761215] using wordTrace_append hprefix tailTrace_1761215
  have hstable : (prefixWord ++ tailWord_1761215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761215).length < 2 ^ (prefixWord ++ tailWord_1761215).sum := by decide
  have hdescent : baseEnd_1761215 < baseStart_1761215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761232 : List Nat := [2, 1, 1, 1, 1, 2, 8, 1, 1, 4]
def baseStart_1761232 : Nat := 118140960795 + 1761232 * 2 ^ 59
def prefixEnd_1761232 : Nat := 4983230072969 + 3 ^ 40 * 1761232 * 2
def baseEnd_1761232 : Nat := 602905706719705603600165

theorem tailTrace_1761232 : CollatzResearch.WordTrace tailWord_1761232 prefixEnd_1761232 602905706719705603600165 := by
  unfold tailWord_1761232
  simp only [CollatzResearch.WordTrace]
  refine ⟨32118704177682366661618975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42824938903576488882158633 32118704177682366661618975)
  ·
    refine ⟨48178056266523549992428463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32118704177682366661618975 48178056266523549992428463)
    ·
      refine ⟨72267084399785324988642695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48178056266523549992428463 72267084399785324988642695)
      ·
        refine ⟨108400626599677987482964043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72267084399785324988642695 108400626599677987482964043)
        ·
          refine ⟨162600939899516981224446065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108400626599677987482964043 162600939899516981224446065)
          ·
            refine ⟨121950704924637735918334549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162600939899516981224446065 121950704924637735918334549)
            ·
              refine ⟨1429109823335598467792983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 121950704924637735918334549 1429109823335598467792983)
              ·
                refine ⟨2143664735003397701689475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1429109823335598467792983 2143664735003397701689475)
                ·
                  refine ⟨3215497102505096552534213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2143664735003397701689475 3215497102505096552534213)
                  ·
                    refine ⟨602905706719705603600165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3215497102505096552534213 602905706719705603600165)
                    ·
                      rfl

theorem cell22_1761232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 1, 4].length) (baseStart_1761232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1761232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1761232 prefixEnd_1761232 := by exact prefixLift 1761232
  have htrace : WordTrace (prefixWord ++ tailWord_1761232) baseStart_1761232 baseEnd_1761232 := by
    simpa [prefixWord, tailWord_1761232, baseEnd_1761232] using wordTrace_append hprefix tailTrace_1761232
  have hstable : (prefixWord ++ tailWord_1761232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761232).length < 2 ^ (prefixWord ++ tailWord_1761232).sum := by decide
  have hdescent : baseEnd_1761232 < baseStart_1761232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761247 : List Nat := [1, 1, 2, 3, 4, 1, 2, 4, 4]
def baseStart_1761247 : Nat := 118140960795 + 1761247 * 2 ^ 59
def prefixEnd_1761247 : Nat := 4983230072969 + 3 ^ 40 * 1761247 * 2
def baseEnd_1761247 : Nat := 200970280508750188158373

theorem tailTrace_1761247 : CollatzResearch.WordTrace tailWord_1761247 prefixEnd_1761247 200970280508750188158373 := by
  unfold tailWord_1761247
  simp only [CollatzResearch.WordTrace]
  refine ⟨64237955450310390885033995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42825303633540260590022663 64237955450310390885033995)
  ·
    refine ⟨96356933175465586327550993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64237955450310390885033995 96356933175465586327550993)
    ·
      refine ⟨72267699881599189745663245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96356933175465586327550993 72267699881599189745663245)
      ·
        refine ⟨27100387455599696154623717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72267699881599189745663245 27100387455599696154623717)
        ·
          refine ⟨5081322647924943028991947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27100387455599696154623717 5081322647924943028991947)
          ·
            refine ⟨7621983971887414543487921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5081322647924943028991947 7621983971887414543487921)
            ·
              refine ⟨5716487978915560907615941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7621983971887414543487921 5716487978915560907615941)
              ·
                refine ⟨1071841496046667670177989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5716487978915560907615941 1071841496046667670177989)
                ·
                  refine ⟨200970280508750188158373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1071841496046667670177989 200970280508750188158373)
                  ·
                    rfl

theorem cell22_1761247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 4].length) (baseStart_1761247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1761247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1761247 prefixEnd_1761247 := by exact prefixLift 1761247
  have htrace : WordTrace (prefixWord ++ tailWord_1761247) baseStart_1761247 baseEnd_1761247 := by
    simpa [prefixWord, tailWord_1761247, baseEnd_1761247] using wordTrace_append hprefix tailTrace_1761247
  have hstable : (prefixWord ++ tailWord_1761247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761247).length < 2 ^ (prefixWord ++ tailWord_1761247).sum := by decide
  have hdescent : baseEnd_1761247 < baseStart_1761247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761262 : List Nat := [4, 1, 2, 1, 3, 1, 3, 1, 1, 5]
def baseStart_1761262 : Nat := 118140960795 + 1761262 * 2 ^ 59
def prefixEnd_1761262 : Nat := 4983230072969 + 3 ^ 40 * 1761262 * 2
def baseEnd_1761262 : Nat := 602915976332795525350073

theorem tailTrace_1761262 : CollatzResearch.WordTrace tailWord_1761262 prefixEnd_1761262 602915976332795525350073 := by
  unfold tailWord_1761262
  simp only [CollatzResearch.WordTrace]
  refine ⟨8029812818157006055853755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42825668363504032297886693 8029812818157006055853755)
  ·
    refine ⟨12044719227235509083780633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8029812818157006055853755 12044719227235509083780633)
    ·
      refine ⟨9033539420426631812835475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12044719227235509083780633 9033539420426631812835475)
      ·
        refine ⟨13550309130639947719253213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9033539420426631812835475 13550309130639947719253213)
        ·
          refine ⟨5081365923989980394719955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13550309130639947719253213 5081365923989980394719955)
          ·
            refine ⟨7622048885984970592079933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5081365923989980394719955 7622048885984970592079933)
            ·
              refine ⟨2858268332244363972029975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7622048885984970592079933 2858268332244363972029975)
              ·
                refine ⟨4287402498366545958044963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2858268332244363972029975 4287402498366545958044963)
                ·
                  refine ⟨6431103747549818937067445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4287402498366545958044963 6431103747549818937067445)
                  ·
                    refine ⟨602915976332795525350073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6431103747549818937067445 602915976332795525350073)
                    ·
                      rfl

theorem cell22_1761262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_1761262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1761262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1761262 prefixEnd_1761262 := by exact prefixLift 1761262
  have htrace : WordTrace (prefixWord ++ tailWord_1761262) baseStart_1761262 baseEnd_1761262 := by
    simpa [prefixWord, tailWord_1761262, baseEnd_1761262] using wordTrace_append hprefix tailTrace_1761262
  have hstable : (prefixWord ++ tailWord_1761262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761262).length < 2 ^ (prefixWord ++ tailWord_1761262).sum := by decide
  have hdescent : baseEnd_1761262 < baseStart_1761262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761275 : List Nat := [1, 1, 1, 1, 1, 3, 8, 6]
def baseStart_1761275 : Nat := 118140960795 + 1761275 * 2 ^ 59
def prefixEnd_1761275 : Nat := 4983230072969 + 3 ^ 40 * 1761275 * 2
def baseEnd_1761275 : Nat := 66991158499829758308337

theorem tailTrace_1761275 : CollatzResearch.WordTrace tailWord_1761275 prefixEnd_1761275 66991158499829758308337 := by
  unfold tailWord_1761275
  simp only [CollatzResearch.WordTrace]
  refine ⟨64238976694208951667053279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42825984462805967778035519 64238976694208951667053279)
  ·
    refine ⟨96358465041313427500579919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64238976694208951667053279 96358465041313427500579919)
    ·
      refine ⟨144537697561970141250869879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96358465041313427500579919 144537697561970141250869879)
      ·
        refine ⟨216806546342955211876304819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144537697561970141250869879 216806546342955211876304819)
        ·
          refine ⟨325209819514432817814457229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216806546342955211876304819 325209819514432817814457229)
          ·
            refine ⟨121953682317912306680421461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 325209819514432817814457229 121953682317912306680421461)
            ·
              refine ⟨1429144714663034843911189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 121953682317912306680421461 1429144714663034843911189)
              ·
                refine ⟨66991158499829758308337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1429144714663034843911189 66991158499829758308337)
                ·
                  rfl

theorem cell22_1761275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 6].length) (baseStart_1761275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1761275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1761275 prefixEnd_1761275 := by exact prefixLift 1761275
  have htrace : WordTrace (prefixWord ++ tailWord_1761275) baseStart_1761275 baseEnd_1761275 := by
    simpa [prefixWord, tailWord_1761275, baseEnd_1761275] using wordTrace_append hprefix tailTrace_1761275
  have hstable : (prefixWord ++ tailWord_1761275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761275).length < 2 ^ (prefixWord ++ tailWord_1761275).sum := by decide
  have hdescent : baseEnd_1761275 < baseStart_1761275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761313 : List Nat := [1, 2, 3, 2, 5, 1, 2, 1, 2, 3]
def baseStart_1761313 : Nat := 118140960795 + 1761313 * 2 ^ 59
def prefixEnd_1761313 : Nat := 4983230072969 + 3 ^ 40 * 1761313 * 2
def baseEnd_1761313 : Nat := 602933434675048392324917

theorem tailTrace_1761313 : CollatzResearch.WordTrace tailWord_1761313 prefixEnd_1761313 602933434675048392324917 := by
  unfold tailWord_1761313
  simp only [CollatzResearch.WordTrace]
  refine ⟨64240362668071284156936593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42826908445380856104624395 64240362668071284156936593)
  ·
    refine ⟨48180272001053463117702445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64240362668071284156936593 48180272001053463117702445)
    ·
      refine ⟨18067602000395048669138417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48180272001053463117702445 18067602000395048669138417)
      ·
        refine ⟨13550701500296286501853813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18067602000395048669138417 13550701500296286501853813)
        ·
          refine ⟨1270378265652776859548795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13550701500296286501853813 1270378265652776859548795)
          ·
            refine ⟨1905567398479165289323193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1270378265652776859548795 1905567398479165289323193)
            ·
              refine ⟨1429175548859373966992395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1905567398479165289323193 1429175548859373966992395)
              ·
                refine ⟨2143763323289060950488593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1429175548859373966992395 2143763323289060950488593)
                ·
                  refine ⟨1607822492466795712866445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2143763323289060950488593 1607822492466795712866445)
                  ·
                    refine ⟨602933434675048392324917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1607822492466795712866445 602933434675048392324917)
                    ·
                      rfl

theorem cell22_1761313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_1761313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1761313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1761313 prefixEnd_1761313 := by exact prefixLift 1761313
  have htrace : WordTrace (prefixWord ++ tailWord_1761313) baseStart_1761313 baseEnd_1761313 := by
    simpa [prefixWord, tailWord_1761313, baseEnd_1761313] using wordTrace_append hprefix tailTrace_1761313
  have hstable : (prefixWord ++ tailWord_1761313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761313).length < 2 ^ (prefixWord ++ tailWord_1761313).sum := by decide
  have hdescent : baseEnd_1761313 < baseStart_1761313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761358 : List Nat := [4, 1, 1, 1, 1, 6, 2, 2, 1, 3]
def baseStart_1761358 : Nat := 118140960795 + 1761358 * 2 ^ 59
def prefixEnd_1761358 : Nat := 4983230072969 + 3 ^ 40 * 1761358 * 2
def baseEnd_1761358 : Nat := 602948839094683274949779

theorem tailTrace_1761358 : CollatzResearch.WordTrace tailWord_1761358 prefixEnd_1761358 602948839094683274949779 := by
  unfold tailWord_1761358
  simp only [CollatzResearch.WordTrace]
  refine ⟨8030250494113532105290591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42828002635272171228216485 8030250494113532105290591)
  ·
    refine ⟨12045375741170298157935887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8030250494113532105290591 12045375741170298157935887)
    ·
      refine ⟨18068063611755447236903831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12045375741170298157935887 18068063611755447236903831)
      ·
        refine ⟨27102095417633170855355747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18068063611755447236903831 27102095417633170855355747)
        ·
          refine ⟨40653143126449756283033621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27102095417633170855355747 40653143126449756283033621)
          ·
            refine ⟨1905616084052332325767201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40653143126449756283033621 1905616084052332325767201)
            ·
              refine ⟨1429212063039249244325401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1905616084052332325767201 1429212063039249244325401)
              ·
                refine ⟨1071909047279436933244051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1429212063039249244325401 1071909047279436933244051)
                ·
                  refine ⟨1607863570919155399866077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1071909047279436933244051 1607863570919155399866077)
                  ·
                    refine ⟨602948839094683274949779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1607863570919155399866077 602948839094683274949779)
                    ·
                      rfl

theorem cell22_1761358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_1761358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1761358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1761358 prefixEnd_1761358 := by exact prefixLift 1761358
  have htrace : WordTrace (prefixWord ++ tailWord_1761358) baseStart_1761358 baseEnd_1761358 := by
    simpa [prefixWord, tailWord_1761358, baseEnd_1761358] using wordTrace_append hprefix tailTrace_1761358
  have hstable : (prefixWord ++ tailWord_1761358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761358).length < 2 ^ (prefixWord ++ tailWord_1761358).sum := by decide
  have hdescent : baseEnd_1761358 < baseStart_1761358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761399 : List Nat := [1, 1, 3, 1, 1, 6, 2, 3, 4]
def baseStart_1761399 : Nat := 118140960795 + 1761399 * 2 ^ 59
def prefixEnd_1761399 : Nat := 4983230072969 + 3 ^ 40 * 1761399 * 2
def baseEnd_1761399 : Nat := 200987624744190944891551

theorem tailTrace_1761399 : CollatzResearch.WordTrace tailWord_1761399 prefixEnd_1761399 200987624744190944891551 := by
  unfold tailWord_1761399
  simp only [CollatzResearch.WordTrace]
  refine ⟨64243499345759720844567251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42828999563839813896378167 64243499345759720844567251)
  ·
    refine ⟨96365249018639581266850877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64243499345759720844567251 96365249018639581266850877)
    ·
      refine ⟨36136968381989842975069079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96365249018639581266850877 36136968381989842975069079)
      ·
        refine ⟨54205452572984764462603619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36136968381989842975069079 54205452572984764462603619)
        ·
          refine ⟨81308178859477146693905429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54205452572984764462603619 81308178859477146693905429)
          ·
            refine ⟨3811320884037991251276817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81308178859477146693905429 3811320884037991251276817)
            ·
              refine ⟨2858490663028493438457613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3811320884037991251276817 2858490663028493438457613)
              ·
                refine ⟨1071933998635685039421605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2858490663028493438457613 1071933998635685039421605)
                ·
                  refine ⟨200987624744190944891551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1071933998635685039421605 200987624744190944891551)
                  ·
                    rfl

theorem cell22_1761399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 4].length) (baseStart_1761399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1761399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1761399 prefixEnd_1761399 := by exact prefixLift 1761399
  have htrace : WordTrace (prefixWord ++ tailWord_1761399) baseStart_1761399 baseEnd_1761399 := by
    simpa [prefixWord, tailWord_1761399, baseEnd_1761399] using wordTrace_append hprefix tailTrace_1761399
  have hstable : (prefixWord ++ tailWord_1761399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761399).length < 2 ^ (prefixWord ++ tailWord_1761399).sum := by decide
  have hdescent : baseEnd_1761399 < baseStart_1761399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761401 : List Nat := [1, 2, 1, 3, 4, 3, 2, 1, 1, 4]
def baseStart_1761401 : Nat := 118140960795 + 1761401 * 2 ^ 59
def prefixEnd_1761401 : Nat := 4983230072969 + 3 ^ 40 * 1761401 * 2
def baseEnd_1761401 : Nat := 602963558873445496124647

theorem tailTrace_1761401 : CollatzResearch.WordTrace tailWord_1761401 prefixEnd_1761401 602963558873445496124647 := by
  unfold tailWord_1761401
  simp only [CollatzResearch.WordTrace]
  refine ⟨64243572291752475186140057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42829048194501650124093371 64243572291752475186140057)
  ·
    refine ⟨48182679218814356389605043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64243572291752475186140057 48182679218814356389605043)
    ·
      refine ⟨72274018828221534584407565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48182679218814356389605043 72274018828221534584407565)
      ·
        refine ⟨27102757060583075469152837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72274018828221534584407565 27102757060583075469152837)
        ·
          refine ⟨5081766948859326650466157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27102757060583075469152837 5081766948859326650466157)
          ·
            refine ⟨1905662605822247493924809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5081766948859326650466157 1905662605822247493924809)
            ·
              refine ⟨1429246954366685620443607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1905662605822247493924809 1429246954366685620443607)
              ·
                refine ⟨2143870431550028430665411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1429246954366685620443607 2143870431550028430665411)
                ·
                  refine ⟨3215805647325042645998117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2143870431550028430665411 3215805647325042645998117)
                  ·
                    refine ⟨602963558873445496124647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3215805647325042645998117 602963558873445496124647)
                    ·
                      rfl

theorem cell22_1761401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 1, 4].length) (baseStart_1761401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1761401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1761401 prefixEnd_1761401 := by exact prefixLift 1761401
  have htrace : WordTrace (prefixWord ++ tailWord_1761401) baseStart_1761401 baseEnd_1761401 := by
    simpa [prefixWord, tailWord_1761401, baseEnd_1761401] using wordTrace_append hprefix tailTrace_1761401
  have hstable : (prefixWord ++ tailWord_1761401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761401).length < 2 ^ (prefixWord ++ tailWord_1761401).sum := by decide
  have hdescent : baseEnd_1761401 < baseStart_1761401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761412 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 4, 4]
def baseStart_1761412 : Nat := 118140960795 + 1761412 * 2 ^ 59
def prefixEnd_1761412 : Nat := 4983230072969 + 3 ^ 40 * 1761412 * 2
def baseEnd_1761412 : Nat := 602967324398245134099613

theorem tailTrace_1761412 : CollatzResearch.WordTrace tailWord_1761412 prefixEnd_1761412 602967324398245134099613 := by
  unfold tailWord_1761412
  simp only [CollatzResearch.WordTrace]
  refine ⟨32121986747356312032395245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42829315663141749376526993 32121986747356312032395245)
  ·
    refine ⟨12045745030258617012148217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32121986747356312032395245 12045745030258617012148217)
    ·
      refine ⟨9034308772693962759111163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12045745030258617012148217 9034308772693962759111163)
      ·
        refine ⟨13551463159040944138666745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9034308772693962759111163 13551463159040944138666745)
        ·
          refine ⟨10163597369280708104000059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13551463159040944138666745 10163597369280708104000059)
          ·
            refine ⟨15245396053921062156000089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10163597369280708104000059 15245396053921062156000089)
            ·
              refine ⟨11434047040440796617000067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15245396053921062156000089 11434047040440796617000067)
              ·
                refine ⟨17151070560661194925500101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11434047040440796617000067 17151070560661194925500101)
                ·
                  refine ⟨3215825730123974048531269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17151070560661194925500101 3215825730123974048531269)
                  ·
                    refine ⟨602967324398245134099613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3215825730123974048531269 602967324398245134099613)
                    ·
                      rfl

theorem cell22_1761412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_1761412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1761412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1761412 prefixEnd_1761412 := by exact prefixLift 1761412
  have htrace : WordTrace (prefixWord ++ tailWord_1761412) baseStart_1761412 baseEnd_1761412 := by
    simpa [prefixWord, tailWord_1761412, baseEnd_1761412] using wordTrace_append hprefix tailTrace_1761412
  have hstable : (prefixWord ++ tailWord_1761412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761412).length < 2 ^ (prefixWord ++ tailWord_1761412).sum := by decide
  have hdescent : baseEnd_1761412 < baseStart_1761412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761431 : List Nat := [1, 1, 3, 3, 5, 1, 1, 1, 1, 5]
def baseStart_1761431 : Nat := 118140960795 + 1761431 * 2 ^ 59
def prefixEnd_1761431 : Nat := 4983230072969 + 3 ^ 40 * 1761431 * 2
def baseEnd_1761431 : Nat := 602973828486535417874555

theorem tailTrace_1761431 : CollatzResearch.WordTrace tailWord_1761431 prefixEnd_1761431 602973828486535417874555 := by
  unfold tailWord_1761431
  simp only [CollatzResearch.WordTrace]
  refine ⟨64244666481643790309732147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42829777654429193539821431 64244666481643790309732147)
  ·
    refine ⟨96366999722465685464598221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64244666481643790309732147 96366999722465685464598221)
    ·
      refine ⟨36137624895924632049224333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96366999722465685464598221 36137624895924632049224333)
      ·
        refine ⟨13551609335971737018459125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36137624895924632049224333 13551609335971737018459125)
        ·
          refine ⟨1270463375247350345480543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13551609335971737018459125 1270463375247350345480543)
          ·
            refine ⟨1905695062871025518220815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1270463375247350345480543 1905695062871025518220815)
            ·
              refine ⟨2858542594306538277331223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1905695062871025518220815 2858542594306538277331223)
              ·
                refine ⟨4287813891459807415996835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2858542594306538277331223 4287813891459807415996835)
                ·
                  refine ⟨6431720837189711123995253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4287813891459807415996835 6431720837189711123995253)
                  ·
                    refine ⟨602973828486535417874555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6431720837189711123995253 602973828486535417874555)
                    ·
                      rfl

theorem cell22_1761431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 1, 5].length) (baseStart_1761431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1761431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1761431 prefixEnd_1761431 := by exact prefixLift 1761431
  have htrace : WordTrace (prefixWord ++ tailWord_1761431) baseStart_1761431 baseEnd_1761431 := by
    simpa [prefixWord, tailWord_1761431, baseEnd_1761431] using wordTrace_append hprefix tailTrace_1761431
  have hstable : (prefixWord ++ tailWord_1761431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761431).length < 2 ^ (prefixWord ++ tailWord_1761431).sum := by decide
  have hdescent : baseEnd_1761431 < baseStart_1761431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761450 : List Nat := [3, 1, 5, 1, 3, 1, 1, 3, 4]
def baseStart_1761450 : Nat := 118140960795 + 1761450 * 2 ^ 59
def prefixEnd_1761450 : Nat := 4983230072969 + 3 ^ 40 * 1761450 * 2
def baseEnd_1761450 : Nat := 200993444191608567216499

theorem tailTrace_1761450 : CollatzResearch.WordTrace tailWord_1761450 prefixEnd_1761450 200993444191608567216499 := by
  unfold tailWord_1761450
  simp only [CollatzResearch.WordTrace]
  refine ⟨16061339867143739138668451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42830239645716637703115869 16061339867143739138668451)
  ·
    refine ⟨24092009800715608708002677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16061339867143739138668451 24092009800715608708002677)
    ·
      refine ⟨2258625918817088316375251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24092009800715608708002677 2258625918817088316375251)
      ·
        refine ⟨3387938878225632474562877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2258625918817088316375251 3387938878225632474562877)
        ·
          refine ⟨1270477079334612177961079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3387938878225632474562877 1270477079334612177961079)
          ·
            refine ⟨1905715619001918266941619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1270477079334612177961079 1905715619001918266941619)
            ·
              refine ⟨2858573428502877400412429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1905715619001918266941619 2858573428502877400412429)
              ·
                refine ⟨1071965035688579025154661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2858573428502877400412429 1071965035688579025154661)
                ·
                  refine ⟨200993444191608567216499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1071965035688579025154661 200993444191608567216499)
                  ·
                    rfl

theorem cell22_1761450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 4].length) (baseStart_1761450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1761450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1761450 prefixEnd_1761450 := by exact prefixLift 1761450
  have htrace : WordTrace (prefixWord ++ tailWord_1761450) baseStart_1761450 baseEnd_1761450 := by
    simpa [prefixWord, tailWord_1761450, baseEnd_1761450] using wordTrace_append hprefix tailTrace_1761450
  have hstable : (prefixWord ++ tailWord_1761450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761450).length < 2 ^ (prefixWord ++ tailWord_1761450).sum := by decide
  have hdescent : baseEnd_1761450 < baseStart_1761450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761461 : List Nat := [1, 3, 3, 4, 2, 1, 8]
def baseStart_1761461 : Nat := 118140960795 + 1761461 * 2 ^ 59
def prefixEnd_1761461 : Nat := 4983230072969 + 3 ^ 40 * 1761461 * 2
def baseEnd_1761461 : Nat := 22332744374060197763869

theorem tailTrace_1761461 : CollatzResearch.WordTrace tailWord_1761461 prefixEnd_1761461 22332744374060197763869 := by
  unfold tailWord_1761461
  simp only [CollatzResearch.WordTrace]
  refine ⟨64245760671535105433324237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42830507114356736955549491 64245760671535105433324237)
  ·
    refine ⟨24092160251825664537496589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64245760671535105433324237 24092160251825664537496589)
    ·
      refine ⟨9034560094434624201561221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24092160251825664537496589 9034560094434624201561221)
      ·
        refine ⟨1693980017706492037792729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9034560094434624201561221 1693980017706492037792729)
        ·
          refine ⟨1270485013279869028344547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1693980017706492037792729 1270485013279869028344547)
          ·
            refine ⟨1905727519919803542516821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1270485013279869028344547 1905727519919803542516821)
            ·
              refine ⟨22332744374060197763869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1905727519919803542516821 22332744374060197763869)
              ·
                rfl

theorem cell22_1761461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 8].length) (baseStart_1761461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1761461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1761461 prefixEnd_1761461 := by exact prefixLift 1761461
  have htrace : WordTrace (prefixWord ++ tailWord_1761461) baseStart_1761461 baseEnd_1761461 := by
    simpa [prefixWord, tailWord_1761461, baseEnd_1761461] using wordTrace_append hprefix tailTrace_1761461
  have hstable : (prefixWord ++ tailWord_1761461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761461).length < 2 ^ (prefixWord ++ tailWord_1761461).sum := by decide
  have hdescent : baseEnd_1761461 < baseStart_1761461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761472 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 7]
def baseStart_1761472 : Nat := 118140960795 + 1761472 * 2 ^ 59
def prefixEnd_1761472 : Nat := 4983230072969 + 3 ^ 40 * 1761472 * 2
def baseEnd_1761472 : Nat := 200995954541474992533143

theorem tailTrace_1761472 : CollatzResearch.WordTrace tailWord_1761472 prefixEnd_1761472 200995954541474992533143 := by
  unfold tailWord_1761472
  simp only [CollatzResearch.WordTrace]
  refine ⟨32123080937247627155987335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42830774582996836207983113 32123080937247627155987335)
  ·
    refine ⟨48184621405871440733981003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32123080937247627155987335 48184621405871440733981003)
    ·
      refine ⟨72276932108807161100971505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48184621405871440733981003 72276932108807161100971505)
      ·
        refine ⟨54207699081605370825728629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72276932108807161100971505 54207699081605370825728629)
        ·
          refine ⟨5081971788900503514912059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54207699081605370825728629 5081971788900503514912059)
          ·
            refine ⟨7622957683350755272368089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5081971788900503514912059 7622957683350755272368089)
            ·
              refine ⟨5717218262513066454276067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7622957683350755272368089 5717218262513066454276067)
              ·
                refine ⟨8575827393769599681414101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5717218262513066454276067 8575827393769599681414101)
                ·
                  refine ⟨200995954541474992533143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8575827393769599681414101 200995954541474992533143)
                  ·
                    rfl

theorem cell22_1761472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 7].length) (baseStart_1761472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1761472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1761472 prefixEnd_1761472 := by exact prefixLift 1761472
  have htrace : WordTrace (prefixWord ++ tailWord_1761472) baseStart_1761472 baseEnd_1761472 := by
    simpa [prefixWord, tailWord_1761472, baseEnd_1761472] using wordTrace_append hprefix tailTrace_1761472
  have hstable : (prefixWord ++ tailWord_1761472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761472).length < 2 ^ (prefixWord ++ tailWord_1761472).sum := by decide
  have hdescent : baseEnd_1761472 < baseStart_1761472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761476 : List Nat := [2, 3, 3, 1, 2, 1, 3, 1, 3, 3]
def baseStart_1761476 : Nat := 118140960795 + 1761476 * 2 ^ 59
def prefixEnd_1761476 : Nat := 4983230072969 + 3 ^ 40 * 1761476 * 2
def baseEnd_1761476 : Nat := 602989232906170300499417

theorem tailTrace_1761476 : CollatzResearch.WordTrace tailWord_1761476 prefixEnd_1761476 602989232906170300499417 := by
  unfold tailWord_1761476
  simp only [CollatzResearch.WordTrace]
  refine ⟨32123153883240381497560141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42830871844320508663413521 32123153883240381497560141)
  ·
    refine ⟨12046182706215143061585053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32123153883240381497560141 12046182706215143061585053)
    ·
      refine ⟨4517318514830678648094395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12046182706215143061585053 4517318514830678648094395)
      ·
        refine ⟨6775977772246017972141593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4517318514830678648094395 6775977772246017972141593)
        ·
          refine ⟨5081983329184513479106195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6775977772246017972141593 5081983329184513479106195)
          ·
            refine ⟨7622974993776770218659293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5081983329184513479106195 7622974993776770218659293)
            ·
              refine ⟨2858615622666288831997235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7622974993776770218659293 2858615622666288831997235)
              ·
                refine ⟨4287923433999433247995853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2858615622666288831997235 4287923433999433247995853)
                ·
                  refine ⟨1607971287749787467998445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4287923433999433247995853 1607971287749787467998445)
                  ·
                    refine ⟨602989232906170300499417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1607971287749787467998445 602989232906170300499417)
                    ·
                      rfl

theorem cell22_1761476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_1761476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1761476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1761476 prefixEnd_1761476 := by exact prefixLift 1761476
  have htrace : WordTrace (prefixWord ++ tailWord_1761476) baseStart_1761476 baseEnd_1761476 := by
    simpa [prefixWord, tailWord_1761476, baseEnd_1761476] using wordTrace_append hprefix tailTrace_1761476
  have hstable : (prefixWord ++ tailWord_1761476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761476).length < 2 ^ (prefixWord ++ tailWord_1761476).sum := by decide
  have hdescent : baseEnd_1761476 < baseStart_1761476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761489 : List Nat := [1, 2, 2, 1, 2, 2, 6, 1, 5]
def baseStart_1761489 : Nat := 118140960795 + 1761489 * 2 ^ 59
def prefixEnd_1761489 : Nat := 4983230072969 + 3 ^ 40 * 1761489 * 2
def baseEnd_1761489 : Nat := 200997894357280866641459

theorem tailTrace_1761489 : CollatzResearch.WordTrace tailWord_1761489 prefixEnd_1761489 200997894357280866641459 := by
  unfold tailWord_1761489
  simp only [CollatzResearch.WordTrace]
  refine ⟨64246781915433666215343521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42831187943622444143562347 64246781915433666215343521)
  ·
    refine ⟨48185086436575249661507641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64246781915433666215343521 48185086436575249661507641)
    ·
      refine ⟨36138814827431437246130731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48185086436575249661507641 36138814827431437246130731)
      ·
        refine ⟨54208222241147155869196097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36138814827431437246130731 54208222241147155869196097)
        ·
          refine ⟨40656166680860366901897073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54208222241147155869196097 40656166680860366901897073)
          ·
            refine ⟨30492125010645275176422805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40656166680860366901897073 30492125010645275176422805)
            ·
              refine ⟨1429318359873997273894819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30492125010645275176422805 1429318359873997273894819)
              ·
                refine ⟨2143977539810995910842229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1429318359873997273894819 2143977539810995910842229)
                ·
                  refine ⟨200997894357280866641459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2143977539810995910842229 200997894357280866641459)
                  ·
                    rfl

theorem cell22_1761489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 5].length) (baseStart_1761489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1761489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1761489 prefixEnd_1761489 := by exact prefixLift 1761489
  have htrace : WordTrace (prefixWord ++ tailWord_1761489) baseStart_1761489 baseEnd_1761489 := by
    simpa [prefixWord, tailWord_1761489, baseEnd_1761489] using wordTrace_append hprefix tailTrace_1761489
  have hstable : (prefixWord ++ tailWord_1761489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761489).length < 2 ^ (prefixWord ++ tailWord_1761489).sum := by decide
  have hdescent : baseEnd_1761489 < baseStart_1761489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761534 : List Nat := [4, 2, 2, 1, 1, 1, 2, 3, 6]
def baseStart_1761534 : Nat := 118140960795 + 1761534 * 2 ^ 59
def prefixEnd_1761534 : Nat := 4983230072969 + 3 ^ 40 * 1761534 * 2
def baseEnd_1761534 : Nat := 201003029163825827516413

theorem tailTrace_1761534 : CollatzResearch.WordTrace tailWord_1761534 prefixEnd_1761534 201003029163825827516413 := by
  unfold tailWord_1761534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8031052900033829862591457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42832282133513759267154437 8031052900033829862591457)
  ·
    refine ⟨6023289675025372396943593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8031052900033829862591457 6023289675025372396943593)
    ·
      refine ⟨4517467256269029297707695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6023289675025372396943593 4517467256269029297707695)
      ·
        refine ⟨6776200884403543946561543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4517467256269029297707695 6776200884403543946561543)
        ·
          refine ⟨10164301326605315919842315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6776200884403543946561543 10164301326605315919842315)
          ·
            refine ⟨15246451989907973879763473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10164301326605315919842315 15246451989907973879763473)
            ·
              refine ⟨11434838992430980409822605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15246451989907973879763473 11434838992430980409822605)
              ·
                refine ⟨4288064622161617653683477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11434838992430980409822605 4288064622161617653683477)
                ·
                  refine ⟨201003029163825827516413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4288064622161617653683477 201003029163825827516413)
                  ·
                    rfl

theorem cell22_1761534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_1761534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1761534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1761534 prefixEnd_1761534 := by exact prefixLift 1761534
  have htrace : WordTrace (prefixWord ++ tailWord_1761534) baseStart_1761534 baseEnd_1761534 := by
    simpa [prefixWord, tailWord_1761534, baseEnd_1761534] using wordTrace_append hprefix tailTrace_1761534
  have hstable : (prefixWord ++ tailWord_1761534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761534).length < 2 ^ (prefixWord ++ tailWord_1761534).sum := by decide
  have hdescent : baseEnd_1761534 < baseStart_1761534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761547 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 1, 6]
def baseStart_1761547 : Nat := 118140960795 + 1761547 * 2 ^ 59
def prefixEnd_1761547 : Nat := 4983230072969 + 3 ^ 40 * 1761547 * 2
def baseEnd_1761547 : Nat := 603013537657149781974199

theorem tailTrace_1761547 : CollatzResearch.WordTrace tailWord_1761547 prefixEnd_1761547 603013537657149781974199 := by
  unfold tailWord_1761547
  simp only [CollatzResearch.WordTrace]
  refine ⟨64248897349223542120954895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42832598232815694747303263 64248897349223542120954895)
  ·
    refine ⟨96373346023835313181432343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64248897349223542120954895 96373346023835313181432343)
    ·
      refine ⟨144560019035752969772148515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96373346023835313181432343 144560019035752969772148515)
      ·
        refine ⟨216840028553629454658222773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144560019035752969772148515 216840028553629454658222773)
        ·
          refine ⟨20328752676902761374208385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 216840028553629454658222773 20328752676902761374208385)
          ·
            refine ⟨15246564507677071030656289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20328752676902761374208385 15246564507677071030656289)
            ·
              refine ⟨11434923380757803272992217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15246564507677071030656289 11434923380757803272992217)
              ·
                refine ⟨8576192535568352454744163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11434923380757803272992217 8576192535568352454744163)
                ·
                  refine ⟨12864288803352528682116245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8576192535568352454744163 12864288803352528682116245)
                  ·
                    refine ⟨603013537657149781974199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12864288803352528682116245 603013537657149781974199)
                    ·
                      rfl

theorem cell22_1761547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 6].length) (baseStart_1761547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1761547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1761547 prefixEnd_1761547 := by exact prefixLift 1761547
  have htrace : WordTrace (prefixWord ++ tailWord_1761547) baseStart_1761547 baseEnd_1761547 := by
    simpa [prefixWord, tailWord_1761547, baseEnd_1761547] using wordTrace_append hprefix tailTrace_1761547
  have hstable : (prefixWord ++ tailWord_1761547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761547).length < 2 ^ (prefixWord ++ tailWord_1761547).sum := by decide
  have hdescent : baseEnd_1761547 < baseStart_1761547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761592 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 1, 8]
def baseStart_1761592 : Nat := 118140960795 + 1761592 * 2 ^ 59
def prefixEnd_1761592 : Nat := 4983230072969 + 3 ^ 40 * 1761592 * 2
def baseEnd_1761592 : Nat := 603028942076784664599061

theorem tailTrace_1761592 : CollatzResearch.WordTrace tailWord_1761592 prefixEnd_1761592 603028942076784664599061 := by
  unfold tailWord_1761592
  simp only [CollatzResearch.WordTrace]
  refine ⟨32125269317030257403171515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42833692422707009870895353 32125269317030257403171515)
  ·
    refine ⟨48187903975545386104757273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32125269317030257403171515 48187903975545386104757273)
    ·
      refine ⟨36140927981659039578567955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48187903975545386104757273 36140927981659039578567955)
      ·
        refine ⟨54211391972488559367851933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36140927981659039578567955 54211391972488559367851933)
        ·
          refine ⟨20329271989683209762944475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54211391972488559367851933 20329271989683209762944475)
          ·
            refine ⟨30493907984524814644416713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20329271989683209762944475 30493907984524814644416713)
            ·
              refine ⟨22870430988393610983312535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30493907984524814644416713 22870430988393610983312535)
              ·
                refine ⟨34305646482590416474968803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22870430988393610983312535 34305646482590416474968803)
                ·
                  refine ⟨51458469723885624712453205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34305646482590416474968803 51458469723885624712453205)
                  ·
                    refine ⟨603028942076784664599061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51458469723885624712453205 603028942076784664599061)
                    ·
                      rfl

theorem cell22_1761592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_1761592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1761592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1761592 prefixEnd_1761592 := by exact prefixLift 1761592
  have htrace : WordTrace (prefixWord ++ tailWord_1761592) baseStart_1761592 baseEnd_1761592 := by
    simpa [prefixWord, tailWord_1761592, baseEnd_1761592] using wordTrace_append hprefix tailTrace_1761592
  have hstable : (prefixWord ++ tailWord_1761592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761592).length < 2 ^ (prefixWord ++ tailWord_1761592).sum := by decide
  have hdescent : baseEnd_1761592 < baseStart_1761592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761645 : List Nat := [1, 5, 1, 1, 1, 2, 5, 2, 1, 3]
def baseStart_1761645 : Nat := 118140960795 + 1761645 * 2 ^ 59
def prefixEnd_1761645 : Nat := 4983230072969 + 3 ^ 40 * 1761645 * 2
def baseEnd_1761645 : Nat := 603047085059910193023899

theorem tailTrace_1761645 : CollatzResearch.WordTrace tailWord_1761645 prefixEnd_1761645 603047085059910193023899 := by
  unfold tailWord_1761645
  simp only [CollatzResearch.WordTrace]
  refine ⟨64252471702868504858022389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42834981135245669905348259 64252471702868504858022389)
  ·
    refine ⟨6023669222143922330439599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64252471702868504858022389 6023669222143922330439599)
    ·
      refine ⟨9035503833215883495659399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6023669222143922330439599 9035503833215883495659399)
      ·
        refine ⟨13553255749823825243489099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9035503833215883495659399 13553255749823825243489099)
        ·
          refine ⟨20329883624735737865233649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13553255749823825243489099 20329883624735737865233649)
          ·
            refine ⟨15247412718551803398925237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20329883624735737865233649 15247412718551803398925237)
            ·
              refine ⟨1429444942364231568649241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15247412718551803398925237 1429444942364231568649241)
              ·
                refine ⟨1072083706773173676486931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1429444942364231568649241 1072083706773173676486931)
                ·
                  refine ⟨1608125560159760514730397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1072083706773173676486931 1608125560159760514730397)
                  ·
                    refine ⟨603047085059910193023899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1608125560159760514730397 603047085059910193023899)
                    ·
                      rfl

theorem cell22_1761645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_1761645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1761645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1761645 prefixEnd_1761645 := by exact prefixLift 1761645
  have htrace : WordTrace (prefixWord ++ tailWord_1761645) baseStart_1761645 baseEnd_1761645 := by
    simpa [prefixWord, tailWord_1761645, baseEnd_1761645] using wordTrace_append hprefix tailTrace_1761645
  have hstable : (prefixWord ++ tailWord_1761645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761645).length < 2 ^ (prefixWord ++ tailWord_1761645).sum := by decide
  have hdescent : baseEnd_1761645 < baseStart_1761645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761703 : List Nat := [1, 1, 6, 1, 1, 3, 1, 4, 4]
def baseStart_1761703 : Nat := 118140960795 + 1761703 * 2 ^ 59
def prefixEnd_1761703 : Nat := 4983230072969 + 3 ^ 40 * 1761703 * 2
def baseEnd_1761703 : Nat := 201022313215072458357907

theorem tailTrace_1761703 : CollatzResearch.WordTrace tailWord_1761703 prefixEnd_1761703 201022313215072458357907 := by
  unfold tailWord_1761703
  simp only [CollatzResearch.WordTrace]
  refine ⟨64254587136658380763633763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42836391424438920509089175 64254587136658380763633763)
  ·
    refine ⟨96381880704987571145450645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64254587136658380763633763 96381880704987571145450645)
    ·
      refine ⟨4517900658046292397442999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 96381880704987571145450645 4517900658046292397442999)
      ·
        refine ⟨6776850987069438596164499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4517900658046292397442999 6776850987069438596164499)
        ·
          refine ⟨10165276480604157894246749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6776850987069438596164499 10165276480604157894246749)
          ·
            refine ⟨3811978680226559210342531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10165276480604157894246749 3811978680226559210342531)
            ·
              refine ⟨5717968020339838815513797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3811978680226559210342531 5717968020339838815513797)
              ·
                refine ⟨1072119003813719777908837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5717968020339838815513797 1072119003813719777908837)
                ·
                  refine ⟨201022313215072458357907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1072119003813719777908837 201022313215072458357907)
                  ·
                    rfl

theorem cell22_1761703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 4].length) (baseStart_1761703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1761703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1761703 prefixEnd_1761703 := by exact prefixLift 1761703
  have htrace : WordTrace (prefixWord ++ tailWord_1761703) baseStart_1761703 baseEnd_1761703 := by
    simpa [prefixWord, tailWord_1761703, baseEnd_1761703] using wordTrace_append hprefix tailTrace_1761703
  have hstable : (prefixWord ++ tailWord_1761703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761703).length < 2 ^ (prefixWord ++ tailWord_1761703).sum := by decide
  have hdescent : baseEnd_1761703 < baseStart_1761703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761853 : List Nat := [1, 4, 1, 3, 2, 2, 1, 2, 1, 5]
def baseStart_1761853 : Nat := 118140960795 + 1761853 * 2 ^ 59
def prefixEnd_1761853 : Nat := 4983230072969 + 3 ^ 40 * 1761853 * 2
def baseEnd_1761853 : Nat := 603118287710666983823261

theorem tailTrace_1761853 : CollatzResearch.WordTrace tailWord_1761853 prefixEnd_1761853 603118287710666983823261 := by
  unfold tailWord_1761853
  simp only [CollatzResearch.WordTrace]
  refine ⟨64260058086114956381594213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42840038724076637587729475 64260058086114956381594213)
  ·
    refine ⟨12048760891146554321548915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64260058086114956381594213 12048760891146554321548915)
    ·
      refine ⟨18073141336719831482323373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12048760891146554321548915 18073141336719831482323373)
      ·
        refine ⟨6777428001269936805871265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18073141336719831482323373 6777428001269936805871265)
        ·
          refine ⟨5083071000952452604403449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6777428001269936805871265 5083071000952452604403449)
          ·
            refine ⟨3812303250714339453302587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5083071000952452604403449 3812303250714339453302587)
            ·
              refine ⟨5718454876071509179953881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3812303250714339453302587 5718454876071509179953881)
              ·
                refine ⟨4288841157053631884965411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5718454876071509179953881 4288841157053631884965411)
                ·
                  refine ⟨6433261735580447827448117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4288841157053631884965411 6433261735580447827448117)
                  ·
                    refine ⟨603118287710666983823261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6433261735580447827448117 603118287710666983823261)
                    ·
                      rfl

theorem cell22_1761853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_1761853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1761853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1761853 prefixEnd_1761853 := by exact prefixLift 1761853
  have htrace : WordTrace (prefixWord ++ tailWord_1761853) baseStart_1761853 baseEnd_1761853 := by
    simpa [prefixWord, tailWord_1761853, baseEnd_1761853] using wordTrace_append hprefix tailTrace_1761853
  have hstable : (prefixWord ++ tailWord_1761853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761853).length < 2 ^ (prefixWord ++ tailWord_1761853).sum := by decide
  have hdescent : baseEnd_1761853 < baseStart_1761853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761966 : List Nat := [4, 1, 4, 1, 1, 3, 1, 3, 1, 3]
def baseStart_1761966 : Nat := 118140960795 + 1761966 * 2 ^ 59
def prefixEnd_1761966 : Nat := 4983230072969 + 3 ^ 40 * 1761966 * 2
def baseEnd_1761966 : Nat := 603156969919972355747915

theorem tailTrace_1761966 : CollatzResearch.WordTrace tailWord_1761966 prefixEnd_1761966 603156969919972355747915 := by
  unfold tailWord_1761966
  simp only [CollatzResearch.WordTrace]
  refine ⟨8033022441838197085057219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42842786356470384453638501 8033022441838197085057219)
  ·
    refine ⟨12049533662757295627585829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8033022441838197085057219 12049533662757295627585829)
    ·
      refine ⟨2259287561766992930172343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12049533662757295627585829 2259287561766992930172343)
      ·
        refine ⟨3388931342650489395258515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2259287561766992930172343 3388931342650489395258515)
        ·
          refine ⟨5083397013975734092887773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3388931342650489395258515 5083397013975734092887773)
          ·
            refine ⟨1906273880240900284832915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5083397013975734092887773 1906273880240900284832915)
            ·
              refine ⟨2859410820361350427249373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1906273880240900284832915 2859410820361350427249373)
              ·
                refine ⟨1072279057635506410218515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2859410820361350427249373 1072279057635506410218515)
                ·
                  refine ⟨1608418586453259615327773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1072279057635506410218515 1608418586453259615327773)
                  ·
                    refine ⟨603156969919972355747915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1608418586453259615327773 603156969919972355747915)
                    ·
                      rfl

theorem cell22_1761966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_1761966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1761966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1761966 prefixEnd_1761966 := by exact prefixLift 1761966
  have htrace : WordTrace (prefixWord ++ tailWord_1761966) baseStart_1761966 baseEnd_1761966 := by
    simpa [prefixWord, tailWord_1761966, baseEnd_1761966] using wordTrace_append hprefix tailTrace_1761966
  have hstable : (prefixWord ++ tailWord_1761966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761966).length < 2 ^ (prefixWord ++ tailWord_1761966).sum := by decide
  have hdescent : baseEnd_1761966 < baseStart_1761966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762020 : List Nat := [2, 3, 1, 1, 1, 5, 2, 1, 2, 4]
def baseStart_1762020 : Nat := 118140960795 + 1762020 * 2 ^ 59
def prefixEnd_1762020 : Nat := 4983230072969 + 3 ^ 40 * 1762020 * 2
def baseEnd_1762020 : Nat := 603175455223534214897749

theorem tailTrace_1762020 : CollatzResearch.WordTrace tailWord_1762020 prefixEnd_1762020 603175455223534214897749 := by
  unfold tailWord_1762020
  simp only [CollatzResearch.WordTrace]
  refine ⟨32133074538254971951461757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42844099384339962601949009 32133074538254971951461757)
  ·
    refine ⟨12049902951845614481798159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32133074538254971951461757 12049902951845614481798159)
    ·
      refine ⟨18074854427768421722697239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12049902951845614481798159 18074854427768421722697239)
      ·
        refine ⟨27112281641652632584045859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18074854427768421722697239 27112281641652632584045859)
        ·
          refine ⟨40668422462478948876068789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27112281641652632584045859 40668422462478948876068789)
          ·
            refine ⟨3812664605857401457131449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40668422462478948876068789 3812664605857401457131449)
            ·
              refine ⟨2859498454393051092848587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3812664605857401457131449 2859498454393051092848587)
              ·
                refine ⟨4289247681589576639272881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2859498454393051092848587 4289247681589576639272881)
                ·
                  refine ⟨3216935761192182479454661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4289247681589576639272881 3216935761192182479454661)
                  ·
                    refine ⟨603175455223534214897749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3216935761192182479454661 603175455223534214897749)
                    ·
                      rfl

theorem cell22_1762020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_1762020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1762020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1762020 prefixEnd_1762020 := by exact prefixLift 1762020
  have htrace : WordTrace (prefixWord ++ tailWord_1762020) baseStart_1762020 baseEnd_1762020 := by
    simpa [prefixWord, tailWord_1762020, baseEnd_1762020] using wordTrace_append hprefix tailTrace_1762020
  have hstable : (prefixWord ++ tailWord_1762020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762020).length < 2 ^ (prefixWord ++ tailWord_1762020).sum := by decide
  have hdescent : baseEnd_1762020 < baseStart_1762020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762063 : List Nat := [1, 1, 2, 1, 1, 1, 5, 5, 5]
def baseStart_1762063 : Nat := 118140960795 + 1762063 * 2 ^ 59
def prefixEnd_1762063 : Nat := 4983230072969 + 3 ^ 40 * 1762063 * 2
def baseEnd_1762063 : Nat := 201063391667432145357539

theorem tailTrace_1762063 : CollatzResearch.WordTrace tailWord_1762063 prefixEnd_1762063 201063391667432145357539 := by
  unfold tailWord_1762063
  simp only [CollatzResearch.WordTrace]
  refine ⟨64267717415354162246738843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42845144943569441497825895 64267717415354162246738843)
  ·
    refine ⟨96401576123031243370108265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64267717415354162246738843 96401576123031243370108265)
    ·
      refine ⟨72301182092273432527581199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96401576123031243370108265 72301182092273432527581199)
      ·
        refine ⟨108451773138410148791371799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72301182092273432527581199 108451773138410148791371799)
        ·
          refine ⟨162677659707615223187057699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108451773138410148791371799 162677659707615223187057699)
          ·
            refine ⟨244016489561422834780586549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162677659707615223187057699 244016489561422834780586549)
            ·
              refine ⟨22876545896383390760679989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 244016489561422834780586549 22876545896383390760679989)
              ·
                refine ⟨2144676177785942883813749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22876545896383390760679989 2144676177785942883813749)
                ·
                  refine ⟨201063391667432145357539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2144676177785942883813749 201063391667432145357539)
                  ·
                    rfl

theorem cell22_1762063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 5].length) (baseStart_1762063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1762063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1762063 prefixEnd_1762063 := by exact prefixLift 1762063
  have htrace : WordTrace (prefixWord ++ tailWord_1762063) baseStart_1762063 baseEnd_1762063 := by
    simpa [prefixWord, tailWord_1762063, baseEnd_1762063] using wordTrace_append hprefix tailTrace_1762063
  have hstable : (prefixWord ++ tailWord_1762063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762063).length < 2 ^ (prefixWord ++ tailWord_1762063).sum := by decide
  have hdescent : baseEnd_1762063 < baseStart_1762063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762157 : List Nat := [1, 5, 1, 1, 1, 1, 1, 6, 2, 3]
def baseStart_1762157 : Nat := 118140960795 + 1762157 * 2 ^ 59
def prefixEnd_1762157 : Nat := 4983230072969 + 3 ^ 40 * 1762157 * 2
def baseEnd_1762157 : Nat := 603222353123311524222329

theorem tailTrace_1762157 : CollatzResearch.WordTrace tailWord_1762157 prefixEnd_1762157 603222353123311524222329 := by
  unfold tailWord_1762157
  simp only [CollatzResearch.WordTrace]
  refine ⟨64271145877013616300660725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42847430584675744200440483 64271145877013616300660725)
  ·
    refine ⟨6025419925970026528186943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64271145877013616300660725 6025419925970026528186943)
    ·
      refine ⟨9038129888955039792280415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6025419925970026528186943 9038129888955039792280415)
      ·
        refine ⟨13557194833432559688420623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9038129888955039792280415 13557194833432559688420623)
        ·
          refine ⟨20335792250148839532630935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13557194833432559688420623 20335792250148839532630935)
          ·
            refine ⟨30503688375223259298946403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20335792250148839532630935 30503688375223259298946403)
            ·
              refine ⟨45755532562834888948419605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30503688375223259298946403 45755532562834888948419605)
              ·
                refine ⟨2144790588882885419457169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45755532562834888948419605 2144790588882885419457169)
                ·
                  refine ⟨1608592941662164064592877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2144790588882885419457169 1608592941662164064592877)
                  ·
                    refine ⟨603222353123311524222329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1608592941662164064592877 603222353123311524222329)
                    ·
                      rfl

theorem cell22_1762157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_1762157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1762157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1762157 prefixEnd_1762157 := by exact prefixLift 1762157
  have htrace : WordTrace (prefixWord ++ tailWord_1762157) baseStart_1762157 baseEnd_1762157 := by
    simpa [prefixWord, tailWord_1762157, baseEnd_1762157] using wordTrace_append hprefix tailTrace_1762157
  have hstable : (prefixWord ++ tailWord_1762157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762157).length < 2 ^ (prefixWord ++ tailWord_1762157).sum := by decide
  have hdescent : baseEnd_1762157 < baseStart_1762157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762168 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 2, 7]
def baseStart_1762168 : Nat := 118140960795 + 1762168 * 2 ^ 59
def prefixEnd_1762168 : Nat := 4983230072969 + 3 ^ 40 * 1762168 * 2
def baseEnd_1762168 : Nat := 603226118648111162197295

theorem tailTrace_1762168 : CollatzResearch.WordTrace tailWord_1762168 prefixEnd_1762168 603226118648111162197295 := by
  unfold tailWord_1762168
  simp only [CollatzResearch.WordTrace]
  refine ⟨32135773539986882589655579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42847698053315843452874105 32135773539986882589655579)
  ·
    refine ⟨48203660309980323884483369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32135773539986882589655579 48203660309980323884483369)
    ·
      refine ⟨36152745232485242913362527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48203660309980323884483369 36152745232485242913362527)
      ·
        refine ⟨54229117848727864370043791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36152745232485242913362527 54229117848727864370043791)
        ·
          refine ⟨81343676773091796555065687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54229117848727864370043791 81343676773091796555065687)
          ·
            refine ⟨122015515159637694832598531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81343676773091796555065687 122015515159637694832598531)
            ·
              refine ⟨183023272739456542248897797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122015515159637694832598531 183023272739456542248897797)
              ·
                refine ⟨34316863638648101671668337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183023272739456542248897797 34316863638648101671668337)
                ·
                  refine ⟨25737647728986076253751253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34316863638648101671668337 25737647728986076253751253)
                  ·
                    refine ⟨603226118648111162197295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25737647728986076253751253 603226118648111162197295)
                    ·
                      rfl

theorem cell22_1762168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_1762168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1762168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1762168 prefixEnd_1762168 := by exact prefixLift 1762168
  have htrace : WordTrace (prefixWord ++ tailWord_1762168) baseStart_1762168 baseEnd_1762168 := by
    simpa [prefixWord, tailWord_1762168, baseEnd_1762168] using wordTrace_append hprefix tailTrace_1762168
  have hstable : (prefixWord ++ tailWord_1762168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762168).length < 2 ^ (prefixWord ++ tailWord_1762168).sum := by decide
  have hdescent : baseEnd_1762168 < baseStart_1762168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762178 : List Nat := [3, 4, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_1762178 : Nat := 118140960795 + 1762178 * 2 ^ 59
def prefixEnd_1762178 : Nat := 4983230072969 + 3 ^ 40 * 1762178 * 2
def baseEnd_1762178 : Nat := 603229541852474469447265

theorem tailTrace_1762178 : CollatzResearch.WordTrace tailWord_1762178 prefixEnd_1762178 603229541852474469447265 := by
  unfold tailWord_1762178
  simp only [CollatzResearch.WordTrace]
  refine ⟨16067977952484384221793797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42847941206625024591450125 16067977952484384221793797)
  ·
    refine ⟨3012745866090822041586337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16067977952484384221793797 3012745866090822041586337)
    ·
      refine ⟨2259559399568116531189753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3012745866090822041586337 2259559399568116531189753)
      ·
        refine ⟨1694669549676087398392315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2259559399568116531189753 1694669549676087398392315)
        ·
          refine ⟨2542004324514131097588473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1694669549676087398392315 2542004324514131097588473)
          ·
            refine ⟨1906503243385598323191355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2542004324514131097588473 1906503243385598323191355)
            ·
              refine ⟨2859754865078397484787033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1906503243385598323191355 2859754865078397484787033)
              ·
                refine ⟨2144816148808798113590275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2859754865078397484787033 2144816148808798113590275)
                ·
                  refine ⟨3217224223213197170385413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2144816148808798113590275 3217224223213197170385413)
                  ·
                    refine ⟨603229541852474469447265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3217224223213197170385413 603229541852474469447265)
                    ·
                      rfl

theorem cell22_1762178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_1762178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1762178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1762178 prefixEnd_1762178 := by exact prefixLift 1762178
  have htrace : WordTrace (prefixWord ++ tailWord_1762178) baseStart_1762178 baseEnd_1762178 := by
    simpa [prefixWord, tailWord_1762178, baseEnd_1762178] using wordTrace_append hprefix tailTrace_1762178
  have hstable : (prefixWord ++ tailWord_1762178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762178).length < 2 ^ (prefixWord ++ tailWord_1762178).sum := by decide
  have hdescent : baseEnd_1762178 < baseStart_1762178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762221 : List Nat := [1, 5, 2, 3, 2, 1, 1, 7]
def baseStart_1762221 : Nat := 118140960795 + 1762221 * 2 ^ 59
def prefixEnd_1762221 : Nat := 4983230072969 + 3 ^ 40 * 1762221 * 2
def baseEnd_1762221 : Nat := 67027140181248521180237

theorem tailTrace_1762221 : CollatzResearch.WordTrace tailWord_1762221 prefixEnd_1762221 67027140181248521180237 := by
  unfold tailWord_1762221
  simp only [CollatzResearch.WordTrace]
  refine ⟨64273480148781755230990517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42848986765854503487327011 64273480148781755230990517)
  ·
    refine ⟨6025638763948289552905361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64273480148781755230990517 6025638763948289552905361)
    ·
      refine ⟨4519229072961217164679021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6025638763948289552905361 4519229072961217164679021)
      ·
        refine ⟨1694710902360456436754633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4519229072961217164679021 1694710902360456436754633)
        ·
          refine ⟨1271033176770342327565975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1694710902360456436754633 1271033176770342327565975)
          ·
            refine ⟨1906549765155513491348963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1271033176770342327565975 1906549765155513491348963)
            ·
              refine ⟨2859824647733270237023445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1906549765155513491348963 2859824647733270237023445)
              ·
                refine ⟨67027140181248521180237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2859824647733270237023445 67027140181248521180237)
                ·
                  rfl

theorem cell22_1762221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 7].length) (baseStart_1762221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1762221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1762221 prefixEnd_1762221 := by exact prefixLift 1762221
  have htrace : WordTrace (prefixWord ++ tailWord_1762221) baseStart_1762221 baseEnd_1762221 := by
    simpa [prefixWord, tailWord_1762221, baseEnd_1762221] using wordTrace_append hprefix tailTrace_1762221
  have hstable : (prefixWord ++ tailWord_1762221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762221).length < 2 ^ (prefixWord ++ tailWord_1762221).sum := by decide
  have hdescent : baseEnd_1762221 < baseStart_1762221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762343 : List Nat := [1, 1, 7, 1, 1, 1, 4, 1, 2, 3]
def baseStart_1762343 : Nat := 118140960795 + 1762343 * 2 ^ 59
def prefixEnd_1762343 : Nat := 4983230072969 + 3 ^ 40 * 1762343 * 2
def baseEnd_1762343 : Nat := 603286024724469039071759

theorem tailTrace_1762343 : CollatzResearch.WordTrace tailWord_1762343 prefixEnd_1762343 603286024724469039071759 := by
  unfold tailWord_1762343
  simp only [CollatzResearch.WordTrace]
  refine ⟨64277929854339770066931683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42851953236226513377954455 64277929854339770066931683)
  ·
    refine ⟨96416894781509655100397525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64277929854339770066931683 96416894781509655100397525)
    ·
      refine ⟨2259770971441632541415567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 96416894781509655100397525 2259770971441632541415567)
      ·
        refine ⟨3389656457162448812123351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2259770971441632541415567 3389656457162448812123351)
        ·
          refine ⟨5084484685743673218185027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3389656457162448812123351 5084484685743673218185027)
          ·
            refine ⟨7626727028615509827277541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5084484685743673218185027 7626727028615509827277541)
            ·
              refine ⟨1430011317865408092614539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7626727028615509827277541 1430011317865408092614539)
              ·
                refine ⟨2145016976798112138921809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1430011317865408092614539 2145016976798112138921809)
                ·
                  refine ⟨1608762732598584104191357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2145016976798112138921809 1608762732598584104191357)
                  ·
                    refine ⟨603286024724469039071759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1608762732598584104191357 603286024724469039071759)
                    ·
                      rfl

theorem cell22_1762343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_1762343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1762343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1762343 prefixEnd_1762343 := by exact prefixLift 1762343
  have htrace : WordTrace (prefixWord ++ tailWord_1762343) baseStart_1762343 baseEnd_1762343 := by
    simpa [prefixWord, tailWord_1762343, baseEnd_1762343] using wordTrace_append hprefix tailTrace_1762343
  have hstable : (prefixWord ++ tailWord_1762343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762343).length < 2 ^ (prefixWord ++ tailWord_1762343).sum := by decide
  have hdescent : baseEnd_1762343 < baseStart_1762343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762382 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 2, 5]
def baseStart_1762382 : Nat := 118140960795 + 1762382 * 2 ^ 59
def prefixEnd_1762382 : Nat := 4983230072969 + 3 ^ 40 * 1762382 * 2
def baseEnd_1762382 : Nat := 603299375221485937346639

theorem tailTrace_1762382 : CollatzResearch.WordTrace tailWord_1762382 prefixEnd_1762382 603299375221485937346639 := by
  unfold tailWord_1762382
  simp only [CollatzResearch.WordTrace]
  refine ⟨8034919037649809965950175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42852901534132319818400933 8034919037649809965950175)
  ·
    refine ⟨12052378556474714948925263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8034919037649809965950175 12052378556474714948925263)
    ·
      refine ⟨18078567834712072423387895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12052378556474714948925263 18078567834712072423387895)
      ·
        refine ⟨27117851752068108635081843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18078567834712072423387895 27117851752068108635081843)
        ·
          refine ⟨40676777628102162952622765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27117851752068108635081843 40676777628102162952622765)
          ·
            refine ⟨15253791610538311107233537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40676777628102162952622765 15253791610538311107233537)
            ·
              refine ⟨11440343707903733330425153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15253791610538311107233537 11440343707903733330425153)
              ·
                refine ⟨8580257780927799997818865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11440343707903733330425153 8580257780927799997818865)
                ·
                  refine ⟨6435193335695849998364149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8580257780927799997818865 6435193335695849998364149)
                  ·
                    refine ⟨603299375221485937346639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6435193335695849998364149 603299375221485937346639)
                    ·
                      rfl

theorem cell22_1762382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_1762382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1762382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1762382 prefixEnd_1762382 := by exact prefixLift 1762382
  have htrace : WordTrace (prefixWord ++ tailWord_1762382) baseStart_1762382 baseEnd_1762382 := by
    simpa [prefixWord, tailWord_1762382, baseEnd_1762382] using wordTrace_append hprefix tailTrace_1762382
  have hstable : (prefixWord ++ tailWord_1762382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762382).length < 2 ^ (prefixWord ++ tailWord_1762382).sum := by decide
  have hdescent : baseEnd_1762382 < baseStart_1762382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762388 : List Nat := [2, 4, 1, 1, 1, 1, 6, 2, 1, 3]
def baseStart_1762388 : Nat := 118140960795 + 1762388 * 2 ^ 59
def prefixEnd_1762388 : Nat := 4983230072969 + 3 ^ 40 * 1762388 * 2
def baseEnd_1762388 : Nat := 603301429144103921696621

theorem tailTrace_1762388 : CollatzResearch.WordTrace tailWord_1762388 prefixEnd_1762388 603301429144103921696621 := by
  unfold tailWord_1762388
  simp only [CollatzResearch.WordTrace]
  refine ⟨32139785569588371376159909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42853047426117828501546545 32139785569588371376159909)
  ·
    refine ⟨6026209794297819633029983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32139785569588371376159909 6026209794297819633029983)
    ·
      refine ⟨9039314691446729449544975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6026209794297819633029983 9039314691446729449544975)
      ·
        refine ⟨13558972037170094174317463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9039314691446729449544975 13558972037170094174317463)
        ·
          refine ⟨20338458055755141261476195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13558972037170094174317463 20338458055755141261476195)
          ·
            refine ⟨30507687083632711892214293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20338458055755141261476195 30507687083632711892214293)
            ·
              refine ⟨1430047832045283369947545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30507687083632711892214293 1430047832045283369947545)
              ·
                refine ⟨1072535874033962527460659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1430047832045283369947545 1072535874033962527460659)
                ·
                  refine ⟨1608803811050943791190989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1072535874033962527460659 1608803811050943791190989)
                  ·
                    refine ⟨603301429144103921696621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1608803811050943791190989 603301429144103921696621)
                    ·
                      rfl

theorem cell22_1762388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_1762388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1762388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1762388 prefixEnd_1762388 := by exact prefixLift 1762388
  have htrace : WordTrace (prefixWord ++ tailWord_1762388) baseStart_1762388 baseEnd_1762388 := by
    simpa [prefixWord, tailWord_1762388, baseEnd_1762388] using wordTrace_append hprefix tailTrace_1762388
  have hstable : (prefixWord ++ tailWord_1762388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762388).length < 2 ^ (prefixWord ++ tailWord_1762388).sum := by decide
  have hdescent : baseEnd_1762388 < baseStart_1762388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762412 : List Nat := [2, 2, 1, 1, 3, 2, 3, 2, 6]
def baseStart_1762412 : Nat := 118140960795 + 1762412 * 2 ^ 59
def prefixEnd_1762412 : Nat := 4983230072969 + 3 ^ 40 * 1762412 * 2
def baseEnd_1762412 : Nat := 201103214944858619698849

theorem tailTrace_1762412 : CollatzResearch.WordTrace tailWord_1762412 prefixEnd_1762412 201103214944858619698849 := by
  unfold tailWord_1762412
  simp only [CollatzResearch.WordTrace]
  refine ⟨32140223245544897425596745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42853630994059863234128993 32140223245544897425596745)
  ·
    refine ⟨24105167434158673069197559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32140223245544897425596745 24105167434158673069197559)
    ·
      refine ⟨36157751151238009603796339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24105167434158673069197559 36157751151238009603796339)
      ·
        refine ⟨54236626726857014405694509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36157751151238009603796339 54236626726857014405694509)
        ·
          refine ⟨20338735022571380402135441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54236626726857014405694509 20338735022571380402135441)
          ·
            refine ⟨15254051266928535301601581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20338735022571380402135441 15254051266928535301601581)
            ·
              refine ⟨5720269225098200738100593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15254051266928535301601581 5720269225098200738100593)
              ·
                refine ⟨4290201918823650553575445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5720269225098200738100593 4290201918823650553575445)
                ·
                  refine ⟨201103214944858619698849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4290201918823650553575445 201103214944858619698849)
                  ·
                    rfl

theorem cell22_1762412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_1762412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1762412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1762412 prefixEnd_1762412 := by exact prefixLift 1762412
  have htrace : WordTrace (prefixWord ++ tailWord_1762412) baseStart_1762412 baseEnd_1762412 := by
    simpa [prefixWord, tailWord_1762412, baseEnd_1762412] using wordTrace_append hprefix tailTrace_1762412
  have hstable : (prefixWord ++ tailWord_1762412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762412).length < 2 ^ (prefixWord ++ tailWord_1762412).sum := by decide
  have hdescent : baseEnd_1762412 < baseStart_1762412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762414 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 3, 4]
def baseStart_1762414 : Nat := 118140960795 + 1762414 * 2 ^ 59
def prefixEnd_1762414 : Nat := 4983230072969 + 3 ^ 40 * 1762414 * 2
def baseEnd_1762414 : Nat := 603310329475448520546541

theorem tailTrace_1762414 : CollatzResearch.WordTrace tailWord_1762414 prefixEnd_1762414 603310329475448520546541 := by
  unfold tailWord_1762414
  simp only [CollatzResearch.WordTrace]
  refine ⟨8035064929635318649095787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42853679624721699461844197 8035064929635318649095787)
  ·
    refine ⟨12052597394452977973643681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8035064929635318649095787 12052597394452977973643681)
    ·
      refine ⟨9039448045839733480232761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12052597394452977973643681 9039448045839733480232761)
      ·
        refine ⟨6779586034379800110174571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9039448045839733480232761 6779586034379800110174571)
        ·
          refine ⟨10169379051569700165261857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6779586034379800110174571 10169379051569700165261857)
          ·
            refine ⟨7627034288677275123946393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10169379051569700165261857 7627034288677275123946393)
            ·
              refine ⟨5720275716507956342959795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7627034288677275123946393 5720275716507956342959795)
              ·
                refine ⟨8580413574761934514439693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5720275716507956342959795 8580413574761934514439693)
                ·
                  refine ⟨3217655090535725442914885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8580413574761934514439693 3217655090535725442914885)
                  ·
                    refine ⟨603310329475448520546541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3217655090535725442914885 603310329475448520546541)
                    ·
                      rfl

theorem cell22_1762414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_1762414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1762414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1762414 prefixEnd_1762414 := by exact prefixLift 1762414
  have htrace : WordTrace (prefixWord ++ tailWord_1762414) baseStart_1762414 baseEnd_1762414 := by
    simpa [prefixWord, tailWord_1762414, baseEnd_1762414] using wordTrace_append hprefix tailTrace_1762414
  have hstable : (prefixWord ++ tailWord_1762414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762414).length < 2 ^ (prefixWord ++ tailWord_1762414).sum := by decide
  have hdescent : baseEnd_1762414 < baseStart_1762414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762446 : List Nat := [4, 1, 1, 3, 2, 1, 2, 4, 4]
def baseStart_1762446 : Nat := 118140960795 + 1762446 * 2 ^ 59
def prefixEnd_1762446 : Nat := 4983230072969 + 3 ^ 40 * 1762446 * 2
def baseEnd_1762446 : Nat := 201107094576470367915481

theorem tailTrace_1762446 : CollatzResearch.WordTrace tailWord_1762446 prefixEnd_1762446 201107094576470367915481 := by
  unfold tailWord_1762446
  simp only [CollatzResearch.WordTrace]
  refine ⟨8035210821620827332241399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42854457715311079105287461 8035210821620827332241399)
  ·
    refine ⟨12052816232431240998362099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8035210821620827332241399 12052816232431240998362099)
    ·
      refine ⟨18079224348646861497543149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12052816232431240998362099 18079224348646861497543149)
      ·
        refine ⟨6779709130742573061578681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18079224348646861497543149 6779709130742573061578681)
        ·
          refine ⟨5084781848056929796184011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6779709130742573061578681 5084781848056929796184011)
          ·
            refine ⟨7627172772085394694276017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5084781848056929796184011 7627172772085394694276017)
            ·
              refine ⟨5720379579064046020707013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7627172772085394694276017 5720379579064046020707013)
              ·
                refine ⟨1072571171074508628882565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5720379579064046020707013 1072571171074508628882565)
                ·
                  refine ⟨201107094576470367915481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1072571171074508628882565 201107094576470367915481)
                  ·
                    rfl

theorem cell22_1762446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_1762446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1762446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1762446 prefixEnd_1762446 := by exact prefixLift 1762446
  have htrace : WordTrace (prefixWord ++ tailWord_1762446) baseStart_1762446 baseEnd_1762446 := by
    simpa [prefixWord, tailWord_1762446, baseEnd_1762446] using wordTrace_append hprefix tailTrace_1762446
  have hstable : (prefixWord ++ tailWord_1762446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762446).length < 2 ^ (prefixWord ++ tailWord_1762446).sum := by decide
  have hdescent : baseEnd_1762446 < baseStart_1762446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762506 : List Nat := [3, 1, 2, 1, 3, 2, 3, 1, 3, 3]
def baseStart_1762506 : Nat := 118140960795 + 1762506 * 2 ^ 59
def prefixEnd_1762506 : Nat := 4983230072969 + 3 ^ 40 * 1762506 * 2
def baseEnd_1762506 : Nat := 603341822955590947246259

theorem tailTrace_1762506 : CollatzResearch.WordTrace tailWord_1762506 prefixEnd_1762506 603341822955590947246259 := by
  unfold tailWord_1762506
  simp only [CollatzResearch.WordTrace]
  refine ⟨16070968738187312226278843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42855916635166165936743581 16070968738187312226278843)
  ·
    refine ⟨24106453107280968339418265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16070968738187312226278843 24106453107280968339418265)
    ·
      refine ⟨18079839830460726254563699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24106453107280968339418265 18079839830460726254563699)
      ·
        refine ⟨27119759745691089381845549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18079839830460726254563699 27119759745691089381845549)
        ·
          refine ⟨10169909904634158518192081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27119759745691089381845549 10169909904634158518192081)
          ·
            refine ⟨7627432428475618888644061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10169909904634158518192081 7627432428475618888644061)
            ·
              refine ⟨2860287160678357083241523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7627432428475618888644061 2860287160678357083241523)
              ·
                refine ⟨4290430741017535624862285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2860287160678357083241523 4290430741017535624862285)
                ·
                  refine ⟨1608911527881575859323357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4290430741017535624862285 1608911527881575859323357)
                  ·
                    refine ⟨603341822955590947246259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1608911527881575859323357 603341822955590947246259)
                    ·
                      rfl

theorem cell22_1762506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_1762506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1762506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1762506 prefixEnd_1762506 := by exact prefixLift 1762506
  have htrace : WordTrace (prefixWord ++ tailWord_1762506) baseStart_1762506 baseEnd_1762506 := by
    simpa [prefixWord, tailWord_1762506, baseEnd_1762506] using wordTrace_append hprefix tailTrace_1762506
  have hstable : (prefixWord ++ tailWord_1762506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762506).length < 2 ^ (prefixWord ++ tailWord_1762506).sum := by decide
  have hdescent : baseEnd_1762506 < baseStart_1762506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762579 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 8, 3]
def baseStart_1762579 : Nat := 118140960795 + 1762579 * 2 ^ 59
def prefixEnd_1762579 : Nat := 4983230072969 + 3 ^ 40 * 1762579 * 2
def baseEnd_1762579 : Nat := 603366812347443090171035

theorem tailTrace_1762579 : CollatzResearch.WordTrace tailWord_1762579 prefixEnd_1762579 603366812347443090171035 := by
  unfold tailWord_1762579
  simp only [CollatzResearch.WordTrace]
  refine ⟨64286537481484782372522791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42857691654323188248348527 64286537481484782372522791)
  ·
    refine ⟨96429806222227173558784187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64286537481484782372522791 96429806222227173558784187)
    ·
      refine ⟨144644709333340760338176281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96429806222227173558784187 144644709333340760338176281)
      ·
        refine ⟨108483532000005570253632211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144644709333340760338176281 108483532000005570253632211)
        ·
          refine ⟨162725298000008355380448317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108483532000005570253632211 162725298000008355380448317)
          ·
            refine ⟨61021986750003133267668119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162725298000008355380448317 61021986750003133267668119)
            ·
              refine ⟨91532980125004699901502179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61021986750003133267668119 91532980125004699901502179)
              ·
                refine ⟨137299470187507049852253269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91532980125004699901502179 137299470187507049852253269)
                ·
                  refine ⟨1608978166259848240456093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 137299470187507049852253269 1608978166259848240456093)
                  ·
                    refine ⟨603366812347443090171035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1608978166259848240456093 603366812347443090171035)
                    ·
                      rfl

theorem cell22_1762579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 3].length) (baseStart_1762579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1762579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1762579 prefixEnd_1762579 := by exact prefixLift 1762579
  have htrace : WordTrace (prefixWord ++ tailWord_1762579) baseStart_1762579 baseEnd_1762579 := by
    simpa [prefixWord, tailWord_1762579, baseEnd_1762579] using wordTrace_append hprefix tailTrace_1762579
  have hstable : (prefixWord ++ tailWord_1762579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762579).length < 2 ^ (prefixWord ++ tailWord_1762579).sum := by decide
  have hdescent : baseEnd_1762579 < baseStart_1762579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762596 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 4, 3]
def baseStart_1762596 : Nat := 118140960795 + 1762596 * 2 ^ 59
def prefixEnd_1762596 : Nat := 4983230072969 + 3 ^ 40 * 1762596 * 2
def baseEnd_1762596 : Nat := 603372631794860712495983

theorem tailTrace_1762596 : CollatzResearch.WordTrace tailWord_1762596 prefixEnd_1762596 603372631794860712495983 := by
  unfold tailWord_1762596
  simp only [CollatzResearch.WordTrace]
  refine ⟨32143578761211597137945821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42858105014948796183927761 32143578761211597137945821)
  ·
    refine ⟨12053842035454348926729683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32143578761211597137945821 12053842035454348926729683)
    ·
      refine ⟨18080763053181523390094525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12053842035454348926729683 18080763053181523390094525)
      ·
        refine ⟨6780286144943071271285447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18080763053181523390094525 6780286144943071271285447)
        ·
          refine ⟨10170429217414606906928171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6780286144943071271285447 10170429217414606906928171)
          ·
            refine ⟨15255643826121910360392257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10170429217414606906928171 15255643826121910360392257)
            ·
              refine ⟨11441732869591432770294193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15255643826121910360392257 11441732869591432770294193)
              ·
                refine ⟨8581299652193574577720645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11441732869591432770294193 8581299652193574577720645)
                ·
                  refine ⟨1608993684786295233322621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8581299652193574577720645 1608993684786295233322621)
                  ·
                    refine ⟨603372631794860712495983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1608993684786295233322621 603372631794860712495983)
                    ·
                      rfl

theorem cell22_1762596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_1762596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1762596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1762596 prefixEnd_1762596 := by exact prefixLift 1762596
  have htrace : WordTrace (prefixWord ++ tailWord_1762596) baseStart_1762596 baseEnd_1762596 := by
    simpa [prefixWord, tailWord_1762596, baseEnd_1762596] using wordTrace_append hprefix tailTrace_1762596
  have hstable : (prefixWord ++ tailWord_1762596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762596).length < 2 ^ (prefixWord ++ tailWord_1762596).sum := by decide
  have hdescent : baseEnd_1762596 < baseStart_1762596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762600 : List Nat := [2, 1, 5, 1, 2, 3, 2, 1, 1, 4]
def baseStart_1762600 : Nat := 118140960795 + 1762600 * 2 ^ 59
def prefixEnd_1762600 : Nat := 4983230072969 + 3 ^ 40 * 1762600 * 2
def baseEnd_1762600 : Nat := 603374001076606035395971

theorem tailTrace_1762600 : CollatzResearch.WordTrace tailWord_1762600 prefixEnd_1762600 603374001076606035395971 := by
  unfold tailWord_1762600
  simp only [CollatzResearch.WordTrace]
  refine ⟨32143651707204351479518627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42858202276272468639358169 32143651707204351479518627)
  ·
    refine ⟨48215477560806527219277941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32143651707204351479518627 48215477560806527219277941)
    ·
      refine ⟨4520201021325611926807307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48215477560806527219277941 4520201021325611926807307)
      ·
        refine ⟨6780301531988417890210961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4520201021325611926807307 6780301531988417890210961)
        ·
          refine ⟨5085226148991313417658221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6780301531988417890210961 5085226148991313417658221)
          ·
            refine ⟨1906959805871742531621833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5085226148991313417658221 1906959805871742531621833)
            ·
              refine ⟨1430219854403806898716375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1906959805871742531621833 1430219854403806898716375)
              ·
                refine ⟨2145329781605710348074563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1430219854403806898716375 2145329781605710348074563)
                ·
                  refine ⟨3217994672408565522111845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2145329781605710348074563 3217994672408565522111845)
                  ·
                    refine ⟨603374001076606035395971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3217994672408565522111845 603374001076606035395971)
                    ·
                      rfl

theorem cell22_1762600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_1762600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1762600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1762600 prefixEnd_1762600 := by exact prefixLift 1762600
  have htrace : WordTrace (prefixWord ++ tailWord_1762600) baseStart_1762600 baseEnd_1762600 := by
    simpa [prefixWord, tailWord_1762600, baseEnd_1762600] using wordTrace_append hprefix tailTrace_1762600
  have hstable : (prefixWord ++ tailWord_1762600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762600).length < 2 ^ (prefixWord ++ tailWord_1762600).sum := by decide
  have hdescent : baseEnd_1762600 < baseStart_1762600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762609 : List Nat := [1, 2, 2, 3, 3, 2, 9]
def baseStart_1762609 : Nat := 118140960795 + 1762609 * 2 ^ 59
def prefixEnd_1762609 : Nat := 4983230072969 + 3 ^ 40 * 1762609 * 2
def baseEnd_1762609 : Nat := 22347299331871593034109

theorem tailTrace_1762609 : CollatzResearch.WordTrace tailWord_1762609 prefixEnd_1762609 22347299331871593034109 := by
  unfold tailWord_1762609
  simp only [CollatzResearch.WordTrace]
  refine ⟨64287631671376097496114881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42858421114250731664076587 64287631671376097496114881)
  ·
    refine ⟨48215723753532073122086161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64287631671376097496114881 48215723753532073122086161)
    ·
      refine ⟨36161792815149054841564621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48215723753532073122086161 36161792815149054841564621)
      ·
        refine ⟨13560672305680895565586733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36161792815149054841564621 13560672305680895565586733)
        ·
          refine ⟨5085252114630335837095025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13560672305680895565586733 5085252114630335837095025)
          ·
            refine ⟨3813939085972751877821269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5085252114630335837095025 3813939085972751877821269)
            ·
              refine ⟨22347299331871593034109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3813939085972751877821269 22347299331871593034109)
              ·
                rfl

theorem cell22_1762609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 9].length) (baseStart_1762609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1762609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1762609 prefixEnd_1762609 := by exact prefixLift 1762609
  have htrace : WordTrace (prefixWord ++ tailWord_1762609) baseStart_1762609 baseEnd_1762609 := by
    simpa [prefixWord, tailWord_1762609, baseEnd_1762609] using wordTrace_append hprefix tailTrace_1762609
  have hstable : (prefixWord ++ tailWord_1762609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762609).length < 2 ^ (prefixWord ++ tailWord_1762609).sum := by decide
  have hdescent : baseEnd_1762609 < baseStart_1762609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762613 : List Nat := [1, 3, 3, 1, 2, 2, 3, 2, 2, 3]
def baseStart_1762613 : Nat := 118140960795 + 1762613 * 2 ^ 59
def prefixEnd_1762613 : Nat := 4983230072969 + 3 ^ 40 * 1762613 * 2
def baseEnd_1762613 : Nat := 603378451242278334820931

theorem tailTrace_1762613 : CollatzResearch.WordTrace tailWord_1762613 prefixEnd_1762613 603378451242278334820931 := by
  unfold tailWord_1762613
  simp only [CollatzResearch.WordTrace]
  refine ⟨64287777563361606179260493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42858518375574404119506995 64287777563361606179260493)
  ·
    refine ⟨24107916586260602317222685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64287777563361606179260493 24107916586260602317222685)
    ·
      refine ⟨9040468719847725868958507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24107916586260602317222685 9040468719847725868958507)
      ·
        refine ⟨13560703079771588803437761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9040468719847725868958507 13560703079771588803437761)
        ·
          refine ⟨10170527309828691602578321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13560703079771588803437761 10170527309828691602578321)
          ·
            refine ⟨7627895482371518701933741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10170527309828691602578321 7627895482371518701933741)
            ·
              refine ⟨2860460805889319513225153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7627895482371518701933741 2860460805889319513225153)
              ·
                refine ⟨2145345604416989634918865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2860460805889319513225153 2145345604416989634918865)
                ·
                  refine ⟨1609009203312742226189149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2145345604416989634918865 1609009203312742226189149)
                  ·
                    refine ⟨603378451242278334820931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1609009203312742226189149 603378451242278334820931)
                    ·
                      rfl

theorem cell22_1762613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_1762613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1762613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1762613 prefixEnd_1762613 := by exact prefixLift 1762613
  have htrace : WordTrace (prefixWord ++ tailWord_1762613) baseStart_1762613 baseEnd_1762613 := by
    simpa [prefixWord, tailWord_1762613, baseEnd_1762613] using wordTrace_append hprefix tailTrace_1762613
  have hstable : (prefixWord ++ tailWord_1762613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762613).length < 2 ^ (prefixWord ++ tailWord_1762613).sum := by decide
  have hdescent : baseEnd_1762613 < baseStart_1762613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762641 : List Nat := [1, 2, 2, 1, 4, 1, 1, 4, 3, 3]
def baseStart_1762641 : Nat := 118140960795 + 1762641 * 2 ^ 59
def prefixEnd_1762641 : Nat := 4983230072969 + 3 ^ 40 * 1762641 * 2
def baseEnd_1762641 : Nat := 603388036214495595120845

theorem tailTrace_1762641 : CollatzResearch.WordTrace tailWord_1762641 prefixEnd_1762641 603388036214495595120845 := by
  unfold tailWord_1762641
  simp only [CollatzResearch.WordTrace]
  refine ⟨64288798807260166961279777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42859199204840111307519851 64288798807260166961279777)
  ·
    refine ⟨48216599105445125220959833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64288798807260166961279777 48216599105445125220959833)
    ·
      refine ⟨36162449329083843915719875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48216599105445125220959833 36162449329083843915719875)
      ·
        refine ⟨54243673993625765873579813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36162449329083843915719875 54243673993625765873579813)
        ·
          refine ⟨10170688873804831101296215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54243673993625765873579813 10170688873804831101296215)
          ·
            refine ⟨15256033310707246651944323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10170688873804831101296215 15256033310707246651944323)
            ·
              refine ⟨22884049966060869977916485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15256033310707246651944323 22884049966060869977916485)
              ·
                refine ⟨4290759368636413120859341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22884049966060869977916485 4290759368636413120859341)
                ·
                  refine ⟨1609034763238654920322253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4290759368636413120859341 1609034763238654920322253)
                  ·
                    refine ⟨603388036214495595120845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1609034763238654920322253 603388036214495595120845)
                    ·
                      rfl

theorem cell22_1762641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 3].length) (baseStart_1762641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1762641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1762641 prefixEnd_1762641 := by exact prefixLift 1762641
  have htrace : WordTrace (prefixWord ++ tailWord_1762641) baseStart_1762641 baseEnd_1762641 := by
    simpa [prefixWord, tailWord_1762641, baseEnd_1762641] using wordTrace_append hprefix tailTrace_1762641
  have hstable : (prefixWord ++ tailWord_1762641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762641).length < 2 ^ (prefixWord ++ tailWord_1762641).sum := by decide
  have hdescent : baseEnd_1762641 < baseStart_1762641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762699 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 8]
def baseStart_1762699 : Nat := 118140960795 + 1762699 * 2 ^ 59
def prefixEnd_1762699 : Nat := 4983230072969 + 3 ^ 40 * 1762699 * 2
def baseEnd_1762699 : Nat := 201135963599934259056889

theorem tailTrace_1762699 : CollatzResearch.WordTrace tailWord_1762699 prefixEnd_1762699 201135963599934259056889 := by
  unfold tailWord_1762699
  simp only [CollatzResearch.WordTrace]
  refine ⟨64290914241050042866891151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42860609494033361911260767 64290914241050042866891151)
  ·
    refine ⟨96436371361575064300336727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64290914241050042866891151 96436371361575064300336727)
    ·
      refine ⟨144654557042362596450505091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96436371361575064300336727 144654557042362596450505091)
      ·
        refine ⟨216981835563543894675757637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144654557042362596450505091 216981835563543894675757637)
        ·
          refine ⟨40684094168164480251704557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216981835563543894675757637 40684094168164480251704557)
          ·
            refine ⟨15256535313061680094389209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40684094168164480251704557 15256535313061680094389209)
            ·
              refine ⟨11442401484796260070791907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15256535313061680094389209 11442401484796260070791907)
              ·
                refine ⟨17163602227194390106187861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11442401484796260070791907 17163602227194390106187861)
                ·
                  refine ⟨201135963599934259056889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17163602227194390106187861 201135963599934259056889)
                  ·
                    rfl

theorem cell22_1762699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 8].length) (baseStart_1762699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1762699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1762699 prefixEnd_1762699 := by exact prefixLift 1762699
  have htrace : WordTrace (prefixWord ++ tailWord_1762699) baseStart_1762699 baseEnd_1762699 := by
    simpa [prefixWord, tailWord_1762699, baseEnd_1762699] using wordTrace_append hprefix tailTrace_1762699
  have hstable : (prefixWord ++ tailWord_1762699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762699).length < 2 ^ (prefixWord ++ tailWord_1762699).sum := by decide
  have hdescent : baseEnd_1762699 < baseStart_1762699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762729 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 5, 6]
def baseStart_1762729 : Nat := 118140960795 + 1762729 * 2 ^ 59
def prefixEnd_1762729 : Nat := 4983230072969 + 3 ^ 40 * 1762729 * 2
def baseEnd_1762729 : Nat := 603418160412892698920575

theorem tailTrace_1762729 : CollatzResearch.WordTrace tailWord_1762729 prefixEnd_1762729 603418160412892698920575 := by
  unfold tailWord_1762729
  simp only [CollatzResearch.WordTrace]
  refine ⟨64292008430941357990483241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42861338953960905326988827 64292008430941357990483241)
  ·
    refine ⟨48219006323206018492862431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64292008430941357990483241 48219006323206018492862431)
    ·
      refine ⟨72328509484809027739293647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48219006323206018492862431 72328509484809027739293647)
      ·
        refine ⟨108492764227213541608940471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72328509484809027739293647 108492764227213541608940471)
        ·
          refine ⟨162739146340820312413410707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108492764227213541608940471 162739146340820312413410707)
          ·
            refine ⟨244108719511230468620116061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162739146340820312413410707 244108719511230468620116061)
            ·
              refine ⟨91540769816711425732543523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244108719511230468620116061 91540769816711425732543523)
              ·
                refine ⟨137311154725067138598815285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91540769816711425732543523 137311154725067138598815285)
                ·
                  refine ⟨12872920755475044243638933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137311154725067138598815285 12872920755475044243638933)
                  ·
                    refine ⟨603418160412892698920575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12872920755475044243638933 603418160412892698920575)
                    ·
                      rfl

theorem cell22_1762729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_1762729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1762729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1762729 prefixEnd_1762729 := by exact prefixLift 1762729
  have htrace : WordTrace (prefixWord ++ tailWord_1762729) baseStart_1762729 baseEnd_1762729 := by
    simpa [prefixWord, tailWord_1762729, baseEnd_1762729] using wordTrace_append hprefix tailTrace_1762729
  have hstable : (prefixWord ++ tailWord_1762729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762729).length < 2 ^ (prefixWord ++ tailWord_1762729).sum := by decide
  have hdescent : baseEnd_1762729 < baseStart_1762729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762887 : List Nat := [1, 1, 4, 1, 5, 1, 3, 1, 1, 4]
def baseStart_1762887 : Nat := 118140960795 + 1762887 * 2 ^ 59
def prefixEnd_1762887 : Nat := 4983230072969 + 3 ^ 40 * 1762887 * 2
def baseEnd_1762887 : Nat := 603472247041832953470091

theorem tailTrace_1762887 : CollatzResearch.WordTrace tailWord_1762887 prefixEnd_1762887 603472247041832953470091 := by
  unfold tailWord_1762887
  simp only [CollatzResearch.WordTrace]
  refine ⟨64297771164368950974734915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42865180776245967316489943 64297771164368950974734915)
  ·
    refine ⟨96446656746553426462102373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64297771164368950974734915 96446656746553426462102373)
    ·
      refine ⟨18083748139978767461644195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96446656746553426462102373 18083748139978767461644195)
      ·
        refine ⟨27125622209968151192466293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18083748139978767461644195 27125622209968151192466293)
        ·
          refine ⟨2543027082184514174293715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27125622209968151192466293 2543027082184514174293715)
          ·
            refine ⟨3814540623276771261440573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2543027082184514174293715 3814540623276771261440573)
            ·
              refine ⟨1430452733728789223040215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3814540623276771261440573 1430452733728789223040215)
              ·
                refine ⟨2145679100593183834560323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1430452733728789223040215 2145679100593183834560323)
                ·
                  refine ⟨3218518650889775751840485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2145679100593183834560323 3218518650889775751840485)
                  ·
                    refine ⟨603472247041832953470091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3218518650889775751840485 603472247041832953470091)
                    ·
                      rfl

theorem cell22_1762887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_1762887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1762887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1762887 prefixEnd_1762887 := by exact prefixLift 1762887
  have htrace : WordTrace (prefixWord ++ tailWord_1762887) baseStart_1762887 baseEnd_1762887 := by
    simpa [prefixWord, tailWord_1762887, baseEnd_1762887] using wordTrace_append hprefix tailTrace_1762887
  have hstable : (prefixWord ++ tailWord_1762887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762887).length < 2 ^ (prefixWord ++ tailWord_1762887).sum := by decide
  have hdescent : baseEnd_1762887 < baseStart_1762887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762911 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 4, 7]
def baseStart_1762911 : Nat := 118140960795 + 1762911 * 2 ^ 59
def prefixEnd_1762911 : Nat := 4983230072969 + 3 ^ 40 * 1762911 * 2
def baseEnd_1762911 : Nat := 603480462732304890870017

theorem tailTrace_1762911 : CollatzResearch.WordTrace tailWord_1762911 prefixEnd_1762911 603480462732304890870017 := by
  unfold tailWord_1762911
  simp only [CollatzResearch.WordTrace]
  refine ⟨64298646516282003073608587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42865764344188002049072391 64298646516282003073608587)
  ·
    refine ⟨96447969774423004610412881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64298646516282003073608587 96447969774423004610412881)
    ·
      refine ⟨72335977330817253457809661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96447969774423004610412881 72335977330817253457809661)
      ·
        refine ⟨27125991499056470046678623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72335977330817253457809661 27125991499056470046678623)
        ·
          refine ⟨40688987248584705070017935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27125991499056470046678623 40688987248584705070017935)
          ·
            refine ⟨61033480872877057605026903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40688987248584705070017935 61033480872877057605026903)
            ·
              refine ⟨91550221309315586407540355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61033480872877057605026903 91550221309315586407540355)
              ·
                refine ⟨137325331963973379611310533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91550221309315586407540355 137325331963973379611310533)
                ·
                  refine ⟨25748499743245008677120725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137325331963973379611310533 25748499743245008677120725)
                  ·
                    refine ⟨603480462732304890870017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25748499743245008677120725 603480462732304890870017)
                    ·
                      rfl

theorem cell22_1762911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_1762911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1762911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1762911 prefixEnd_1762911 := by exact prefixLift 1762911
  have htrace : WordTrace (prefixWord ++ tailWord_1762911) baseStart_1762911 baseEnd_1762911 := by
    simpa [prefixWord, tailWord_1762911, baseEnd_1762911] using wordTrace_append hprefix tailTrace_1762911
  have hstable : (prefixWord ++ tailWord_1762911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762911).length < 2 ^ (prefixWord ++ tailWord_1762911).sum := by decide
  have hdescent : baseEnd_1762911 < baseStart_1762911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762930 : List Nat := [3, 2, 1, 2, 3, 2, 3, 6]
def baseStart_1762930 : Nat := 118140960795 + 1762930 * 2 ^ 59
def prefixEnd_1762930 : Nat := 4983230072969 + 3 ^ 40 * 1762930 * 2
def baseEnd_1762930 : Nat := 67054107424510574960551

theorem tailTrace_1762930 : CollatzResearch.WordTrace tailWord_1762930 prefixEnd_1762930 67054107424510574960551 := by
  unfold tailWord_1762930
  simp only [CollatzResearch.WordTrace]
  refine ⟨16074834875803292329637561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42866226335475446212366829 16074834875803292329637561)
  ·
    refine ⟨12056126156852469247228171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16074834875803292329637561 12056126156852469247228171)
    ·
      refine ⟨18084189235278703870842257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12056126156852469247228171 18084189235278703870842257)
      ·
        refine ⟨13563141926459027903131693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18084189235278703870842257 13563141926459027903131693)
        ·
          refine ⟨5086178222422135463674385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13563141926459027903131693 5086178222422135463674385)
          ·
            refine ⟨3814633666816601597755789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5086178222422135463674385 3814633666816601597755789)
            ·
              refine ⟨1430487625056225599158421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3814633666816601597755789 1430487625056225599158421)
              ·
                refine ⟨67054107424510574960551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1430487625056225599158421 67054107424510574960551)
                ·
                  rfl

theorem cell22_1762930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 6].length) (baseStart_1762930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1762930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1762930 prefixEnd_1762930 := by exact prefixLift 1762930
  have htrace : WordTrace (prefixWord ++ tailWord_1762930) baseStart_1762930 baseEnd_1762930 := by
    simpa [prefixWord, tailWord_1762930, baseEnd_1762930] using wordTrace_append hprefix tailTrace_1762930
  have hstable : (prefixWord ++ tailWord_1762930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762930).length < 2 ^ (prefixWord ++ tailWord_1762930).sum := by decide
  have hdescent : baseEnd_1762930 < baseStart_1762930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763005 : List Nat := [1, 4, 1, 2, 1, 2, 1, 5, 1, 4]
def baseStart_1763005 : Nat := 118140960795 + 1763005 * 2 ^ 59
def prefixEnd_1763005 : Nat := 4983230072969 + 3 ^ 40 * 1763005 * 2
def baseEnd_1763005 : Nat := 603512640853319979019729

theorem tailTrace_1763005 : CollatzResearch.WordTrace tailWord_1763005 prefixEnd_1763005 603512640853319979019729 := by
  unfold tailWord_1763005
  simp only [CollatzResearch.WordTrace]
  refine ⟨64302074977941457127530469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42868049985294304751686979 64302074977941457127530469)
  ·
    refine ⟨12056639058364023211411963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64302074977941457127530469 12056639058364023211411963)
    ·
      refine ⟨18084958587546034817117945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12056639058364023211411963 18084958587546034817117945)
      ·
        refine ⟨13563718940659526112838459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18084958587546034817117945 13563718940659526112838459)
        ·
          refine ⟨20345578410989289169257689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13563718940659526112838459 20345578410989289169257689)
          ·
            refine ⟨15259183808241966876943267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20345578410989289169257689 15259183808241966876943267)
            ·
              refine ⟨22888775712362950315414901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15259183808241966876943267 22888775712362950315414901)
              ·
                refine ⟨2145822723034026592070147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22888775712362950315414901 2145822723034026592070147)
                ·
                  refine ⟨3218734084551039888105221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2145822723034026592070147 3218734084551039888105221)
                  ·
                    refine ⟨603512640853319979019729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3218734084551039888105221 603512640853319979019729)
                    ·
                      rfl

theorem cell22_1763005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_1763005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1763005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1763005 prefixEnd_1763005 := by exact prefixLift 1763005
  have htrace : WordTrace (prefixWord ++ tailWord_1763005) baseStart_1763005 baseEnd_1763005 := by
    simpa [prefixWord, tailWord_1763005, baseEnd_1763005] using wordTrace_append hprefix tailTrace_1763005
  have hstable : (prefixWord ++ tailWord_1763005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763005).length < 2 ^ (prefixWord ++ tailWord_1763005).sum := by decide
  have hdescent : baseEnd_1763005 < baseStart_1763005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763050 : List Nat := [3, 1, 3, 1, 1, 1, 3, 3, 2, 4]
def baseStart_1763050 : Nat := 118140960795 + 1763050 * 2 ^ 59
def prefixEnd_1763050 : Nat := 4983230072969 + 3 ^ 40 * 1763050 * 2
def baseEnd_1763050 : Nat := 603528045272954861644591

theorem tailTrace_1763050 : CollatzResearch.WordTrace tailWord_1763050 prefixEnd_1763050 603528045272954861644591 := by
  unfold tailWord_1763050
  simp only [CollatzResearch.WordTrace]
  refine ⟨16075929065694607453229651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42869144175185619875279069 16075929065694607453229651)
  ·
    refine ⟨24113893598541911179844477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16075929065694607453229651 24113893598541911179844477)
    ·
      refine ⟨9042710099453216692441679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24113893598541911179844477 9042710099453216692441679)
      ·
        refine ⟨13564065149179825038662519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9042710099453216692441679 13564065149179825038662519)
        ·
          refine ⟨20346097723769737557993779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13564065149179825038662519 20346097723769737557993779)
          ·
            refine ⟨30519146585654606336990669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20346097723769737557993779 30519146585654606336990669)
            ·
              refine ⟨11444679969620477376371501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30519146585654606336990669 11444679969620477376371501)
              ·
                refine ⟨4291754988607679016139313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11444679969620477376371501 4291754988607679016139313)
                ·
                  refine ⟨3218816241455759262104485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4291754988607679016139313 3218816241455759262104485)
                  ·
                    refine ⟨603528045272954861644591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3218816241455759262104485 603528045272954861644591)
                    ·
                      rfl

theorem cell22_1763050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_1763050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1763050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1763050 prefixEnd_1763050 := by exact prefixLift 1763050
  have htrace : WordTrace (prefixWord ++ tailWord_1763050) baseStart_1763050 baseEnd_1763050 := by
    simpa [prefixWord, tailWord_1763050, baseEnd_1763050] using wordTrace_append hprefix tailTrace_1763050
  have hstable : (prefixWord ++ tailWord_1763050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763050).length < 2 ^ (prefixWord ++ tailWord_1763050).sum := by decide
  have hdescent : baseEnd_1763050 < baseStart_1763050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763157 : List Nat := [1, 3, 2, 2, 2, 2, 1, 4, 1, 4]
def baseStart_1763157 : Nat := 118140960795 + 1763157 * 2 ^ 59
def prefixEnd_1763157 : Nat := 4983230072969 + 3 ^ 40 * 1763157 * 2
def baseEnd_1763157 : Nat := 603564673559642249219263

theorem tailTrace_1763157 : CollatzResearch.WordTrace tailWord_1763157 prefixEnd_1763157 603564673559642249219263 := by
  unfold tailWord_1763157
  simp only [CollatzResearch.WordTrace]
  refine ⟨64307618873390787087063725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42871745915593858058042483 64307618873390787087063725)
  ·
    refine ⟨24115357077521545157648897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64307618873390787087063725 24115357077521545157648897)
    ·
      refine ⟨18086517808141158868236673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24115357077521545157648897 18086517808141158868236673)
      ·
        refine ⟨13564888356105869151177505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18086517808141158868236673 13564888356105869151177505)
        ·
          refine ⟨10173666267079401863383129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13564888356105869151177505 10173666267079401863383129)
          ·
            refine ⟨7630249700309551397537347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10173666267079401863383129 7630249700309551397537347)
            ·
              refine ⟨11445374550464327096306021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7630249700309551397537347 11445374550464327096306021)
              ·
                refine ⟨2146007728212061330557379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11445374550464327096306021 2146007728212061330557379)
                ·
                  refine ⟨3219011592318091995836069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2146007728212061330557379 3219011592318091995836069)
                  ·
                    refine ⟨603564673559642249219263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3219011592318091995836069 603564673559642249219263)
                    ·
                      rfl

theorem cell22_1763157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_1763157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1763157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1763157 prefixEnd_1763157 := by exact prefixLift 1763157
  have htrace : WordTrace (prefixWord ++ tailWord_1763157) baseStart_1763157 baseEnd_1763157 := by
    simpa [prefixWord, tailWord_1763157, baseEnd_1763157] using wordTrace_append hprefix tailTrace_1763157
  have hstable : (prefixWord ++ tailWord_1763157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763157).length < 2 ^ (prefixWord ++ tailWord_1763157).sum := by decide
  have hdescent : baseEnd_1763157 < baseStart_1763157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763187 : List Nat := [1, 1, 1, 2, 2, 1, 3, 6, 2, 3]
def baseStart_1763187 : Nat := 118140960795 + 1763187 * 2 ^ 59
def prefixEnd_1763187 : Nat := 4983230072969 + 3 ^ 40 * 1763187 * 2
def baseEnd_1763187 : Nat := 603574943172732170969171

theorem tailTrace_1763187 : CollatzResearch.WordTrace tailWord_1763187 prefixEnd_1763187 603574943172732170969171 := by
  unfold tailWord_1763187
  simp only [CollatzResearch.WordTrace]
  refine ⟨64308713063282102210655815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42872475375521401473770543 64308713063282102210655815)
  ·
    refine ⟨96463069594923153315983723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64308713063282102210655815 96463069594923153315983723)
    ·
      refine ⟨144694604392384729973975585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96463069594923153315983723 144694604392384729973975585)
      ·
        refine ⟨108520953294288547480481689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144694604392384729973975585 108520953294288547480481689)
        ·
          refine ⟨81390714970716410610361267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108520953294288547480481689 81390714970716410610361267)
          ·
            refine ⟨122086072456074615915541901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81390714970716410610361267 122086072456074615915541901)
            ·
              refine ⟨45782277171027980968328213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122086072456074615915541901 45782277171027980968328213)
              ·
                refine ⟨2146044242391936607890385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45782277171027980968328213 2146044242391936607890385)
                ·
                  refine ⟨1609533181793952455917789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2146044242391936607890385 1609533181793952455917789)
                  ·
                    refine ⟨603574943172732170969171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1609533181793952455917789 603574943172732170969171)
                    ·
                      rfl

theorem cell22_1763187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 3].length) (baseStart_1763187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1763187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1763187 prefixEnd_1763187 := by exact prefixLift 1763187
  have htrace : WordTrace (prefixWord ++ tailWord_1763187) baseStart_1763187 baseEnd_1763187 := by
    simpa [prefixWord, tailWord_1763187, baseEnd_1763187] using wordTrace_append hprefix tailTrace_1763187
  have hstable : (prefixWord ++ tailWord_1763187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763187).length < 2 ^ (prefixWord ++ tailWord_1763187).sum := by decide
  have hdescent : baseEnd_1763187 < baseStart_1763187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763200 : List Nat := [2, 1, 1, 2, 1, 2, 6, 7]
def baseStart_1763200 : Nat := 118140960795 + 1763200 * 2 ^ 59
def prefixEnd_1763200 : Nat := 4983230072969 + 3 ^ 40 * 1763200 * 2
def baseEnd_1763200 : Nat := 67064377037600496710459

theorem tailTrace_1763200 : CollatzResearch.WordTrace tailWord_1763200 prefixEnd_1763200 67064377037600496710459 := by
  unfold tailWord_1763200
  simp only [CollatzResearch.WordTrace]
  refine ⟨32154593606117502715439527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42872791474823336953919369 32154593606117502715439527)
  ·
    refine ⟨48231890409176254073159291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32154593606117502715439527 48231890409176254073159291)
    ·
      refine ⟨72347835613764381109738937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48231890409176254073159291 72347835613764381109738937)
      ·
        refine ⟨54260876710323285832304203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72347835613764381109738937 54260876710323285832304203)
        ·
          refine ⟨81391315065484928748456305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54260876710323285832304203 81391315065484928748456305)
          ·
            refine ⟨61043486299113696561342229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81391315065484928748456305 61043486299113696561342229)
            ·
              refine ⟨2861413420270954526312917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61043486299113696561342229 2861413420270954526312917)
              ·
                refine ⟨67064377037600496710459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2861413420270954526312917 67064377037600496710459)
                ·
                  rfl

theorem cell22_1763200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 7].length) (baseStart_1763200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1763200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1763200 prefixEnd_1763200 := by exact prefixLift 1763200
  have htrace : WordTrace (prefixWord ++ tailWord_1763200) baseStart_1763200 baseEnd_1763200 := by
    simpa [prefixWord, tailWord_1763200, baseEnd_1763200] using wordTrace_append hprefix tailTrace_1763200
  have hstable : (prefixWord ++ tailWord_1763200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763200).length < 2 ^ (prefixWord ++ tailWord_1763200).sum := by decide
  have hdescent : baseEnd_1763200 < baseStart_1763200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763240 : List Nat := [2, 1, 6, 2, 1, 2, 2, 2, 4]
def baseStart_1763240 : Nat := 118140960795 + 1763240 * 2 ^ 59
def prefixEnd_1763240 : Nat := 4983230072969 + 3 ^ 40 * 1763240 * 2
def baseEnd_1763240 : Nat := 201197695385285899798003

theorem tailTrace_1763240 : CollatzResearch.WordTrace tailWord_1763240 prefixEnd_1763240 201197695385285899798003 := by
  unfold tailWord_1763240
  simp only [CollatzResearch.WordTrace]
  refine ⟨32155323066045046131167587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42873764088060061508223449 32155323066045046131167587)
  ·
    refine ⟨48232984599067569196751381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32155323066045046131167587 48232984599067569196751381)
    ·
      refine ⟨2260921153081292306097721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48232984599067569196751381 2260921153081292306097721)
      ·
        refine ⟨1695690864810969229573291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2260921153081292306097721 1695690864810969229573291)
        ·
          refine ⟨2543536297216453844359937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1695690864810969229573291 2543536297216453844359937)
          ·
            refine ⟨1907652222912340383269953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2543536297216453844359937 1907652222912340383269953)
            ·
              refine ⟨1430739167184255287452465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1907652222912340383269953 1430739167184255287452465)
              ·
                refine ⟨1073054375388191465589349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1430739167184255287452465 1073054375388191465589349)
                ·
                  refine ⟨201197695385285899798003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1073054375388191465589349 201197695385285899798003)
                  ·
                    rfl

theorem cell22_1763240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 4].length) (baseStart_1763240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1763240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1763240 prefixEnd_1763240 := by exact prefixLift 1763240
  have htrace : WordTrace (prefixWord ++ tailWord_1763240) baseStart_1763240 baseEnd_1763240 := by
    simpa [prefixWord, tailWord_1763240, baseEnd_1763240] using wordTrace_append hprefix tailTrace_1763240
  have hstable : (prefixWord ++ tailWord_1763240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763240).length < 2 ^ (prefixWord ++ tailWord_1763240).sum := by decide
  have hdescent : baseEnd_1763240 < baseStart_1763240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763305 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 1, 11]
def baseStart_1763305 : Nat := 118140960795 + 1763305 * 2 ^ 59
def prefixEnd_1763305 : Nat := 4983230072969 + 3 ^ 40 * 1763305 * 2
def baseEnd_1763305 : Nat := 603615336984219196518809

theorem tailTrace_1763305 : CollatzResearch.WordTrace tailWord_1763305 prefixEnd_1763305 603615336984219196518809 := by
  unfold tailWord_1763305
  simp only [CollatzResearch.WordTrace]
  refine ⟨64313016876854608363451369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42875344584569738908967579 64313016876854608363451369)
  ·
    refine ⟨48234762657640956272588527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64313016876854608363451369 48234762657640956272588527)
    ·
      refine ⟨72352143986461434408882791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48234762657640956272588527 72352143986461434408882791)
      ·
        refine ⟨108528215979692151613324187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72352143986461434408882791 108528215979692151613324187)
        ·
          refine ⟨162792323969538227419986281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108528215979692151613324187 162792323969538227419986281)
          ·
            refine ⟨122094242977153670564989711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162792323969538227419986281 122094242977153670564989711)
            ·
              refine ⟨183141364465730505847484567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122094242977153670564989711 183141364465730505847484567)
              ·
                refine ⟨274712046698595758771226851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183141364465730505847484567 274712046698595758771226851)
                ·
                  refine ⟨412068070047893638156840277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274712046698595758771226851 412068070047893638156840277)
                  ·
                    refine ⟨603615336984219196518809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 412068070047893638156840277 603615336984219196518809)
                    ·
                      rfl

theorem cell22_1763305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_1763305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1763305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1763305 prefixEnd_1763305 := by exact prefixLift 1763305
  have htrace : WordTrace (prefixWord ++ tailWord_1763305) baseStart_1763305 baseEnd_1763305 := by
    simpa [prefixWord, tailWord_1763305, baseEnd_1763305] using wordTrace_append hprefix tailTrace_1763305
  have hstable : (prefixWord ++ tailWord_1763305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763305).length < 2 ^ (prefixWord ++ tailWord_1763305).sum := by decide
  have hdescent : baseEnd_1763305 < baseStart_1763305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763326 : List Nat := [4, 2, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_1763326 : Nat := 118140960795 + 1763326 * 2 ^ 59
def prefixEnd_1763326 : Nat := 4983230072969 + 3 ^ 40 * 1763326 * 2
def baseEnd_1763326 : Nat := 603622525713382141743745

theorem tailTrace_1763326 : CollatzResearch.WordTrace tailWord_1763326 prefixEnd_1763326 603622525713382141743745 := by
  unfold tailWord_1763326
  simp only [CollatzResearch.WordTrace]
  refine ⟨8039222851222316118745729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42875855206519019299977221 8039222851222316118745729)
  ·
    refine ⟨6029417138416737089059297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8039222851222316118745729 6029417138416737089059297)
    ·
      refine ⟨4522062853812552816794473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6029417138416737089059297 4522062853812552816794473)
      ·
        refine ⟨3391547140359414612595855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4522062853812552816794473 3391547140359414612595855)
        ·
          refine ⟨5087320710539121918893783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3391547140359414612595855 5087320710539121918893783)
          ·
            refine ⟨7630981065808682878340675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5087320710539121918893783 7630981065808682878340675)
            ·
              refine ⟨11446471598713024317511013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7630981065808682878340675 11446471598713024317511013)
              ·
                refine ⟨2146213424758692059533315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11446471598713024317511013 2146213424758692059533315)
                ·
                  refine ⟨3219320137138038089299973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2146213424758692059533315 3219320137138038089299973)
                  ·
                    refine ⟨603622525713382141743745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3219320137138038089299973 603622525713382141743745)
                    ·
                      rfl

theorem cell22_1763326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_1763326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1763326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1763326 prefixEnd_1763326 := by exact prefixLift 1763326
  have htrace : WordTrace (prefixWord ++ tailWord_1763326) baseStart_1763326 baseEnd_1763326 := by
    simpa [prefixWord, tailWord_1763326, baseEnd_1763326] using wordTrace_append hprefix tailTrace_1763326
  have hstable : (prefixWord ++ tailWord_1763326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763326).length < 2 ^ (prefixWord ++ tailWord_1763326).sum := by decide
  have hdescent : baseEnd_1763326 < baseStart_1763326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763354 : List Nat := [3, 1, 1, 3, 1, 4, 1, 2, 2, 4]
def baseStart_1763354 : Nat := 118140960795 + 1763354 * 2 ^ 59
def prefixEnd_1763354 : Nat := 4983230072969 + 3 ^ 40 * 1763354 * 2
def baseEnd_1763354 : Nat := 603632110685599402043659

theorem tailTrace_1763354 : CollatzResearch.WordTrace tailWord_1763354 prefixEnd_1763354 603632110685599402043659 := by
  unfold tailWord_1763354
  simp only [CollatzResearch.WordTrace]
  refine ⟨16078701013419272432996279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42876536035784726487990077 16078701013419272432996279)
  ·
    refine ⟨24118051520128908649494419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16078701013419272432996279 24118051520128908649494419)
    ·
      refine ⟨36177077280193362974241629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24118051520128908649494419 36177077280193362974241629)
      ·
        refine ⟨13566403980072511115340611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36177077280193362974241629 13566403980072511115340611)
        ·
          refine ⟨20349605970108766673010917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13566403980072511115340611 20349605970108766673010917)
          ·
            refine ⟨3815551119395393751189547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20349605970108766673010917 3815551119395393751189547)
            ·
              refine ⟨5723326679093090626784321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3815551119395393751189547 5723326679093090626784321)
              ·
                refine ⟨4292495009319817970088241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5723326679093090626784321 4292495009319817970088241)
                ·
                  refine ⟨3219371256989863477566181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4292495009319817970088241 3219371256989863477566181)
                  ·
                    refine ⟨603632110685599402043659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3219371256989863477566181 603632110685599402043659)
                    ·
                      rfl

theorem cell22_1763354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_1763354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1763354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1763354 prefixEnd_1763354 := by exact prefixLift 1763354
  have htrace : WordTrace (prefixWord ++ tailWord_1763354) baseStart_1763354 baseEnd_1763354 := by
    simpa [prefixWord, tailWord_1763354, baseEnd_1763354] using wordTrace_append hprefix tailTrace_1763354
  have hstable : (prefixWord ++ tailWord_1763354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763354).length < 2 ^ (prefixWord ++ tailWord_1763354).sum := by decide
  have hdescent : baseEnd_1763354 < baseStart_1763354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763401 : List Nat := [1, 2, 1, 1, 2, 2, 4, 5, 1, 3]
def baseStart_1763401 : Nat := 118140960795 + 1763401 * 2 ^ 59
def prefixEnd_1763401 : Nat := 4983230072969 + 3 ^ 40 * 1763401 * 2
def baseEnd_1763401 : Nat := 603648199746106946118515

theorem tailTrace_1763401 : CollatzResearch.WordTrace tailWord_1763401 prefixEnd_1763401 603648199746106946118515 := by
  unfold tailWord_1763401
  simp only [CollatzResearch.WordTrace]
  refine ⟨64316518284506816758946057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42877678856337877839297371 64316518284506816758946057)
  ·
    refine ⟨48237388713380112569209543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64316518284506816758946057 48237388713380112569209543)
    ·
      refine ⟨72356083070070168853814315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48237388713380112569209543 72356083070070168853814315)
      ·
        refine ⟨108534124605105253280721473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72356083070070168853814315 108534124605105253280721473)
        ·
          refine ⟨81400593453828939960541105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108534124605105253280721473 81400593453828939960541105)
          ·
            refine ⟨61050445090371704970405829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81400593453828939960541105 61050445090371704970405829)
            ·
              refine ⟨11446958454444694681951093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61050445090371704970405829 11446958454444694681951093)
              ·
                refine ⟨1073152355104190126432915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11446958454444694681951093 1073152355104190126432915)
                ·
                  refine ⟨1609728532656285189649373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1073152355104190126432915 1609728532656285189649373)
                  ·
                    refine ⟨603648199746106946118515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1609728532656285189649373 603648199746106946118515)
                    ·
                      rfl

theorem cell22_1763401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 1, 3].length) (baseStart_1763401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1763401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1763401 prefixEnd_1763401 := by exact prefixLift 1763401
  have htrace : WordTrace (prefixWord ++ tailWord_1763401) baseStart_1763401 baseEnd_1763401 := by
    simpa [prefixWord, tailWord_1763401, baseEnd_1763401] using wordTrace_append hprefix tailTrace_1763401
  have hstable : (prefixWord ++ tailWord_1763401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763401).length < 2 ^ (prefixWord ++ tailWord_1763401).sum := by decide
  have hdescent : baseEnd_1763401 < baseStart_1763401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763429 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 2, 5]
def baseStart_1763429 : Nat := 118140960795 + 1763429 * 2 ^ 59
def prefixEnd_1763429 : Nat := 4983230072969 + 3 ^ 40 * 1763429 * 2
def baseEnd_1763429 : Nat := 603657784718324206418429

theorem tailTrace_1763429 : CollatzResearch.WordTrace tailWord_1763429 prefixEnd_1763429 603657784718324206418429 := by
  unfold tailWord_1763429
  simp only [CollatzResearch.WordTrace]
  refine ⟨64317539528405377540965341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42878359685603585027310227 64317539528405377540965341)
  ·
    refine ⟨24119077323152016577862003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64317539528405377540965341 24119077323152016577862003)
    ·
      refine ⟨36178615984728024866793005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24119077323152016577862003 36178615984728024866793005)
      ·
        refine ⟨13566980994273009325047377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36178615984728024866793005 13566980994273009325047377)
        ·
          refine ⟨10175235745704756993785533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13566980994273009325047377 10175235745704756993785533)
          ·
            refine ⟨3815713404639283872669575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10175235745704756993785533 3815713404639283872669575)
            ·
              refine ⟨5723570106958925809004363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3815713404639283872669575 5723570106958925809004363)
              ·
                refine ⟨8585355160438388713506545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5723570106958925809004363 8585355160438388713506545)
                ·
                  refine ⟨6439016370328791535129909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8585355160438388713506545 6439016370328791535129909)
                  ·
                    refine ⟨603657784718324206418429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6439016370328791535129909 603657784718324206418429)
                    ·
                      rfl

theorem cell22_1763429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_1763429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1763429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1763429 prefixEnd_1763429 := by exact prefixLift 1763429
  have htrace : WordTrace (prefixWord ++ tailWord_1763429) baseStart_1763429 baseEnd_1763429 := by
    simpa [prefixWord, tailWord_1763429, baseEnd_1763429] using wordTrace_append hprefix tailTrace_1763429
  have hstable : (prefixWord ++ tailWord_1763429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763429).length < 2 ^ (prefixWord ++ tailWord_1763429).sum := by decide
  have hdescent : baseEnd_1763429 < baseStart_1763429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763461 : List Nat := [1, 3, 1, 1, 5, 2, 1, 3, 1, 4]
def baseStart_1763461 : Nat := 118140960795 + 1763461 * 2 ^ 59
def prefixEnd_1763461 : Nat := 4983230072969 + 3 ^ 40 * 1763461 * 2
def baseEnd_1763461 : Nat := 603668738972286789618331

theorem tailTrace_1763461 : CollatzResearch.WordTrace tailWord_1763461 prefixEnd_1763461 603668738972286789618331 := by
  unfold tailWord_1763461
  simp only [CollatzResearch.WordTrace]
  refine ⟨64318706664289447006130237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42879137776192964670753491 64318706664289447006130237)
  ·
    refine ⟨24119514999108542627298839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64318706664289447006130237 24119514999108542627298839)
    ·
      refine ⟨36179272498662813940948259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24119514999108542627298839 36179272498662813940948259)
      ·
        refine ⟨54268908747994220911422389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36179272498662813940948259 54268908747994220911422389)
        ·
          refine ⟨5087710195124458210445849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54268908747994220911422389 5087710195124458210445849)
          ·
            refine ⟨3815782646343343657834387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5087710195124458210445849 3815782646343343657834387)
            ·
              refine ⟨5723673969515015486751581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3815782646343343657834387 5723673969515015486751581)
              ·
                refine ⟨2146377738568130807531843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5723673969515015486751581 2146377738568130807531843)
                ·
                  refine ⟨3219566607852196211297765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2146377738568130807531843 3219566607852196211297765)
                  ·
                    refine ⟨603668738972286789618331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3219566607852196211297765 603668738972286789618331)
                    ·
                      rfl

theorem cell22_1763461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_1763461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1763461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1763461 prefixEnd_1763461 := by exact prefixLift 1763461
  have htrace : WordTrace (prefixWord ++ tailWord_1763461) baseStart_1763461 baseEnd_1763461 := by
    simpa [prefixWord, tailWord_1763461, baseEnd_1763461] using wordTrace_append hprefix tailTrace_1763461
  have hstable : (prefixWord ++ tailWord_1763461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763461).length < 2 ^ (prefixWord ++ tailWord_1763461).sum := by decide
  have hdescent : baseEnd_1763461 < baseStart_1763461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763489 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 1, 6]
def baseStart_1763489 : Nat := 118140960795 + 1763489 * 2 ^ 59
def prefixEnd_1763489 : Nat := 4983230072969 + 3 ^ 40 * 1763489 * 2
def baseEnd_1763489 : Nat := 603678323944504049918245

theorem tailTrace_1763489 : CollatzResearch.WordTrace tailWord_1763489 prefixEnd_1763489 603678323944504049918245 := by
  unfold tailWord_1763489
  simp only [CollatzResearch.WordTrace]
  refine ⟨64319727908188007788149521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42879818605458671858766347 64319727908188007788149521)
  ·
    refine ⟨48239795931141005841112141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64319727908188007788149521 48239795931141005841112141)
    ·
      refine ⟨18089923474177877190417053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48239795931141005841112141 18089923474177877190417053)
      ·
        refine ⟨6783721302816703946406395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18089923474177877190417053 6783721302816703946406395)
        ·
          refine ⟨10175581954225055919609593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6783721302816703946406395 10175581954225055919609593)
          ·
            refine ⟨7631686465668791939707195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10175581954225055919609593 7631686465668791939707195)
            ·
              refine ⟨11447529698503187909560793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7631686465668791939707195 11447529698503187909560793)
              ·
                refine ⟨8585647273877390932170595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11447529698503187909560793 8585647273877390932170595)
                ·
                  refine ⟨12878470910816086398255893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8585647273877390932170595 12878470910816086398255893)
                  ·
                    refine ⟨603678323944504049918245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12878470910816086398255893 603678323944504049918245)
                    ·
                      rfl

theorem cell22_1763489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_1763489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1763489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1763489 prefixEnd_1763489 := by exact prefixLift 1763489
  have htrace : WordTrace (prefixWord ++ tailWord_1763489) baseStart_1763489 baseEnd_1763489 := by
    simpa [prefixWord, tailWord_1763489, baseEnd_1763489] using wordTrace_append hprefix tailTrace_1763489
  have hstable : (prefixWord ++ tailWord_1763489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763489).length < 2 ^ (prefixWord ++ tailWord_1763489).sum := by decide
  have hdescent : baseEnd_1763489 < baseStart_1763489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763542 : List Nat := [5, 2, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_1763542 : Nat := 118140960795 + 1763542 * 2 ^ 59
def prefixEnd_1763542 : Nat := 4983230072969 + 3 ^ 40 * 1763542 * 2
def baseEnd_1763542 : Nat := 603696466927629578343083

theorem tailTrace_1763542 : CollatzResearch.WordTrace tailWord_1763542 prefixEnd_1763542 603696466927629578343083 := by
  unfold tailWord_1763542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4020103811062249864989305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42881107317997331893219253 4020103811062249864989305)
  ·
    refine ⟨3015077858296687398741979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4020103811062249864989305 3015077858296687398741979)
    ·
      refine ⟨4522616787445031098112969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3015077858296687398741979 4522616787445031098112969)
      ·
        refine ⟨3391962590583773323584727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4522616787445031098112969 3391962590583773323584727)
        ·
          refine ⟨5087943885875659985377091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3391962590583773323584727 5087943885875659985377091)
          ·
            refine ⟨7631915828813489978065637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5087943885875659985377091 7631915828813489978065637)
            ·
              refine ⟨1430984217902529370887307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7631915828813489978065637 1430984217902529370887307)
              ·
                refine ⟨2146476326853794056330961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1430984217902529370887307 2146476326853794056330961)
                ·
                  refine ⟨1609857245140345542248221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2146476326853794056330961 1609857245140345542248221)
                  ·
                    refine ⟨603696466927629578343083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1609857245140345542248221 603696466927629578343083)
                    ·
                      rfl

theorem cell22_1763542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_1763542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1763542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1763542 prefixEnd_1763542 := by exact prefixLift 1763542
  have htrace : WordTrace (prefixWord ++ tailWord_1763542) baseStart_1763542 baseEnd_1763542 := by
    simpa [prefixWord, tailWord_1763542, baseEnd_1763542] using wordTrace_append hprefix tailTrace_1763542
  have hstable : (prefixWord ++ tailWord_1763542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763542).length < 2 ^ (prefixWord ++ tailWord_1763542).sum := by decide
  have hdescent : baseEnd_1763542 < baseStart_1763542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763660 : List Nat := [2, 2, 1, 3, 2, 1, 5, 1, 2, 3]
def baseStart_1763660 : Nat := 118140960795 + 1763660 * 2 ^ 59
def prefixEnd_1763660 : Nat := 4983230072969 + 3 ^ 40 * 1763660 * 2
def baseEnd_1763660 : Nat := 603736860739116603892721

theorem tailTrace_1763660 : CollatzResearch.WordTrace tailWord_1763660 prefixEnd_1763660 603736860739116603892721 := by
  unfold tailWord_1763660
  simp only [CollatzResearch.WordTrace]
  refine ⟨32162982395284251996312217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42883976527045669328416289 32162982395284251996312217)
  ·
    refine ⟨24122236796463188997234163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32162982395284251996312217 24122236796463188997234163)
    ·
      refine ⟨36183355194694783495851245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24122236796463188997234163 36183355194694783495851245)
      ·
        refine ⟨13568758198010543810944217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36183355194694783495851245 13568758198010543810944217)
        ·
          refine ⟨10176568648507907858208163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13568758198010543810944217 10176568648507907858208163)
          ·
            refine ⟨15264852972761861787312245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10176568648507907858208163 15264852972761861787312245)
            ·
              refine ⟨1431079966196424542560523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15264852972761861787312245 1431079966196424542560523)
              ·
                refine ⟨2146619949294636813840785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1431079966196424542560523 2146619949294636813840785)
                ·
                  refine ⟨1609964961970977610380589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2146619949294636813840785 1609964961970977610380589)
                  ·
                    refine ⟨603736860739116603892721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1609964961970977610380589 603736860739116603892721)
                    ·
                      rfl

theorem cell22_1763660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 2, 3].length) (baseStart_1763660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1763660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1763660 prefixEnd_1763660 := by exact prefixLift 1763660
  have htrace : WordTrace (prefixWord ++ tailWord_1763660) baseStart_1763660 baseEnd_1763660 := by
    simpa [prefixWord, tailWord_1763660, baseEnd_1763660] using wordTrace_append hprefix tailTrace_1763660
  have hstable : (prefixWord ++ tailWord_1763660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763660).length < 2 ^ (prefixWord ++ tailWord_1763660).sum := by decide
  have hdescent : baseEnd_1763660 < baseStart_1763660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763716 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 1, 7]
def baseStart_1763716 : Nat := 118140960795 + 1763716 * 2 ^ 59
def prefixEnd_1763716 : Nat := 4983230072969 + 3 ^ 40 * 1763716 * 2
def baseEnd_1763716 : Nat := 603756030683551124492549

theorem tailTrace_1763716 : CollatzResearch.WordTrace tailWord_1763716 prefixEnd_1763716 603756030683551124492549 := by
  unfold tailWord_1763716
  simp only [CollatzResearch.WordTrace]
  refine ⟨32164003639182812778331501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42885338185577083704442001 32164003639182812778331501)
  ·
    refine ⟨12061501364693554791874313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32164003639182812778331501 12061501364693554791874313)
    ·
      refine ⟨9046126023520166093905735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12061501364693554791874313 9046126023520166093905735)
      ·
        refine ⟨13569189035280249140858603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9046126023520166093905735 13569189035280249140858603)
        ·
          refine ⟨20353783552920373711287905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13569189035280249140858603 20353783552920373711287905)
          ·
            refine ⟨15265337664690280283465929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20353783552920373711287905 15265337664690280283465929)
            ·
              refine ⟨11449003248517710212599447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15265337664690280283465929 11449003248517710212599447)
              ·
                refine ⟨17173504872776565318899171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11449003248517710212599447 17173504872776565318899171)
                ·
                  refine ⟨25760257309164847978348757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17173504872776565318899171 25760257309164847978348757)
                  ·
                    refine ⟨603756030683551124492549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25760257309164847978348757 603756030683551124492549)
                    ·
                      rfl

theorem cell22_1763716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1763716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1763716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1763716 prefixEnd_1763716 := by exact prefixLift 1763716
  have htrace : WordTrace (prefixWord ++ tailWord_1763716) baseStart_1763716 baseEnd_1763716 := by
    simpa [prefixWord, tailWord_1763716, baseEnd_1763716] using wordTrace_append hprefix tailTrace_1763716
  have hstable : (prefixWord ++ tailWord_1763716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763716).length < 2 ^ (prefixWord ++ tailWord_1763716).sum := by decide
  have hdescent : baseEnd_1763716 < baseStart_1763716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763748 : List Nat := [2, 3, 1, 2, 1, 1, 2, 5, 1, 4]
def baseStart_1763748 : Nat := 118140960795 + 1763748 * 2 ^ 59
def prefixEnd_1763748 : Nat := 4983230072969 + 3 ^ 40 * 1763748 * 2
def baseEnd_1763748 : Nat := 603766984937513707692451

theorem tailTrace_1763748 : CollatzResearch.WordTrace tailWord_1763748 prefixEnd_1763748 603766984937513707692451 := by
  unfold tailWord_1763748
  simp only [CollatzResearch.WordTrace]
  refine ⟨32164587207124847510913949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42886116276166463347885265 32164587207124847510913949)
  ·
    refine ⟨12061720202671817816592731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32164587207124847510913949 12061720202671817816592731)
    ·
      refine ⟨18092580304007726724889097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12061720202671817816592731 18092580304007726724889097)
      ·
        refine ⟨13569435228005795043666823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18092580304007726724889097 13569435228005795043666823)
        ·
          refine ⟨20354152842008692565500235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13569435228005795043666823 20354152842008692565500235)
          ·
            refine ⟨30531229263013038848250353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20354152842008692565500235 30531229263013038848250353)
            ·
              refine ⟨22898421947259779136187765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30531229263013038848250353 22898421947259779136187765)
              ·
                refine ⟨2146727057555604294017603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22898421947259779136187765 2146727057555604294017603)
                ·
                  refine ⟨3220090586333406441026405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2146727057555604294017603 3220090586333406441026405)
                  ·
                    refine ⟨603766984937513707692451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3220090586333406441026405 603766984937513707692451)
                    ·
                      rfl

theorem cell22_1763748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_1763748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1763748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1763748 prefixEnd_1763748 := by exact prefixLift 1763748
  have htrace : WordTrace (prefixWord ++ tailWord_1763748) baseStart_1763748 baseEnd_1763748 := by
    simpa [prefixWord, tailWord_1763748, baseEnd_1763748] using wordTrace_append hprefix tailTrace_1763748
  have hstable : (prefixWord ++ tailWord_1763748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763748).length < 2 ^ (prefixWord ++ tailWord_1763748).sum := by decide
  have hdescent : baseEnd_1763748 < baseStart_1763748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763776 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 1, 6]
def baseStart_1763776 : Nat := 118140960795 + 1763776 * 2 ^ 59
def prefixEnd_1763776 : Nat := 4983230072969 + 3 ^ 40 * 1763776 * 2
def baseEnd_1763776 : Nat := 603776569909730967992365

theorem tailTrace_1763776 : CollatzResearch.WordTrace tailWord_1763776 prefixEnd_1763776 603776569909730967992365 := by
  unfold tailWord_1763776
  simp only [CollatzResearch.WordTrace]
  refine ⟨32165097829074127901923591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42886797105432170535898121 32165097829074127901923591)
  ·
    refine ⟨48247646743611191852885387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32165097829074127901923591 48247646743611191852885387)
    ·
      refine ⟨72371470115416787779328081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48247646743611191852885387 72371470115416787779328081)
      ·
        refine ⟨54278602586562590834496061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72371470115416787779328081 54278602586562590834496061)
        ·
          refine ⟨20354475969960971562936023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54278602586562590834496061 20354475969960971562936023)
          ·
            refine ⟨30531713954941457344404035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20354475969960971562936023 30531713954941457344404035)
            ·
              refine ⟨45797570932412186016606053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30531713954941457344404035 45797570932412186016606053)
              ·
                refine ⟨8587044549827284878113635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45797570932412186016606053 8587044549827284878113635)
                ·
                  refine ⟨12880566824740927317170453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8587044549827284878113635 12880566824740927317170453)
                  ·
                    refine ⟨603776569909730967992365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12880566824740927317170453 603776569909730967992365)
                    ·
                      rfl

theorem cell22_1763776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_1763776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1763776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1763776 prefixEnd_1763776 := by exact prefixLift 1763776
  have htrace : WordTrace (prefixWord ++ tailWord_1763776) baseStart_1763776 baseEnd_1763776 := by
    simpa [prefixWord, tailWord_1763776, baseEnd_1763776] using wordTrace_append hprefix tailTrace_1763776
  have hstable : (prefixWord ++ tailWord_1763776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763776).length < 2 ^ (prefixWord ++ tailWord_1763776).sum := by decide
  have hdescent : baseEnd_1763776 < baseStart_1763776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763780 : List Nat := [2, 3, 3, 2, 2, 1, 1, 2, 6]
def baseStart_1763780 : Nat := 118140960795 + 1763780 * 2 ^ 59
def prefixEnd_1763780 : Nat := 4983230072969 + 3 ^ 40 * 1763780 * 2
def baseEnd_1763780 : Nat := 201259313063825430297451

theorem tailTrace_1763780 : CollatzResearch.WordTrace tailWord_1763780 prefixEnd_1763780 201259313063825430297451 := by
  unfold tailWord_1763780
  simp only [CollatzResearch.WordTrace]
  refine ⟨32165170775066882243496397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42886894366755842991328529 32165170775066882243496397)
  ·
    refine ⟨12061939040650080841311149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32165170775066882243496397 12061939040650080841311149)
    ·
      refine ⟨4523227140243780315491681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12061939040650080841311149 4523227140243780315491681)
      ·
        refine ⟨3392420355182835236618761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4523227140243780315491681 3392420355182835236618761)
        ·
          refine ⟨2544315266387126427464071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3392420355182835236618761 2544315266387126427464071)
          ·
            refine ⟨3816472899580689641196107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2544315266387126427464071 3816472899580689641196107)
            ·
              refine ⟨5724709349371034461794161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3816472899580689641196107 5724709349371034461794161)
              ·
                refine ⟨4293532012028275846345621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5724709349371034461794161 4293532012028275846345621)
                ·
                  refine ⟨201259313063825430297451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4293532012028275846345621 201259313063825430297451)
                  ·
                    rfl

theorem cell22_1763780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_1763780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1763780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1763780 prefixEnd_1763780 := by exact prefixLift 1763780
  have htrace : WordTrace (prefixWord ++ tailWord_1763780) baseStart_1763780 baseEnd_1763780 := by
    simpa [prefixWord, tailWord_1763780, baseEnd_1763780] using wordTrace_append hprefix tailTrace_1763780
  have hstable : (prefixWord ++ tailWord_1763780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763780).length < 2 ^ (prefixWord ++ tailWord_1763780).sum := by decide
  have hdescent : baseEnd_1763780 < baseStart_1763780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763829 : List Nat := [1, 3, 5, 1, 3, 1, 1, 1, 1, 5]
def baseStart_1763829 : Nat := 118140960795 + 1763829 * 2 ^ 59
def prefixEnd_1763829 : Nat := 4983230072969 + 3 ^ 40 * 1763829 * 2
def baseEnd_1763829 : Nat := 603794712892856496417203

theorem tailTrace_1763829 : CollatzResearch.WordTrace tailWord_1763829 prefixEnd_1763829 603794712892856496417203 := by
  unfold tailWord_1763829
  simp only [CollatzResearch.WordTrace]
  refine ⟨64332128726956245855526541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42888085817970830570351027 64332128726956245855526541)
  ·
    refine ⟨24124548272608592195822453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64332128726956245855526541 24124548272608592195822453)
    ·
      refine ⟨2261676400557055518358355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24124548272608592195822453 2261676400557055518358355)
      ·
        refine ⟨3392514600835583277537533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2261676400557055518358355 3392514600835583277537533)
        ·
          refine ⟨1272192975313343729076575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3392514600835583277537533 1272192975313343729076575)
          ·
            refine ⟨1908289462970015593614863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1272192975313343729076575 1908289462970015593614863)
            ·
              refine ⟨2862434194455023390422295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1908289462970015593614863 2862434194455023390422295)
              ·
                refine ⟨4293651291682535085633443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2862434194455023390422295 4293651291682535085633443)
                ·
                  refine ⟨6440476937523802628450165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4293651291682535085633443 6440476937523802628450165)
                  ·
                    refine ⟨603794712892856496417203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6440476937523802628450165 603794712892856496417203)
                    ·
                      rfl

theorem cell22_1763829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_1763829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1763829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1763829 prefixEnd_1763829 := by exact prefixLift 1763829
  have htrace : WordTrace (prefixWord ++ tailWord_1763829) baseStart_1763829 baseEnd_1763829 := by
    simpa [prefixWord, tailWord_1763829, baseEnd_1763829] using wordTrace_append hprefix tailTrace_1763829
  have hstable : (prefixWord ++ tailWord_1763829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763829).length < 2 ^ (prefixWord ++ tailWord_1763829).sum := by decide
  have hdescent : baseEnd_1763829 < baseStart_1763829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763900 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 3, 4]
def baseStart_1763900 : Nat := 118140960795 + 1763900 * 2 ^ 59
def prefixEnd_1763900 : Nat := 4983230072969 + 3 ^ 40 * 1763900 * 2
def baseEnd_1763900 : Nat := 603819017643835977891985

theorem tailTrace_1763900 : CollatzResearch.WordTrace tailWord_1763900 prefixEnd_1763900 603819017643835977891985 := by
  unfold tailWord_1763900
  simp only [CollatzResearch.WordTrace]
  refine ⟨32167359154849512490680577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42889812206466016654240769 32167359154849512490680577)
  ·
    refine ⟨24125519366137134368010433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32167359154849512490680577 24125519366137134368010433)
    ·
      refine ⟨18094139524602850776007825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24125519366137134368010433 18094139524602850776007825)
      ·
        refine ⟨13570604643452138082005869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18094139524602850776007825 13570604643452138082005869)
        ·
          refine ⟨5088976741294551780752201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13570604643452138082005869 5088976741294551780752201)
          ·
            refine ⟨3816732555970913835564151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5088976741294551780752201 3816732555970913835564151)
            ·
              refine ⟨5725098833956370753346227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3816732555970913835564151 5725098833956370753346227)
              ·
                refine ⟨8587648250934556130019341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5725098833956370753346227 8587648250934556130019341)
                ·
                  refine ⟨3220368094100458548757253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8587648250934556130019341 3220368094100458548757253)
                  ·
                    refine ⟨603819017643835977891985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3220368094100458548757253 603819017643835977891985)
                    ·
                      rfl

theorem cell22_1763900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_1763900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1763900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1763900 prefixEnd_1763900 := by exact prefixLift 1763900
  have htrace : WordTrace (prefixWord ++ tailWord_1763900) baseStart_1763900 baseEnd_1763900 := by
    simpa [prefixWord, tailWord_1763900, baseEnd_1763900] using wordTrace_append hprefix tailTrace_1763900
  have hstable : (prefixWord ++ tailWord_1763900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763900).length < 2 ^ (prefixWord ++ tailWord_1763900).sum := by decide
  have hdescent : baseEnd_1763900 < baseStart_1763900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763975 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 5, 3]
def baseStart_1763975 : Nat := 118140960795 + 1763975 * 2 ^ 59
def prefixEnd_1763975 : Nat := 4983230072969 + 3 ^ 40 * 1763975 * 2
def baseEnd_1763975 : Nat := 603844691676560782266755

theorem tailTrace_1763975 : CollatzResearch.WordTrace tailWord_1763975 prefixEnd_1763975 603844691676560782266755 := by
  unfold tailWord_1763975
  simp only [CollatzResearch.WordTrace]
  refine ⟨64337453784427312790341379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42891635856284875193560919 64337453784427312790341379)
  ·
    refine ⟨96506180676640969185512069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64337453784427312790341379 96506180676640969185512069)
    ·
      refine ⟨18094908876870181722283513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96506180676640969185512069 18094908876870181722283513)
      ·
        refine ⟨13571181657652636291712635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18094908876870181722283513 13571181657652636291712635)
        ·
          refine ⟨20356772486478954437568953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13571181657652636291712635 20356772486478954437568953)
          ·
            refine ⟨15267579364859215828176715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20356772486478954437568953 15267579364859215828176715)
            ·
              refine ⟨22901369047288823742265073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15267579364859215828176715 22901369047288823742265073)
              ·
                refine ⟨17176026785466617806698805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22901369047288823742265073 17176026785466617806698805)
                ·
                  refine ⟨1610252511137495419378013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17176026785466617806698805 1610252511137495419378013)
                  ·
                    refine ⟨603844691676560782266755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1610252511137495419378013 603844691676560782266755)
                    ·
                      rfl

theorem cell22_1763975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_1763975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1763975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1763975 prefixEnd_1763975 := by exact prefixLift 1763975
  have htrace : WordTrace (prefixWord ++ tailWord_1763975) baseStart_1763975 baseEnd_1763975 := by
    simpa [prefixWord, tailWord_1763975, baseEnd_1763975] using wordTrace_append hprefix tailTrace_1763975
  have hstable : (prefixWord ++ tailWord_1763975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763975).length < 2 ^ (prefixWord ++ tailWord_1763975).sum := by decide
  have hdescent : baseEnd_1763975 < baseStart_1763975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763992 : List Nat := [2, 1, 2, 4, 1, 1, 4, 1, 3, 3]
def baseStart_1763992 : Nat := 118140960795 + 1763992 * 2 ^ 59
def prefixEnd_1763992 : Nat := 4983230072969 + 3 ^ 40 * 1763992 * 2
def baseEnd_1763992 : Nat := 603850511123978404591703

theorem tailTrace_1763992 : CollatzResearch.WordTrace tailWord_1763992 prefixEnd_1763992 603850511123978404591703 := by
  unfold tailWord_1763992
  simp only [CollatzResearch.WordTrace]
  refine ⟨32169036912682862346855115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42892049216910483129140153 32169036912682862346855115)
  ·
    refine ⟨48253555369024293520282673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32169036912682862346855115 48253555369024293520282673)
    ·
      refine ⟨36190166526768220140212005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48253555369024293520282673 36190166526768220140212005)
      ·
        refine ⟨6785656223769041276289751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36190166526768220140212005 6785656223769041276289751)
        ·
          refine ⟨10178484335653561914434627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6785656223769041276289751 10178484335653561914434627)
          ·
            refine ⟨15267726503480342871651941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10178484335653561914434627 15267726503480342871651941)
            ·
              refine ⟨2862698719402564288434739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15267726503480342871651941 2862698719402564288434739)
              ·
                refine ⟨4294048079103846432652109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2862698719402564288434739 4294048079103846432652109)
                ·
                  refine ⟨1610268029663942412244541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4294048079103846432652109 1610268029663942412244541)
                  ·
                    refine ⟨603850511123978404591703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1610268029663942412244541 603850511123978404591703)
                    ·
                      rfl

theorem cell22_1763992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 3, 3].length) (baseStart_1763992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1763992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1763992 prefixEnd_1763992 := by exact prefixLift 1763992
  have htrace : WordTrace (prefixWord ++ tailWord_1763992) baseStart_1763992 baseEnd_1763992 := by
    simpa [prefixWord, tailWord_1763992, baseEnd_1763992] using wordTrace_append hprefix tailTrace_1763992
  have hstable : (prefixWord ++ tailWord_1763992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763992).length < 2 ^ (prefixWord ++ tailWord_1763992).sum := by decide
  have hdescent : baseEnd_1763992 < baseStart_1763992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764003 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 1, 7]
def baseStart_1764003 : Nat := 118140960795 + 1764003 * 2 ^ 59
def prefixEnd_1764003 : Nat := 4983230072969 + 3 ^ 40 * 1764003 * 2
def baseEnd_1764003 : Nat := 603854276648778042566669

theorem tailTrace_1764003 : CollatzResearch.WordTrace tailWord_1764003 prefixEnd_1764003 603854276648778042566669 := by
  unfold tailWord_1764003
  simp only [CollatzResearch.WordTrace]
  refine ⟨64338475028325873572360663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42892316685550582381573775 64338475028325873572360663)
  ·
    refine ⟨96507712542488810358540995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64338475028325873572360663 96507712542488810358540995)
    ·
      refine ⟨144761568813733215537811493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96507712542488810358540995 144761568813733215537811493)
      ·
        refine ⟨27142794152574977913339655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144761568813733215537811493 27142794152574977913339655)
        ·
          refine ⟨40714191228862466870009483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27142794152574977913339655 40714191228862466870009483)
          ·
            refine ⟨61071286843293700305014225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40714191228862466870009483 61071286843293700305014225)
            ·
              refine ⟨45803465132470275228760669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61071286843293700305014225 45803465132470275228760669)
              ·
                refine ⟨17176299424676353210785251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45803465132470275228760669 17176299424676353210785251)
                ·
                  refine ⟨25764449137014529816177877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17176299424676353210785251 25764449137014529816177877)
                  ·
                    refine ⟨603854276648778042566669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25764449137014529816177877 603854276648778042566669)
                    ·
                      rfl

theorem cell22_1764003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 7].length) (baseStart_1764003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764003 prefixEnd_1764003 := by exact prefixLift 1764003
  have htrace : WordTrace (prefixWord ++ tailWord_1764003) baseStart_1764003 baseEnd_1764003 := by
    simpa [prefixWord, tailWord_1764003, baseEnd_1764003] using wordTrace_append hprefix tailTrace_1764003
  have hstable : (prefixWord ++ tailWord_1764003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764003).length < 2 ^ (prefixWord ++ tailWord_1764003).sum := by decide
  have hdescent : baseEnd_1764003 < baseStart_1764003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764069 : List Nat := [1, 3, 1, 4, 1, 4, 1, 2, 1, 4]
def baseStart_1764069 : Nat := 118140960795 + 1764069 * 2 ^ 59
def prefixEnd_1764069 : Nat := 4983230072969 + 3 ^ 40 * 1764069 * 2
def baseEnd_1764069 : Nat := 603876869797575870416467

theorem tailTrace_1764069 : CollatzResearch.WordTrace tailWord_1764069 prefixEnd_1764069 603876869797575870416467 := by
  unfold tailWord_1764069
  simp only [CollatzResearch.WordTrace]
  refine ⟨64340882246086766844263261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42893921497391177896175507 64340882246086766844263261)
  ·
    refine ⟨24127830842282537566598723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64340882246086766844263261 24127830842282537566598723)
    ·
      refine ⟨36191746263423806349898085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24127830842282537566598723 36191746263423806349898085)
      ·
        refine ⟨6785952424391963690605891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36191746263423806349898085 6785952424391963690605891)
        ·
          refine ⟨10178928636587945535908837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6785952424391963690605891 10178928636587945535908837)
          ·
            refine ⟨1908549119360239787982907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10178928636587945535908837 1908549119360239787982907)
            ·
              refine ⟨2862823679040359681974361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1908549119360239787982907 2862823679040359681974361)
              ·
                refine ⟨2147117759280269761480771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2862823679040359681974361 2147117759280269761480771)
                ·
                  refine ⟨3220676638920404642221157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2147117759280269761480771 3220676638920404642221157)
                  ·
                    refine ⟨603876869797575870416467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3220676638920404642221157 603876869797575870416467)
                    ·
                      rfl

theorem cell22_1764069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 4].length) (baseStart_1764069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764069 prefixEnd_1764069 := by exact prefixLift 1764069
  have htrace : WordTrace (prefixWord ++ tailWord_1764069) baseStart_1764069 baseEnd_1764069 := by
    simpa [prefixWord, tailWord_1764069, baseEnd_1764069] using wordTrace_append hprefix tailTrace_1764069
  have hstable : (prefixWord ++ tailWord_1764069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764069).length < 2 ^ (prefixWord ++ tailWord_1764069).sum := by decide
  have hdescent : baseEnd_1764069 < baseStart_1764069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764082 : List Nat := [3, 2, 1, 3, 1, 3, 1, 2, 1, 5]
def baseStart_1764082 : Nat := 118140960795 + 1764082 * 2 ^ 59
def prefixEnd_1764082 : Nat := 4983230072969 + 3 ^ 40 * 1764082 * 2
def baseEnd_1764082 : Nat := 603881319963248169841427

theorem tailTrace_1764082 : CollatzResearch.WordTrace tailWord_1764082 prefixEnd_1764082 603881319963248169841427 := by
  unfold tailWord_1764082
  simp only [CollatzResearch.WordTrace]
  refine ⟨16085339098759917516121625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42894237596693113376324333 16085339098759917516121625)
  ·
    refine ⟨12064004324069938137091219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16085339098759917516121625 12064004324069938137091219)
    ·
      refine ⟨18096006486104907205636829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12064004324069938137091219 18096006486104907205636829)
      ·
        refine ⟨6786002432289340202113811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18096006486104907205636829 6786002432289340202113811)
        ·
          refine ⟨10179003648434010303170717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6786002432289340202113811 10179003648434010303170717)
          ·
            refine ⟨3817126368162753863689019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10179003648434010303170717 3817126368162753863689019)
            ·
              refine ⟨5725689552244130795533529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3817126368162753863689019 5725689552244130795533529)
              ·
                refine ⟨4294267164183098096650147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5725689552244130795533529 4294267164183098096650147)
                ·
                  refine ⟨6441400746274647144975221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4294267164183098096650147 6441400746274647144975221)
                  ·
                    refine ⟨603881319963248169841427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6441400746274647144975221 603881319963248169841427)
                    ·
                      rfl

theorem cell22_1764082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_1764082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764082 prefixEnd_1764082 := by exact prefixLift 1764082
  have htrace : WordTrace (prefixWord ++ tailWord_1764082) baseStart_1764082 baseEnd_1764082 := by
    simpa [prefixWord, tailWord_1764082, baseEnd_1764082] using wordTrace_append hprefix tailTrace_1764082
  have hstable : (prefixWord ++ tailWord_1764082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764082).length < 2 ^ (prefixWord ++ tailWord_1764082).sum := by decide
  have hdescent : baseEnd_1764082 < baseStart_1764082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764110 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 2, 7]
def baseStart_1764110 : Nat := 118140960795 + 1764110 * 2 ^ 59
def prefixEnd_1764110 : Nat := 4983230072969 + 3 ^ 40 * 1764110 * 2
def baseEnd_1764110 : Nat := 603890904935465430141341

theorem tailTrace_1764110 : CollatzResearch.WordTrace tailWord_1764110 prefixEnd_1764110 603890904935465430141341 := by
  unfold tailWord_1764110
  simp only [CollatzResearch.WordTrace]
  refine ⟨8042797204867278855813223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42894918425958820564337189 8042797204867278855813223)
  ·
    refine ⟨12064195807300918283719835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8042797204867278855813223 12064195807300918283719835)
    ·
      refine ⟨18096293710951377425579753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12064195807300918283719835 18096293710951377425579753)
      ·
        refine ⟨13572220283213533069184815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18096293710951377425579753 13572220283213533069184815)
        ·
          refine ⟨20358330424820299603777223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13572220283213533069184815 20358330424820299603777223)
          ·
            refine ⟨30537495637230449405665835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20358330424820299603777223 30537495637230449405665835)
            ·
              refine ⟨45806243455845674108498753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30537495637230449405665835 45806243455845674108498753)
              ·
                refine ⟨34354682591884255581374065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45806243455845674108498753 34354682591884255581374065)
                ·
                  refine ⟨25766011943913191686030549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34354682591884255581374065 25766011943913191686030549)
                  ·
                    refine ⟨603890904935465430141341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25766011943913191686030549 603890904935465430141341)
                    ·
                      rfl

theorem cell22_1764110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_1764110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764110 prefixEnd_1764110 := by exact prefixLift 1764110
  have htrace : WordTrace (prefixWord ++ tailWord_1764110) baseStart_1764110 baseEnd_1764110 := by
    simpa [prefixWord, tailWord_1764110, baseEnd_1764110] using wordTrace_append hprefix tailTrace_1764110
  have hstable : (prefixWord ++ tailWord_1764110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764110).length < 2 ^ (prefixWord ++ tailWord_1764110).sum := by decide
  have hdescent : baseEnd_1764110 < baseStart_1764110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764127 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 5, 3]
def baseStart_1764127 : Nat := 118140960795 + 1764127 * 2 ^ 59
def prefixEnd_1764127 : Nat := 4983230072969 + 3 ^ 40 * 1764127 * 2
def baseEnd_1764127 : Nat := 603896724382883052466289

theorem tailTrace_1764127 : CollatzResearch.WordTrace tailWord_1764127 prefixEnd_1764127 603896724382883052466289 := by
  unfold tailWord_1764127
  simp only [CollatzResearch.WordTrace]
  refine ⟨64342997679876642749874635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42895331786584428499916423 64342997679876642749874635)
  ·
    refine ⟨96514496519814964124811953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64342997679876642749874635 96514496519814964124811953)
    ·
      refine ⟨72385872389861223093608965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96514496519814964124811953 72385872389861223093608965)
      ·
        refine ⟨13572351073098979330051681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72385872389861223093608965 13572351073098979330051681)
        ·
          refine ⟨10179263304824234497538761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13572351073098979330051681 10179263304824234497538761)
          ·
            refine ⟨7634447478618175873154071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10179263304824234497538761 7634447478618175873154071)
            ·
              refine ⟨11451671217927263809731107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7634447478618175873154071 11451671217927263809731107)
              ·
                refine ⟨17177506826890895714596661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11451671217927263809731107 17177506826890895714596661)
                ·
                  refine ⟨1610391265021021473243437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17177506826890895714596661 1610391265021021473243437)
                  ·
                    refine ⟨603896724382883052466289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1610391265021021473243437 603896724382883052466289)
                    ·
                      rfl

theorem cell22_1764127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 3].length) (baseStart_1764127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764127 prefixEnd_1764127 := by exact prefixLift 1764127
  have htrace : WordTrace (prefixWord ++ tailWord_1764127) baseStart_1764127 baseEnd_1764127 := by
    simpa [prefixWord, tailWord_1764127, baseEnd_1764127] using wordTrace_append hprefix tailTrace_1764127
  have hstable : (prefixWord ++ tailWord_1764127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764127).length < 2 ^ (prefixWord ++ tailWord_1764127).sum := by decide
  have hdescent : baseEnd_1764127 < baseStart_1764127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764140 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 7]
def baseStart_1764140 : Nat := 118140960795 + 1764140 * 2 ^ 59
def prefixEnd_1764140 : Nat := 4983230072969 + 3 ^ 40 * 1764140 * 2
def baseEnd_1764140 : Nat := 201300391516185117297083

theorem tailTrace_1764140 : CollatzResearch.WordTrace tailWord_1764140 prefixEnd_1764140 201300391516185117297083 := by
  unfold tailWord_1764140
  simp only [CollatzResearch.WordTrace]
  refine ⟨32171735914414772985048937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42895647885886363980065249 32171735914414772985048937)
  ·
    refine ⟨24128801935811079738786703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32171735914414772985048937 24128801935811079738786703)
    ·
      refine ⟨36193202903716619608180055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24128801935811079738786703 36193202903716619608180055)
      ·
        refine ⟨54289804355574929412270083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36193202903716619608180055 54289804355574929412270083)
        ·
          refine ⟨81434706533362394118405125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54289804355574929412270083 81434706533362394118405125)
          ·
            refine ⟨15269007475005448897200961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81434706533362394118405125 15269007475005448897200961)
            ·
              refine ⟨11451755606254086672900721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15269007475005448897200961 11451755606254086672900721)
              ·
                refine ⟨8588816704690565004675541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11451755606254086672900721 8588816704690565004675541)
                ·
                  refine ⟨201300391516185117297083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8588816704690565004675541 201300391516185117297083)
                  ·
                    rfl

theorem cell22_1764140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_1764140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764140 prefixEnd_1764140 := by exact prefixLift 1764140
  have htrace : WordTrace (prefixWord ++ tailWord_1764140) baseStart_1764140 baseEnd_1764140 := by
    simpa [prefixWord, tailWord_1764140, baseEnd_1764140] using wordTrace_append hprefix tailTrace_1764140
  have hstable : (prefixWord ++ tailWord_1764140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764140).length < 2 ^ (prefixWord ++ tailWord_1764140).sum := by decide
  have hdescent : baseEnd_1764140 < baseStart_1764140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764150 : List Nat := [5, 1, 2, 2, 3, 1, 1, 2, 2, 3]
def baseStart_1764150 : Nat := 118140960795 + 1764150 * 2 ^ 59
def prefixEnd_1764150 : Nat := 4983230072969 + 3 ^ 40 * 1764150 * 2
def baseEnd_1764150 : Nat := 603904597752918659141219

theorem tailTrace_1764150 : CollatzResearch.WordTrace tailWord_1764150 prefixEnd_1764150 603904597752918659141219 := by
  unfold tailWord_1764150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4021489784924582354872619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42895891039195545118641269 4021489784924582354872619)
  ·
    refine ⟨6032234677386873532308929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4021489784924582354872619 6032234677386873532308929)
    ·
      refine ⟨4524176008040155149231697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6032234677386873532308929 4524176008040155149231697)
      ·
        refine ⟨3393132006030116361923773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4524176008040155149231697 3393132006030116361923773)
        ·
          refine ⟨1272424502261293635721415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3393132006030116361923773 1272424502261293635721415)
          ·
            refine ⟨1908636753391940453582123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1272424502261293635721415 1908636753391940453582123)
            ·
              refine ⟨2862955130087910680373185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1908636753391940453582123 2862955130087910680373185)
              ·
                refine ⟨2147216347565933010279889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2862955130087910680373185 2147216347565933010279889)
                ·
                  refine ⟨1610412260674449757709917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2147216347565933010279889 1610412260674449757709917)
                  ·
                    refine ⟨603904597752918659141219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1610412260674449757709917 603904597752918659141219)
                    ·
                      rfl

theorem cell22_1764150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_1764150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764150 prefixEnd_1764150 := by exact prefixLift 1764150
  have htrace : WordTrace (prefixWord ++ tailWord_1764150) baseStart_1764150 baseEnd_1764150 := by
    simpa [prefixWord, tailWord_1764150, baseEnd_1764150] using wordTrace_append hprefix tailTrace_1764150
  have hstable : (prefixWord ++ tailWord_1764150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764150).length < 2 ^ (prefixWord ++ tailWord_1764150).sum := by decide
  have hdescent : baseEnd_1764150 < baseStart_1764150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764170 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 2, 8]
def baseStart_1764170 : Nat := 118140960795 + 1764170 * 2 ^ 59
def prefixEnd_1764170 : Nat := 4983230072969 + 3 ^ 40 * 1764170 * 2
def baseEnd_1764170 : Nat := 603911444161645273641157

theorem tailTrace_1764170 : CollatzResearch.WordTrace tailWord_1764170 prefixEnd_1764170 603911444161645273641157 := by
  unfold tailWord_1764170
  simp only [CollatzResearch.WordTrace]
  refine ⟨16086141504680215273422491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42896377345813907395793309 16086141504680215273422491)
  ·
    refine ⟨24129212257020322910133737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16086141504680215273422491 24129212257020322910133737)
    ·
      refine ⟨18096909192765242182600303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24129212257020322910133737 18096909192765242182600303)
      ·
        refine ⟨27145363789147863273900455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18096909192765242182600303 27145363789147863273900455)
        ·
          refine ⟨40718045683721794910850683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27145363789147863273900455 40718045683721794910850683)
          ·
            refine ⟨61077068525582692366276025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40718045683721794910850683 61077068525582692366276025)
            ·
              refine ⟨45807801394187019274707019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61077068525582692366276025 45807801394187019274707019)
              ·
                refine ⟨68711702091280528912060529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45807801394187019274707019 68711702091280528912060529)
                ·
                  refine ⟨51533776568460396684045397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68711702091280528912060529 51533776568460396684045397)
                  ·
                    refine ⟨603911444161645273641157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51533776568460396684045397 603911444161645273641157)
                    ·
                      rfl

theorem cell22_1764170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_1764170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764170 prefixEnd_1764170 := by exact prefixLift 1764170
  have htrace : WordTrace (prefixWord ++ tailWord_1764170) baseStart_1764170 baseEnd_1764170 := by
    simpa [prefixWord, tailWord_1764170, baseEnd_1764170] using wordTrace_append hprefix tailTrace_1764170
  have hstable : (prefixWord ++ tailWord_1764170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764170).length < 2 ^ (prefixWord ++ tailWord_1764170).sum := by decide
  have hdescent : baseEnd_1764170 < baseStart_1764170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764172 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 2, 5]
def baseStart_1764172 : Nat := 118140960795 + 1764172 * 2 ^ 59
def prefixEnd_1764172 : Nat := 4983230072969 + 3 ^ 40 * 1764172 * 2
def baseEnd_1764172 : Nat := 603912128802517935091151

theorem tailTrace_1764172 : CollatzResearch.WordTrace tailWord_1764172 prefixEnd_1764172 603912128802517935091151 := by
  unfold tailWord_1764172
  simp only [CollatzResearch.WordTrace]
  refine ⟨32172319482356807717631385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42896425976475743623508513 32172319482356807717631385)
  ·
    refine ⟨24129239611767605788223539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32172319482356807717631385 24129239611767605788223539)
    ·
      refine ⟨36193859417651408682335309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24129239611767605788223539 36193859417651408682335309)
      ·
        refine ⟨13572697281619278255875741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36193859417651408682335309 13572697281619278255875741)
        ·
          refine ⟨5089761480607229345953403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13572697281619278255875741 5089761480607229345953403)
          ·
            refine ⟨7634642220910844018930105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5089761480607229345953403 7634642220910844018930105)
            ·
              refine ⟨5725981665683133014197579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7634642220910844018930105 5725981665683133014197579)
              ·
                refine ⟨8588972498524699521296369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5725981665683133014197579 8588972498524699521296369)
                ·
                  refine ⟨6441729373893524640972277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8588972498524699521296369 6441729373893524640972277)
                  ·
                    refine ⟨603912128802517935091151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6441729373893524640972277 603912128802517935091151)
                    ·
                      rfl

theorem cell22_1764172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_1764172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764172 prefixEnd_1764172 := by exact prefixLift 1764172
  have htrace : WordTrace (prefixWord ++ tailWord_1764172) baseStart_1764172 baseEnd_1764172 := by
    simpa [prefixWord, tailWord_1764172, baseEnd_1764172] using wordTrace_append hprefix tailTrace_1764172
  have hstable : (prefixWord ++ tailWord_1764172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764172).length < 2 ^ (prefixWord ++ tailWord_1764172).sum := by decide
  have hdescent : baseEnd_1764172 < baseStart_1764172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764277 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 1, 8]
def baseStart_1764277 : Nat := 118140960795 + 1764277 * 2 ^ 59
def prefixEnd_1764277 : Nat := 4983230072969 + 3 ^ 40 * 1764277 * 2
def baseEnd_1764277 : Nat := 603948072448332661215829

theorem tailTrace_1764277 : CollatzResearch.WordTrace tailWord_1764277 prefixEnd_1764277 603948072448332661215829 := by
  unfold tailWord_1764277
  simp only [CollatzResearch.WordTrace]
  refine ⟨64348468629333218367835085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42898979086222145578556723 64348468629333218367835085)
  ·
    refine ⟨24130675735999956887938157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64348468629333218367835085 24130675735999956887938157)
    ·
      refine ⟨9049003400999983832976809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24130675735999956887938157 9049003400999983832976809)
      ·
        refine ⟨6786752550749987874732607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9049003400999983832976809 6786752550749987874732607)
        ·
          refine ⟨10180128826124981812098911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6786752550749987874732607 10180128826124981812098911)
          ·
            refine ⟨15270193239187472718148367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10180128826124981812098911 15270193239187472718148367)
            ·
              refine ⟨22905289858781209077222551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15270193239187472718148367 22905289858781209077222551)
              ·
                refine ⟨34357934788171813615833827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22905289858781209077222551 34357934788171813615833827)
                ·
                  refine ⟨51536902182257720423750741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34357934788171813615833827 51536902182257720423750741)
                  ·
                    refine ⟨603948072448332661215829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51536902182257720423750741 603948072448332661215829)
                    ·
                      rfl

theorem cell22_1764277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_1764277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764277 prefixEnd_1764277 := by exact prefixLift 1764277
  have htrace : WordTrace (prefixWord ++ tailWord_1764277) baseStart_1764277 baseEnd_1764277 := by
    simpa [prefixWord, tailWord_1764277, baseEnd_1764277] using wordTrace_append hprefix tailTrace_1764277
  have hstable : (prefixWord ++ tailWord_1764277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764277).length < 2 ^ (prefixWord ++ tailWord_1764277).sum := by decide
  have hdescent : baseEnd_1764277 < baseStart_1764277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764296 : List Nat := [2, 1, 3, 1, 5, 1, 1, 2, 3, 3]
def baseStart_1764296 : Nat := 118140960795 + 1764296 * 2 ^ 59
def prefixEnd_1764296 : Nat := 4983230072969 + 3 ^ 40 * 1764296 * 2
def baseEnd_1764296 : Nat := 603954576536622944990771

theorem tailTrace_1764296 : CollatzResearch.WordTrace tailWord_1764296 prefixEnd_1764296 603954576536622944990771 := by
  unfold tailWord_1764296
  simp only [CollatzResearch.WordTrace]
  refine ⟨32174580808132192306388371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42899441077509589741851161 32174580808132192306388371)
  ·
    refine ⟨48261871212198288459582557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32174580808132192306388371 48261871212198288459582557)
    ·
      refine ⟨18098201704574358172343459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48261871212198288459582557 18098201704574358172343459)
      ·
        refine ⟨27147302556861537258515189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18098201704574358172343459 27147302556861537258515189)
        ·
          refine ⟨2545059614705769117985799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27147302556861537258515189 2545059614705769117985799)
          ·
            refine ⟨3817589422058653676978699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2545059614705769117985799 3817589422058653676978699)
            ·
              refine ⟨5726384133087980515468049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3817589422058653676978699 5726384133087980515468049)
              ·
                refine ⟨4294788099815985386601037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5726384133087980515468049 4294788099815985386601037)
                ·
                  refine ⟨1610545537430994519975389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4294788099815985386601037 1610545537430994519975389)
                  ·
                    refine ⟨603954576536622944990771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1610545537430994519975389 603954576536622944990771)
                    ·
                      rfl

theorem cell22_1764296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_1764296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764296 prefixEnd_1764296 := by exact prefixLift 1764296
  have htrace : WordTrace (prefixWord ++ tailWord_1764296) baseStart_1764296 baseEnd_1764296 := by
    simpa [prefixWord, tailWord_1764296, baseEnd_1764296] using wordTrace_append hprefix tailTrace_1764296
  have hstable : (prefixWord ++ tailWord_1764296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764296).length < 2 ^ (prefixWord ++ tailWord_1764296).sum := by decide
  have hdescent : baseEnd_1764296 < baseStart_1764296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764313 : List Nat := [1, 2, 1, 2, 5, 2, 2, 3, 1, 3]
def baseStart_1764313 : Nat := 118140960795 + 1764313 * 2 ^ 59
def prefixEnd_1764313 : Nat := 4983230072969 + 3 ^ 40 * 1764313 * 2
def baseEnd_1764313 : Nat := 603960395984040567315719

theorem tailTrace_1764313 : CollatzResearch.WordTrace tailWord_1764313 prefixEnd_1764313 603960395984040567315719 := by
  unfold tailWord_1764313
  simp only [CollatzResearch.WordTrace]
  refine ⟨64349781657202796516145593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42899854438135197677430395 64349781657202796516145593)
  ·
    refine ⟨48262336242902097387109195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64349781657202796516145593 48262336242902097387109195)
    ·
      refine ⟨72393504364353146080663793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48262336242902097387109195 72393504364353146080663793)
      ·
        refine ⟨54295128273264859560497845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72393504364353146080663793 54295128273264859560497845)
        ·
          refine ⟨5090168275618580583796673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54295128273264859560497845 5090168275618580583796673)
          ·
            refine ⟨3817626206713935437847505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5090168275618580583796673 3817626206713935437847505)
            ·
              refine ⟨2863219655035451578385629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3817626206713935437847505 2863219655035451578385629)
              ·
                refine ⟨1073707370638294341894611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2863219655035451578385629 1073707370638294341894611)
                ·
                  refine ⟨1610561055957441512841917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1073707370638294341894611 1610561055957441512841917)
                  ·
                    refine ⟨603960395984040567315719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1610561055957441512841917 603960395984040567315719)
                    ·
                      rfl

theorem cell22_1764313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 1, 3].length) (baseStart_1764313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764313 prefixEnd_1764313 := by exact prefixLift 1764313
  have htrace : WordTrace (prefixWord ++ tailWord_1764313) baseStart_1764313 baseEnd_1764313 := by
    simpa [prefixWord, tailWord_1764313, baseEnd_1764313] using wordTrace_append hprefix tailTrace_1764313
  have hstable : (prefixWord ++ tailWord_1764313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764313).length < 2 ^ (prefixWord ++ tailWord_1764313).sum := by decide
  have hdescent : baseEnd_1764313 < baseStart_1764313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764386 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 4, 3]
def baseStart_1764386 : Nat := 118140960795 + 1764386 * 2 ^ 59
def prefixEnd_1764386 : Nat := 4983230072969 + 3 ^ 40 * 1764386 * 2
def baseEnd_1764386 : Nat := 603985385375892710240495

theorem tailTrace_1764386 : CollatzResearch.WordTrace tailWord_1764386 prefixEnd_1764386 603985385375892710240495 := by
  unfold tailWord_1764386
  simp only [CollatzResearch.WordTrace]
  refine ⟨16088111046484582495888253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42901629457292219989035341 16088111046484582495888253)
  ·
    refine ⟨6033041642431718435958095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16088111046484582495888253 6033041642431718435958095)
    ·
      refine ⟨9049562463647577653937143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6033041642431718435958095 9049562463647577653937143)
      ·
        refine ⟨13574343695471366480905715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9049562463647577653937143 13574343695471366480905715)
        ·
          refine ⟨20361515543207049721358573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13574343695471366480905715 20361515543207049721358573)
          ·
            refine ⟨7635568328702643645509465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20361515543207049721358573 7635568328702643645509465)
            ·
              refine ⟨5726676246526982734132099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7635568328702643645509465 5726676246526982734132099)
              ·
                refine ⟨8590014369790474101198149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5726676246526982734132099 8590014369790474101198149)
                ·
                  refine ⟨1610627694335713893974653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8590014369790474101198149 1610627694335713893974653)
                  ·
                    refine ⟨603985385375892710240495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1610627694335713893974653 603985385375892710240495)
                    ·
                      rfl

theorem cell22_1764386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_1764386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764386 prefixEnd_1764386 := by exact prefixLift 1764386
  have htrace : WordTrace (prefixWord ++ tailWord_1764386) baseStart_1764386 baseEnd_1764386 := by
    simpa [prefixWord, tailWord_1764386, baseEnd_1764386] using wordTrace_append hprefix tailTrace_1764386
  have hstable : (prefixWord ++ tailWord_1764386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764386).length < 2 ^ (prefixWord ++ tailWord_1764386).sum := by decide
  have hdescent : baseEnd_1764386 < baseStart_1764386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764448 : List Nat := [2, 1, 1, 3, 2, 2, 3, 4, 1, 3]
def baseStart_1764448 : Nat := 118140960795 + 1764448 * 2 ^ 59
def prefixEnd_1764448 : Nat := 4983230072969 + 3 ^ 40 * 1764448 * 2
def baseEnd_1764448 : Nat := 604006609242945215190305

theorem tailTrace_1764448 : CollatzResearch.WordTrace tailWord_1764448 prefixEnd_1764448 604006609242945215190305 := by
  unfold tailWord_1764448
  simp only [CollatzResearch.WordTrace]
  refine ⟨32177352755856857286154999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42903137007809143048206665 32177352755856857286154999)
  ·
    refine ⟨48266029133785285929232499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32177352755856857286154999 48266029133785285929232499)
    ·
      refine ⟨72399043700677928893848749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48266029133785285929232499 72399043700677928893848749)
      ·
        refine ⟨27149641387754223335193281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72399043700677928893848749 27149641387754223335193281)
        ·
          refine ⟨20362231040815667501394961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27149641387754223335193281 20362231040815667501394961)
          ·
            refine ⟨15271673280611750626046221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20362231040815667501394961 15271673280611750626046221)
            ·
              refine ⟨5726877480229406484767333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15271673280611750626046221 5726877480229406484767333)
              ·
                refine ⟨1073789527543013715893875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5726877480229406484767333 1073789527543013715893875)
                ·
                  refine ⟨1610684291314520573840813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1073789527543013715893875 1610684291314520573840813)
                  ·
                    refine ⟨604006609242945215190305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1610684291314520573840813 604006609242945215190305)
                    ·
                      rfl

theorem cell22_1764448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 1, 3].length) (baseStart_1764448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764448 prefixEnd_1764448 := by exact prefixLift 1764448
  have htrace : WordTrace (prefixWord ++ tailWord_1764448) baseStart_1764448 baseEnd_1764448 := by
    simpa [prefixWord, tailWord_1764448, baseEnd_1764448] using wordTrace_append hprefix tailTrace_1764448
  have hstable : (prefixWord ++ tailWord_1764448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764448).length < 2 ^ (prefixWord ++ tailWord_1764448).sum := by decide
  have hdescent : baseEnd_1764448 < baseStart_1764448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764461 : List Nat := [1, 5, 1, 1, 2, 2, 2, 3, 5]
def baseStart_1764461 : Nat := 118140960795 + 1764461 * 2 ^ 59
def prefixEnd_1764461 : Nat := 4983230072969 + 3 ^ 40 * 1764461 * 2
def baseEnd_1764461 : Nat := 201337019802872504871755

theorem tailTrace_1764461 : CollatzResearch.WordTrace tailWord_1764461 prefixEnd_1764461 201337019802872504871755 := by
  unfold tailWord_1764461
  simp only [CollatzResearch.WordTrace]
  refine ⟨64355179660666617792533237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42903453107111078528355491 64355179660666617792533237)
  ·
    refine ⟨6033298093187495418049991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64355179660666617792533237 6033298093187495418049991)
    ·
      refine ⟨9049947139781243127074987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6033298093187495418049991 9049947139781243127074987)
      ·
        refine ⟨13574920709671864690612481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9049947139781243127074987 13574920709671864690612481)
        ·
          refine ⟨10181190532253898517959361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13574920709671864690612481 10181190532253898517959361)
          ·
            refine ⟨7635892899190423888469521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10181190532253898517959361 7635892899190423888469521)
            ·
              refine ⟨5726919674392817916352141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7635892899190423888469521 5726919674392817916352141)
              ·
                refine ⟨2147594877897306718632053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5726919674392817916352141 2147594877897306718632053)
                ·
                  refine ⟨201337019802872504871755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2147594877897306718632053 201337019802872504871755)
                  ·
                    rfl

theorem cell22_1764461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_1764461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764461 prefixEnd_1764461 := by exact prefixLift 1764461
  have htrace : WordTrace (prefixWord ++ tailWord_1764461) baseStart_1764461 baseEnd_1764461 := by
    simpa [prefixWord, tailWord_1764461, baseEnd_1764461] using wordTrace_append hprefix tailTrace_1764461
  have hstable : (prefixWord ++ tailWord_1764461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764461).length < 2 ^ (prefixWord ++ tailWord_1764461).sum := by decide
  have hdescent : baseEnd_1764461 < baseStart_1764461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764506 : List Nat := [3, 1, 1, 5, 1, 1, 1, 3, 6]
def baseStart_1764506 : Nat := 118140960795 + 1764506 * 2 ^ 59
def prefixEnd_1764506 : Nat := 4983230072969 + 3 ^ 40 * 1764506 * 2
def baseEnd_1764506 : Nat := 201342154609417465746709

theorem tailTrace_1764506 : CollatzResearch.WordTrace tailWord_1764506 prefixEnd_1764506 201342154609417465746709 := by
  unfold tailWord_1764506
  simp only [CollatzResearch.WordTrace]
  refine ⟨16089205236375897619480343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42904547297002393651947581 16089205236375897619480343)
  ·
    refine ⟨24133807854563846429220515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16089205236375897619480343 24133807854563846429220515)
    ·
      refine ⟨36200711781845769643830773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24133807854563846429220515 36200711781845769643830773)
      ·
        refine ⟨3393816729548040904109135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36200711781845769643830773 3393816729548040904109135)
        ·
          refine ⟨5090725094322061356163703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3393816729548040904109135 5090725094322061356163703)
          ·
            refine ⟨7636087641483092034245555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5090725094322061356163703 7636087641483092034245555)
            ·
              refine ⟨11454131462224638051368333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7636087641483092034245555 11454131462224638051368333)
              ·
                refine ⟨4295299298334239269263125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11454131462224638051368333 4295299298334239269263125)
                ·
                  refine ⟨201342154609417465746709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4295299298334239269263125 201342154609417465746709)
                  ·
                    rfl

theorem cell22_1764506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_1764506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764506 prefixEnd_1764506 := by exact prefixLift 1764506
  have htrace : WordTrace (prefixWord ++ tailWord_1764506) baseStart_1764506 baseEnd_1764506 := by
    simpa [prefixWord, tailWord_1764506, baseEnd_1764506] using wordTrace_append hprefix tailTrace_1764506
  have hstable : (prefixWord ++ tailWord_1764506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764506).length < 2 ^ (prefixWord ++ tailWord_1764506).sum := by decide
  have hdescent : baseEnd_1764506 < baseStart_1764506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764525 : List Nat := [1, 5, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_1764525 : Nat := 118140960795 + 1764525 * 2 ^ 59
def prefixEnd_1764525 : Nat := 4983230072969 + 3 ^ 40 * 1764525 * 2
def baseEnd_1764525 : Nat := 604032967916542681015069

theorem tailTrace_1764525 : CollatzResearch.WordTrace tailWord_1764525 prefixEnd_1764525 604032967916542681015069 := by
  unfold tailWord_1764525
  simp only [CollatzResearch.WordTrace]
  refine ⟨64357513932434756722863029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42905009288289837815242019 64357513932434756722863029)
  ·
    refine ⟨6033516931165758442768409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64357513932434756722863029 6033516931165758442768409)
    ·
      refine ⟨4525137698374318832076307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6033516931165758442768409 4525137698374318832076307)
      ·
        refine ⟨6787706547561478248114461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4525137698374318832076307 6787706547561478248114461)
        ·
          refine ⟨2545389955335554343042923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6787706547561478248114461 2545389955335554343042923)
          ·
            refine ⟨3818084933003331514564385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2545389955335554343042923 3818084933003331514564385)
            ·
              refine ⟨2863563699752498635923289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3818084933003331514564385 2863563699752498635923289)
              ·
                refine ⟨2147672774814373976942467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2863563699752498635923289 2147672774814373976942467)
                ·
                  refine ⟨3221509162221560965413701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2147672774814373976942467 3221509162221560965413701)
                  ·
                    refine ⟨604032967916542681015069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3221509162221560965413701 604032967916542681015069)
                    ·
                      rfl

theorem cell22_1764525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_1764525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764525 prefixEnd_1764525 := by exact prefixLift 1764525
  have htrace : WordTrace (prefixWord ++ tailWord_1764525) baseStart_1764525 baseEnd_1764525 := by
    simpa [prefixWord, tailWord_1764525, baseEnd_1764525] using wordTrace_append hprefix tailTrace_1764525
  have hstable : (prefixWord ++ tailWord_1764525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764525).length < 2 ^ (prefixWord ++ tailWord_1764525).sum := by decide
  have hdescent : baseEnd_1764525 < baseStart_1764525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764540 : List Nat := [2, 2, 2, 3, 2, 3, 1, 3, 4]
def baseStart_1764540 : Nat := 118140960795 + 1764540 * 2 ^ 59
def prefixEnd_1764540 : Nat := 4983230072969 + 3 ^ 40 * 1764540 * 2
def baseEnd_1764540 : Nat := 201346034241029213963341

theorem tailTrace_1764540 : CollatzResearch.WordTrace tailWord_1764540 prefixEnd_1764540 201346034241029213963341 := by
  unfold tailWord_1764540
  simp only [CollatzResearch.WordTrace]
  refine ⟨32179030513690207142329537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42905374018253609523106049 32179030513690207142329537)
  ·
    refine ⟨24134272885267655356747153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32179030513690207142329537 24134272885267655356747153)
    ·
      refine ⟨18100704663950741517560365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24134272885267655356747153 18100704663950741517560365)
      ·
        refine ⟨6787764248981528069085137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18100704663950741517560365 6787764248981528069085137)
        ·
          refine ⟨5090823186736146051813853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6787764248981528069085137 5090823186736146051813853)
          ·
            refine ⟨1909058695026054769430195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5090823186736146051813853 1909058695026054769430195)
            ·
              refine ⟨2863588042539082154145293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1909058695026054769430195 2863588042539082154145293)
              ·
                refine ⟨1073845515952155807804485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2863588042539082154145293 1073845515952155807804485)
                ·
                  refine ⟨201346034241029213963341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1073845515952155807804485 201346034241029213963341)
                  ·
                    rfl

theorem cell22_1764540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 4].length) (baseStart_1764540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764540 prefixEnd_1764540 := by exact prefixLift 1764540
  have htrace : WordTrace (prefixWord ++ tailWord_1764540) baseStart_1764540 baseEnd_1764540 := by
    simpa [prefixWord, tailWord_1764540, baseEnd_1764540] using wordTrace_append hprefix tailTrace_1764540
  have hstable : (prefixWord ++ tailWord_1764540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764540).length < 2 ^ (prefixWord ++ tailWord_1764540).sum := by decide
  have hdescent : baseEnd_1764540 < baseStart_1764540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764557 : List Nat := [1, 6, 2, 2, 1, 2, 1, 1, 6]
def baseStart_1764557 : Nat := 118140960795 + 1764557 * 2 ^ 59
def prefixEnd_1764557 : Nat := 4983230072969 + 3 ^ 40 * 1764557 * 2
def baseEnd_1764557 : Nat := 201347974056835088071657

theorem tailTrace_1764557 : CollatzResearch.WordTrace tailWord_1764557 prefixEnd_1764557 201347974056835088071657 := by
  unfold tailWord_1764557
  simp only [CollatzResearch.WordTrace]
  refine ⟨64358681068318826188027925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42905787378879217458685283 64358681068318826188027925)
  ·
    refine ⟨3016813175077444977563809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 64358681068318826188027925 3016813175077444977563809)
    ·
      refine ⟨2262609881308083733172857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3016813175077444977563809 2262609881308083733172857)
      ·
        refine ⟨1696957410981062799879643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2262609881308083733172857 1696957410981062799879643)
        ·
          refine ⟨2545436116471594199819465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1696957410981062799879643 2545436116471594199819465)
          ·
            refine ⟨1909077087353695649864599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2545436116471594199819465 1909077087353695649864599)
            ·
              refine ⟨2863615631030543474796899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1909077087353695649864599 2863615631030543474796899)
              ·
                refine ⟨4295423446545815212195349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2863615631030543474796899 4295423446545815212195349)
                ·
                  refine ⟨201347974056835088071657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4295423446545815212195349 201347974056835088071657)
                  ·
                    rfl

theorem cell22_1764557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_1764557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764557 prefixEnd_1764557 := by exact prefixLift 1764557
  have htrace : WordTrace (prefixWord ++ tailWord_1764557) baseStart_1764557 baseEnd_1764557 := by
    simpa [prefixWord, tailWord_1764557, baseEnd_1764557] using wordTrace_append hprefix tailTrace_1764557
  have hstable : (prefixWord ++ tailWord_1764557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764557).length < 2 ^ (prefixWord ++ tailWord_1764557).sum := by decide
  have hdescent : baseEnd_1764557 < baseStart_1764557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764656 : List Nat := [2, 1, 1, 1, 2, 2, 3, 4, 1, 5]
def baseStart_1764656 : Nat := 118140960795 + 1764656 * 2 ^ 59
def prefixEnd_1764656 : Nat := 4983230072969 + 3 ^ 40 * 1764656 * 2
def baseEnd_1764656 : Nat := 604077811893702005989667

theorem tailTrace_1764656 : CollatzResearch.WordTrace tailWord_1764656 prefixEnd_1764656 604077811893702005989667 := by
  unfold tailWord_1764656
  simp only [CollatzResearch.WordTrace]
  refine ⟨32181145947480083047940911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42908194596640110730587881 32181145947480083047940911)
  ·
    refine ⟨48271718921220124571911367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32181145947480083047940911 48271718921220124571911367)
    ·
      refine ⟨72407578381830186857867051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48271718921220124571911367 72407578381830186857867051)
      ·
        refine ⟨108611367572745280286800577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72407578381830186857867051 108611367572745280286800577)
        ·
          refine ⟨81458525679558960215100433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108611367572745280286800577 81458525679558960215100433)
          ·
            refine ⟨61093894259669220161325325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81458525679558960215100433 61093894259669220161325325)
            ·
              refine ⟨22910210347375957560496997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61093894259669220161325325 22910210347375957560496997)
              ·
                refine ⟨4295664440132992042593187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22910210347375957560496997 4295664440132992042593187)
                ·
                  refine ⟨6443496660199488063889781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4295664440132992042593187 6443496660199488063889781)
                  ·
                    refine ⟨604077811893702005989667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6443496660199488063889781 604077811893702005989667)
                    ·
                      rfl

theorem cell22_1764656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 1, 5].length) (baseStart_1764656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764656 prefixEnd_1764656 := by exact prefixLift 1764656
  have htrace : WordTrace (prefixWord ++ tailWord_1764656) baseStart_1764656 baseEnd_1764656 := by
    simpa [prefixWord, tailWord_1764656, baseEnd_1764656] using wordTrace_append hprefix tailTrace_1764656
  have hstable : (prefixWord ++ tailWord_1764656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764656).length < 2 ^ (prefixWord ++ tailWord_1764656).sum := by decide
  have hdescent : baseEnd_1764656 < baseStart_1764656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764660 : List Nat := [2, 5, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_1764660 : Nat := 118140960795 + 1764660 * 2 ^ 59
def prefixEnd_1764660 : Nat := 4983230072969 + 3 ^ 40 * 1764660 * 2
def baseEnd_1764660 : Nat := 604079181175447328889655

theorem tailTrace_1764660 : CollatzResearch.WordTrace tailWord_1764660 prefixEnd_1764660 604079181175447328889655 := by
  unfold tailWord_1764660
  simp only [CollatzResearch.WordTrace]
  refine ⟨32181218893472837389513717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42908291857963783186018289 32181218893472837389513717)
  ·
    refine ⟨3016989271263078505266911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32181218893472837389513717 3016989271263078505266911)
    ·
      refine ⟨4525483906894617757900367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3016989271263078505266911 4525483906894617757900367)
      ·
        refine ⟨6788225860341926636850551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4525483906894617757900367 6788225860341926636850551)
        ·
          refine ⟨10182338790512889955275827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6788225860341926636850551 10182338790512889955275827)
          ·
            refine ⟨15273508185769334932913741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10182338790512889955275827 15273508185769334932913741)
            ·
              refine ⟨5727565569663500599842653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15273508185769334932913741 5727565569663500599842653)
              ·
                refine ⟨2147837088623812724940995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5727565569663500599842653 2147837088623812724940995)
                ·
                  refine ⟨3221755632935719087411493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2147837088623812724940995 3221755632935719087411493)
                  ·
                    refine ⟨604079181175447328889655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3221755632935719087411493 604079181175447328889655)
                    ·
                      rfl

theorem cell22_1764660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_1764660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764660 prefixEnd_1764660 := by exact prefixLift 1764660
  have htrace : WordTrace (prefixWord ++ tailWord_1764660) baseStart_1764660 baseEnd_1764660 := by
    simpa [prefixWord, tailWord_1764660, baseEnd_1764660] using wordTrace_append hprefix tailTrace_1764660
  have hstable : (prefixWord ++ tailWord_1764660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764660).length < 2 ^ (prefixWord ++ tailWord_1764660).sum := by decide
  have hdescent : baseEnd_1764660 < baseStart_1764660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764686 : List Nat := [4, 1, 1, 1, 1, 1, 4, 9]
def baseStart_1764686 : Nat := 118140960795 + 1764686 * 2 ^ 59
def prefixEnd_1764686 : Nat := 4983230072969 + 3 ^ 40 * 1764686 * 2
def baseEnd_1764686 : Nat := 67120897945199103082175

theorem tailTrace_1764686 : CollatzResearch.WordTrace tailWord_1764686 prefixEnd_1764686 67120897945199103082175 := by
  unfold tailWord_1764686
  simp only [CollatzResearch.WordTrace]
  refine ⟨8045423260606435152434239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42908924056567654146315941 8045423260606435152434239)
  ·
    refine ⟨12068134890909652728651359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8045423260606435152434239 12068134890909652728651359)
    ·
      refine ⟨18102202336364479092977039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12068134890909652728651359 18102202336364479092977039)
      ·
        refine ⟨27153303504546718639465559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18102202336364479092977039 27153303504546718639465559)
        ·
          refine ⟨40729955256820077959198339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27153303504546718639465559 40729955256820077959198339)
          ·
            refine ⟨61094932885230116938797509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40729955256820077959198339 61094932885230116938797509)
            ·
              refine ⟨11455299915980646926024533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61094932885230116938797509 11455299915980646926024533)
              ·
                refine ⟨67120897945199103082175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11455299915980646926024533 67120897945199103082175)
                ·
                  rfl

theorem cell22_1764686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_1764686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764686 prefixEnd_1764686 := by exact prefixLift 1764686
  have htrace : WordTrace (prefixWord ++ tailWord_1764686) baseStart_1764686 baseEnd_1764686 := by
    simpa [prefixWord, tailWord_1764686, baseEnd_1764686] using wordTrace_append hprefix tailTrace_1764686
  have hstable : (prefixWord ++ tailWord_1764686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764686).length < 2 ^ (prefixWord ++ tailWord_1764686).sum := by decide
  have hdescent : baseEnd_1764686 < baseStart_1764686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764731 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 7]
def baseStart_1764731 : Nat := 118140960795 + 1764731 * 2 ^ 59
def prefixEnd_1764731 : Nat := 4983230072969 + 3 ^ 40 * 1764731 * 2
def baseEnd_1764731 : Nat := 201367828642142270121479

theorem tailTrace_1764731 : CollatzResearch.WordTrace tailWord_1764731 prefixEnd_1764731 201367828642142270121479 := by
  unfold tailWord_1764731
  simp only [CollatzResearch.WordTrace]
  refine ⟨64365027369688453904862047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42910018246458969269908031 64365027369688453904862047)
  ·
    refine ⟨96547541054532680857293071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64365027369688453904862047 96547541054532680857293071)
    ·
      refine ⟨144821311581799021285939607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96547541054532680857293071 144821311581799021285939607)
      ·
        refine ⟨217231967372698531928909411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144821311581799021285939607 217231967372698531928909411)
        ·
          refine ⟨325847951059047797893364117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217231967372698531928909411 325847951059047797893364117)
          ·
            refine ⟨15274122705892865526251443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 325847951059047797893364117 15274122705892865526251443)
            ·
              refine ⟨22911184058839298289377165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15274122705892865526251443 22911184058839298289377165)
              ·
                refine ⟨8591694022064736858516437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22911184058839298289377165 8591694022064736858516437)
                ·
                  refine ⟨201367828642142270121479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8591694022064736858516437 201367828642142270121479)
                  ·
                    rfl

theorem cell22_1764731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 7].length) (baseStart_1764731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764731 prefixEnd_1764731 := by exact prefixLift 1764731
  have htrace : WordTrace (prefixWord ++ tailWord_1764731) baseStart_1764731 baseEnd_1764731 := by
    simpa [prefixWord, tailWord_1764731, baseEnd_1764731] using wordTrace_append hprefix tailTrace_1764731
  have hstable : (prefixWord ++ tailWord_1764731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764731).length < 2 ^ (prefixWord ++ tailWord_1764731).sum := by decide
  have hdescent : baseEnd_1764731 < baseStart_1764731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764748 : List Nat := [2, 2, 1, 2, 1, 3, 3, 3, 5]
def baseStart_1764748 : Nat := 118140960795 + 1764748 * 2 ^ 59
def prefixEnd_1764748 : Nat := 4983230072969 + 3 ^ 40 * 1764748 * 2
def baseEnd_1764748 : Nat := 201369768457948144229795

theorem tailTrace_1764748 : CollatzResearch.WordTrace tailWord_1764748 prefixEnd_1764748 201369768457948144229795 := by
  unfold tailWord_1764748
  simp only [CollatzResearch.WordTrace]
  refine ⟨32182823705313432904115449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42910431607084577205487265 32182823705313432904115449)
  ·
    refine ⟨24137117778985074678086587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32182823705313432904115449 24137117778985074678086587)
    ·
      refine ⟨36205676668477612017129881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24137117778985074678086587 36205676668477612017129881)
      ·
        refine ⟨27154257501358209012847411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36205676668477612017129881 27154257501358209012847411)
        ·
          refine ⟨40731386252037313519271117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27154257501358209012847411 40731386252037313519271117)
          ·
            refine ⟨15274269844513992569726669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40731386252037313519271117 15274269844513992569726669)
            ·
              refine ⟨5727851191692747213647501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15274269844513992569726669 5727851191692747213647501)
              ·
                refine ⟨2147944196884780205117813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5727851191692747213647501 2147944196884780205117813)
                ·
                  refine ⟨201369768457948144229795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2147944196884780205117813 201369768457948144229795)
                  ·
                    rfl

theorem cell22_1764748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_1764748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764748 prefixEnd_1764748 := by exact prefixLift 1764748
  have htrace : WordTrace (prefixWord ++ tailWord_1764748) baseStart_1764748 baseEnd_1764748 := by
    simpa [prefixWord, tailWord_1764748, baseEnd_1764748] using wordTrace_append hprefix tailTrace_1764748
  have hstable : (prefixWord ++ tailWord_1764748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764748).length < 2 ^ (prefixWord ++ tailWord_1764748).sum := by decide
  have hdescent : baseEnd_1764748 < baseStart_1764748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764829 : List Nat := [1, 4, 3, 1, 1, 4, 2, 1, 1, 4]
def baseStart_1764829 : Nat := 118140960795 + 1764829 * 2 ^ 59
def prefixEnd_1764829 : Nat := 4983230072969 + 3 ^ 40 * 1764829 * 2
def baseEnd_1764829 : Nat := 604137033329187221414137

theorem tailTrace_1764829 : CollatzResearch.WordTrace tailWord_1764829 prefixEnd_1764829 604137033329187221414137 := by
  unfold tailWord_1764829
  simp only [CollatzResearch.WordTrace]
  refine ⟨64368601723333416641929541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42912401148888944427953027 64368601723333416641929541)
  ·
    refine ⟨12069112823125015620361789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64368601723333416641929541 12069112823125015620361789)
    ·
      refine ⟨4525917308671880857635671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12069112823125015620361789 4525917308671880857635671)
      ·
        refine ⟨6788875963007821286453507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4525917308671880857635671 6788875963007821286453507)
        ·
          refine ⟨10183313944511731929680261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6788875963007821286453507 10183313944511731929680261)
          ·
            refine ⟨1909371364595949736815049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10183313944511731929680261 1909371364595949736815049)
            ·
              refine ⟨1432028523446962302611287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1909371364595949736815049 1432028523446962302611287)
              ·
                refine ⟨2148042785170443453916931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1432028523446962302611287 2148042785170443453916931)
                ·
                  refine ⟨3222064177755665180875397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2148042785170443453916931 3222064177755665180875397)
                  ·
                    refine ⟨604137033329187221414137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3222064177755665180875397 604137033329187221414137)
                    ·
                      rfl

theorem cell22_1764829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_1764829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764829 prefixEnd_1764829 := by exact prefixLift 1764829
  have htrace : WordTrace (prefixWord ++ tailWord_1764829) baseStart_1764829 baseEnd_1764829 := by
    simpa [prefixWord, tailWord_1764829, baseEnd_1764829] using wordTrace_append hprefix tailTrace_1764829
  have hstable : (prefixWord ++ tailWord_1764829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764829).length < 2 ^ (prefixWord ++ tailWord_1764829).sum := by decide
  have hdescent : baseEnd_1764829 < baseStart_1764829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764842 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 4, 3]
def baseStart_1764842 : Nat := 118140960795 + 1764842 * 2 ^ 59
def prefixEnd_1764842 : Nat := 4983230072969 + 3 ^ 40 * 1764842 * 2
def baseEnd_1764842 : Nat := 604141483494859520839097

theorem tailTrace_1764842 : CollatzResearch.WordTrace tailWord_1764842 prefixEnd_1764842 604141483494859520839097 := by
  unfold tailWord_1764842
  simp only [CollatzResearch.WordTrace]
  refine ⟨16092268968071579965538195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42912717248190879908101853 16092268968071579965538195)
  ·
    refine ⟨24138403452107369948307293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16092268968071579965538195 24138403452107369948307293)
    ·
      refine ⟨9051901294540263730615235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24138403452107369948307293 9051901294540263730615235)
      ·
        refine ⟨13577851941810395595922853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9051901294540263730615235 13577851941810395595922853)
        ·
          refine ⟨2545847239089449174235535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13577851941810395595922853 2545847239089449174235535)
          ·
            refine ⟨3818770858634173761353303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2545847239089449174235535 3818770858634173761353303)
            ·
              refine ⟨5728156287951260642029955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3818770858634173761353303 5728156287951260642029955)
              ·
                refine ⟨8592234431926890963044933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5728156287951260642029955 8592234431926890963044933)
                ·
                  refine ⟨1611043955986292055570925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8592234431926890963044933 1611043955986292055570925)
                  ·
                    refine ⟨604141483494859520839097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1611043955986292055570925 604141483494859520839097)
                    ·
                      rfl

theorem cell22_1764842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_1764842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764842 prefixEnd_1764842 := by exact prefixLift 1764842
  have htrace : WordTrace (prefixWord ++ tailWord_1764842) baseStart_1764842 baseEnd_1764842 := by
    simpa [prefixWord, tailWord_1764842, baseEnd_1764842] using wordTrace_append hprefix tailTrace_1764842
  have hstable : (prefixWord ++ tailWord_1764842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764842).length < 2 ^ (prefixWord ++ tailWord_1764842).sum := by decide
  have hdescent : baseEnd_1764842 < baseStart_1764842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764883 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 7]
def baseStart_1764883 : Nat := 118140960795 + 1764883 * 2 ^ 59
def prefixEnd_1764883 : Nat := 4983230072969 + 3 ^ 40 * 1764883 * 2
def baseEnd_1764883 : Nat := 201385172877583026854657

theorem tailTrace_1764883 : CollatzResearch.WordTrace tailWord_1764883 prefixEnd_1764883 201385172877583026854657 := by
  unfold tailWord_1764883
  simp only [CollatzResearch.WordTrace]
  refine ⟨64370571265137783864395303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42913714176758522576263535 64370571265137783864395303)
  ·
    refine ⟨96555856897706675796592955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64370571265137783864395303 96555856897706675796592955)
    ·
      refine ⟨144833785346560013694889433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96555856897706675796592955 144833785346560013694889433)
      ·
        refine ⟨108625339009920010271167075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144833785346560013694889433 108625339009920010271167075)
        ·
          refine ⟨162938008514880015406750613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108625339009920010271167075 162938008514880015406750613)
          ·
            refine ⟨7637719149135000722191435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 162938008514880015406750613 7637719149135000722191435)
            ·
              refine ⟨11456578723702501083287153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7637719149135000722191435 11456578723702501083287153)
              ·
                refine ⟨8592434042776875812465365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11456578723702501083287153 8592434042776875812465365)
                ·
                  refine ⟨201385172877583026854657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8592434042776875812465365 201385172877583026854657)
                  ·
                    rfl

theorem cell22_1764883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 7].length) (baseStart_1764883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764883 prefixEnd_1764883 := by exact prefixLift 1764883
  have htrace : WordTrace (prefixWord ++ tailWord_1764883) baseStart_1764883 baseEnd_1764883 := by
    simpa [prefixWord, tailWord_1764883, baseEnd_1764883] using wordTrace_append hprefix tailTrace_1764883
  have hstable : (prefixWord ++ tailWord_1764883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764883).length < 2 ^ (prefixWord ++ tailWord_1764883).sum := by decide
  have hdescent : baseEnd_1764883 < baseStart_1764883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764913 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 2, 8]
def baseStart_1764913 : Nat := 118140960795 + 1764913 * 2 ^ 59
def prefixEnd_1764913 : Nat := 4983230072969 + 3 ^ 40 * 1764913 * 2
def baseEnd_1764913 : Nat := 604165788245839002313879

theorem tailTrace_1764913 : CollatzResearch.WordTrace tailWord_1764913 prefixEnd_1764913 604165788245839002313879 := by
  unfold tailWord_1764913
  simp only [CollatzResearch.WordTrace]
  refine ⟨64371665455029098987987393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42914443636686065991991595 64371665455029098987987393)
  ·
    refine ⟨48278749091271824240990545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64371665455029098987987393 48278749091271824240990545)
    ·
      refine ⟨36209061818453868180742909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48278749091271824240990545 36209061818453868180742909)
      ·
        refine ⟨13578398181920200567778591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36209061818453868180742909 13578398181920200567778591)
        ·
          refine ⟨20367597272880300851667887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13578398181920200567778591 20367597272880300851667887)
          ·
            refine ⟨30551395909320451277501831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20367597272880300851667887 30551395909320451277501831)
            ·
              refine ⟨45827093863980676916252747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30551395909320451277501831 45827093863980676916252747)
              ·
                refine ⟨68740640795971015374379121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45827093863980676916252747 68740640795971015374379121)
                ·
                  refine ⟨51555480596978261530784341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68740640795971015374379121 51555480596978261530784341)
                  ·
                    refine ⟨604165788245839002313879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51555480596978261530784341 604165788245839002313879)
                    ·
                      rfl

theorem cell22_1764913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_1764913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764913 prefixEnd_1764913 := by exact prefixLift 1764913
  have htrace : WordTrace (prefixWord ++ tailWord_1764913) baseStart_1764913 baseEnd_1764913 := by
    simpa [prefixWord, tailWord_1764913, baseEnd_1764913] using wordTrace_append hprefix tailTrace_1764913
  have hstable : (prefixWord ++ tailWord_1764913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764913).length < 2 ^ (prefixWord ++ tailWord_1764913).sum := by decide
  have hdescent : baseEnd_1764913 < baseStart_1764913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764917 : List Nat := [1, 3, 3, 1, 1, 3, 4, 1, 5]
def baseStart_1764917 : Nat := 118140960795 + 1764917 * 2 ^ 59
def prefixEnd_1764917 : Nat := 4983230072969 + 3 ^ 40 * 1764917 * 2
def baseEnd_1764917 : Nat := 201389052509194775071289

theorem tailTrace_1764917 : CollatzResearch.WordTrace tailWord_1764917 prefixEnd_1764917 201389052509194775071289 := by
  unfold tailWord_1764917
  simp only [CollatzResearch.WordTrace]
  refine ⟨64371811347014607671133005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42914540898009738447422003 64371811347014607671133005)
  ·
    refine ⟨24139429255130477876674877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64371811347014607671133005 24139429255130477876674877)
    ·
      refine ⟨9052285970673929203753079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24139429255130477876674877 9052285970673929203753079)
      ·
        refine ⟨13578428956010893805629619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9052285970673929203753079 13578428956010893805629619)
        ·
          refine ⟨20367643434016340708444429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13578428956010893805629619 20367643434016340708444429)
          ·
            refine ⟨7637866287756127765666661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20367643434016340708444429 7637866287756127765666661)
            ·
              refine ⟨1432099928954273956062499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7637866287756127765666661 1432099928954273956062499)
              ·
                refine ⟨2148149893431410934093749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1432099928954273956062499 2148149893431410934093749)
                ·
                  refine ⟨201389052509194775071289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2148149893431410934093749 201389052509194775071289)
                  ·
                    rfl

theorem cell22_1764917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 5].length) (baseStart_1764917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764917 prefixEnd_1764917 := by exact prefixLift 1764917
  have htrace : WordTrace (prefixWord ++ tailWord_1764917) baseStart_1764917 baseEnd_1764917 := by
    simpa [prefixWord, tailWord_1764917, baseEnd_1764917] using wordTrace_append hprefix tailTrace_1764917
  have hstable : (prefixWord ++ tailWord_1764917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764917).length < 2 ^ (prefixWord ++ tailWord_1764917).sum := by decide
  have hdescent : baseEnd_1764917 < baseStart_1764917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764928 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 8]
def baseStart_1764928 : Nat := 118140960795 + 1764928 * 2 ^ 59
def prefixEnd_1764928 : Nat := 4983230072969 + 3 ^ 40 * 1764928 * 2
def baseEnd_1764928 : Nat := 201390307684127987729611

theorem tailTrace_1764928 : CollatzResearch.WordTrace tailWord_1764928 prefixEnd_1764928 201390307684127987729611 := by
  unfold tailWord_1764928
  simp only [CollatzResearch.WordTrace]
  refine ⟨32186106274987378274891719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42914808366649837699855625 32186106274987378274891719)
  ·
    refine ⟨48279159412481067412337579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32186106274987378274891719 48279159412481067412337579)
    ·
      refine ⟨72418739118721601118506369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48279159412481067412337579 72418739118721601118506369)
      ·
        refine ⟨54314054339041200838879777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72418739118721601118506369 54314054339041200838879777)
        ·
          refine ⟨40735540754280900629159833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54314054339041200838879777 40735540754280900629159833)
          ·
            refine ⟨30551655565710675471869875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40735540754280900629159833 30551655565710675471869875)
            ·
              refine ⟨45827483348566013207804813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30551655565710675471869875 45827483348566013207804813)
              ·
                refine ⟨17185306255712254952926805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45827483348566013207804813 17185306255712254952926805)
                ·
                  refine ⟨201390307684127987729611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17185306255712254952926805 201390307684127987729611)
                  ·
                    rfl

theorem cell22_1764928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 8].length) (baseStart_1764928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1764928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1764928 prefixEnd_1764928 := by exact prefixLift 1764928
  have htrace : WordTrace (prefixWord ++ tailWord_1764928) baseStart_1764928 baseEnd_1764928 := by
    simpa [prefixWord, tailWord_1764928, baseEnd_1764928] using wordTrace_append hprefix tailTrace_1764928
  have hstable : (prefixWord ++ tailWord_1764928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764928).length < 2 ^ (prefixWord ++ tailWord_1764928).sum := by decide
  have hdescent : baseEnd_1764928 < baseStart_1764928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765058 : List Nat := [3, 5, 1, 2, 2, 1, 8]
def baseStart_1765058 : Nat := 118140960795 + 1765058 * 2 ^ 59
def prefixEnd_1765058 : Nat := 4983230072969 + 3 ^ 40 * 1765058 * 2
def baseEnd_1765058 : Nat := 22378349063300257682905

theorem tailTrace_1765058 : CollatzResearch.WordTrace tailWord_1765058 prefixEnd_1765058 22378349063300257682905 := by
  unfold tailWord_1765058
  simp only [CollatzResearch.WordTrace]
  refine ⟨16094238509875947188003957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42917969359669192501343885 16094238509875947188003957)
  ·
    refine ⟨1508834860300870048875371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16094238509875947188003957 1508834860300870048875371)
    ·
      refine ⟨2263252290451305073313057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1508834860300870048875371 2263252290451305073313057)
      ·
        refine ⟨1697439217838478804984793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2263252290451305073313057 1697439217838478804984793)
        ·
          refine ⟨1273079413378859103738595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1697439217838478804984793 1273079413378859103738595)
          ·
            refine ⟨1909619120068288655607893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273079413378859103738595 1909619120068288655607893)
            ·
              refine ⟨22378349063300257682905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1909619120068288655607893 22378349063300257682905)
              ·
                rfl

theorem cell22_1765058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 8].length) (baseStart_1765058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765058 prefixEnd_1765058 := by exact prefixLift 1765058
  have htrace : WordTrace (prefixWord ++ tailWord_1765058) baseStart_1765058 baseEnd_1765058 := by
    simpa [prefixWord, tailWord_1765058, baseEnd_1765058] using wordTrace_append hprefix tailTrace_1765058
  have hstable : (prefixWord ++ tailWord_1765058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765058).length < 2 ^ (prefixWord ++ tailWord_1765058).sum := by decide
  have hdescent : baseEnd_1765058 < baseStart_1765058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765069 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 7]
def baseStart_1765069 : Nat := 118140960795 + 1765069 * 2 ^ 59
def prefixEnd_1765069 : Nat := 4983230072969 + 3 ^ 40 * 1765069 * 2
def baseEnd_1765069 : Nat := 201406396744635531804467

theorem tailTrace_1765069 : CollatzResearch.WordTrace tailWord_1765069 prefixEnd_1765069 201406396744635531804467 := by
  unfold tailWord_1765069
  simp only [CollatzResearch.WordTrace]
  refine ⟨64377355242463937630666261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42918236828309291753777507 64377355242463937630666261)
  ·
    refine ⟨3017688526990497076437481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 64377355242463937630666261 3017688526990497076437481)
    ·
      refine ⟨2263266395242872807328111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3017688526990497076437481 2263266395242872807328111)
      ·
        refine ⟨3394899592864309210992167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2263266395242872807328111 3394899592864309210992167)
        ·
          refine ⟨5092349389296463816488251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3394899592864309210992167 5092349389296463816488251)
          ·
            refine ⟨7638524083944695724732377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5092349389296463816488251 7638524083944695724732377)
            ·
              refine ⟨5728893062958521793549283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7638524083944695724732377 5728893062958521793549283)
              ·
                refine ⟨8593339594437782690323925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5728893062958521793549283 8593339594437782690323925)
                ·
                  refine ⟨201406396744635531804467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8593339594437782690323925 201406396744635531804467)
                  ·
                    rfl

theorem cell22_1765069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_1765069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765069 prefixEnd_1765069 := by exact prefixLift 1765069
  have htrace : WordTrace (prefixWord ++ tailWord_1765069) baseStart_1765069 baseEnd_1765069 := by
    simpa [prefixWord, tailWord_1765069, baseEnd_1765069] using wordTrace_append hprefix tailTrace_1765069
  have hstable : (prefixWord ++ tailWord_1765069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765069).length < 2 ^ (prefixWord ++ tailWord_1765069).sum := by decide
  have hdescent : baseEnd_1765069 < baseStart_1765069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765112 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 4, 3]
def baseStart_1765112 : Nat := 118140960795 + 1765112 * 2 ^ 59
def prefixEnd_1765112 : Nat := 4983230072969 + 3 ^ 40 * 1765112 * 2
def baseEnd_1765112 : Nat := 604233910012668816588269

theorem tailTrace_1765112 : CollatzResearch.WordTrace tailWord_1765112 prefixEnd_1765112 604233910012668816588269 := by
  unfold tailWord_1765112
  simp only [CollatzResearch.WordTrace]
  refine ⟨32189461790654077987240795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42919282387538770649654393 32189461790654077987240795)
  ·
    refine ⟨48284192685981116980861193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32189461790654077987240795 48284192685981116980861193)
    ·
      refine ⟨36213144514485837735645895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48284192685981116980861193 36213144514485837735645895)
      ·
        refine ⟨54319716771728756603468843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36213144514485837735645895 54319716771728756603468843)
        ·
          refine ⟨81479575157593134905203265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54319716771728756603468843 81479575157593134905203265)
          ·
            refine ⟨61109681368194851178902449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81479575157593134905203265 61109681368194851178902449)
            ·
              refine ⟨45832261026146138384176837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61109681368194851178902449 45832261026146138384176837)
              ·
                refine ⟨8593548942402400947033157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45832261026146138384176837 8593548942402400947033157)
                ·
                  refine ⟨1611290426700450177568717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8593548942402400947033157 1611290426700450177568717)
                  ·
                    refine ⟨604233910012668816588269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1611290426700450177568717 604233910012668816588269)
                    ·
                      rfl

theorem cell22_1765112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 4, 3].length) (baseStart_1765112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765112 prefixEnd_1765112 := by exact prefixLift 1765112
  have htrace : WordTrace (prefixWord ++ tailWord_1765112) baseStart_1765112 baseEnd_1765112 := by
    simpa [prefixWord, tailWord_1765112, baseEnd_1765112] using wordTrace_append hprefix tailTrace_1765112
  have hstable : (prefixWord ++ tailWord_1765112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765112).length < 2 ^ (prefixWord ++ tailWord_1765112).sum := by decide
  have hdescent : baseEnd_1765112 < baseStart_1765112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765187 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 7]
def baseStart_1765187 : Nat := 118140960795 + 1765187 * 2 ^ 59
def prefixEnd_1765187 : Nat := 4983230072969 + 3 ^ 40 * 1765187 * 2
def baseEnd_1765187 : Nat := 201419861348464540321013

theorem tailTrace_1765187 : CollatzResearch.WordTrace tailWord_1765187 prefixEnd_1765187 201419861348464540321013 := by
  unfold tailWord_1765187
  simp only [CollatzResearch.WordTrace]
  refine ⟨64381659056036443783461815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42921106037357629188974543 64381659056036443783461815)
  ·
    refine ⟨96572488584054665675192723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64381659056036443783461815 96572488584054665675192723)
    ·
      refine ⟨144858732876081998512789085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96572488584054665675192723 144858732876081998512789085)
      ·
        refine ⟨54322024828530749442295907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144858732876081998512789085 54322024828530749442295907)
        ·
          refine ⟨81483037242796124163443861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54322024828530749442295907 81483037242796124163443861)
          ·
            refine ⟨3819517370756068320161431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81483037242796124163443861 3819517370756068320161431)
            ·
              refine ⟨5729276056134102480242147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3819517370756068320161431 5729276056134102480242147)
              ·
                refine ⟨8593914084201153720363221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5729276056134102480242147 8593914084201153720363221)
                ·
                  refine ⟨201419861348464540321013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8593914084201153720363221 201419861348464540321013)
                  ·
                    rfl

theorem cell22_1765187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 7].length) (baseStart_1765187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765187 prefixEnd_1765187 := by exact prefixLift 1765187
  have htrace : WordTrace (prefixWord ++ tailWord_1765187) baseStart_1765187 baseEnd_1765187 := by
    simpa [prefixWord, tailWord_1765187, baseEnd_1765187] using wordTrace_append hprefix tailTrace_1765187
  have hstable : (prefixWord ++ tailWord_1765187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765187).length < 2 ^ (prefixWord ++ tailWord_1765187).sum := by decide
  have hdescent : baseEnd_1765187 < baseStart_1765187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765191 : List Nat := [1, 1, 4, 1, 2, 1, 4, 4, 1, 3]
def baseStart_1765191 : Nat := 118140960795 + 1765191 * 2 ^ 59
def prefixEnd_1765191 : Nat := 4983230072969 + 3 ^ 40 * 1765191 * 2
def baseEnd_1765191 : Nat := 604260953327138943863027

theorem tailTrace_1765191 : CollatzResearch.WordTrace tailWord_1765191 prefixEnd_1765191 604260953327138943863027 := by
  unfold tailWord_1765191
  simp only [CollatzResearch.WordTrace]
  refine ⟨64381804948021952466607427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42921203298681301644404951 64381804948021952466607427)
  ·
    refine ⟨96572707422032928699911141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64381804948021952466607427 96572707422032928699911141)
    ·
      refine ⟨18107382641631174131233339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96572707422032928699911141 18107382641631174131233339)
      ·
        refine ⟨27161073962446761196850009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18107382641631174131233339 27161073962446761196850009)
        ·
          refine ⟨20370805471835070897637507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27161073962446761196850009 20370805471835070897637507)
          ·
            refine ⟨30556208207752606346456261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20370805471835070897637507 30556208207752606346456261)
            ·
              refine ⟨5729289038953613689960549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30556208207752606346456261 5729289038953613689960549)
              ·
                refine ⟨1074241694803802566867603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5729289038953613689960549 1074241694803802566867603)
                ·
                  refine ⟨1611362542205703850301405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1074241694803802566867603 1611362542205703850301405)
                  ·
                    refine ⟨604260953327138943863027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1611362542205703850301405 604260953327138943863027)
                    ·
                      rfl

theorem cell22_1765191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_1765191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765191 prefixEnd_1765191 := by exact prefixLift 1765191
  have htrace : WordTrace (prefixWord ++ tailWord_1765191) baseStart_1765191 baseEnd_1765191 := by
    simpa [prefixWord, tailWord_1765191, baseEnd_1765191] using wordTrace_append hprefix tailTrace_1765191
  have hstable : (prefixWord ++ tailWord_1765191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765191).length < 2 ^ (prefixWord ++ tailWord_1765191).sum := by decide
  have hdescent : baseEnd_1765191 < baseStart_1765191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765268 : List Nat := [2, 4, 2, 1, 1, 4, 1, 2, 1, 4]
def baseStart_1765268 : Nat := 118140960795 + 1765268 * 2 ^ 59
def prefixEnd_1765268 : Nat := 4983230072969 + 3 ^ 40 * 1765268 * 2
def baseEnd_1765268 : Nat := 604287312000736409687791

theorem tailTrace_1765268 : CollatzResearch.WordTrace tailWord_1765268 prefixEnd_1765268 604287312000736409687791 := by
  unfold tailWord_1765268
  simp only [CollatzResearch.WordTrace]
  refine ⟨32192306684371497308580229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42923075579161996411440305 32192306684371497308580229)
  ·
    refine ⟨6036057503319655745358793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32192306684371497308580229 6036057503319655745358793)
    ·
      refine ⟨4527043127489741809019095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6036057503319655745358793 4527043127489741809019095)
      ·
        refine ⟨6790564691234612713528643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4527043127489741809019095 6790564691234612713528643)
        ·
          refine ⟨10185847036851919070292965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6790564691234612713528643 10185847036851919070292965)
          ·
            refine ⟨1909846319409734825679931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10185847036851919070292965 1909846319409734825679931)
            ·
              refine ⟨2864769479114602238519897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1909846319409734825679931 2864769479114602238519897)
              ·
                refine ⟨2148577109335951678889923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2864769479114602238519897 2148577109335951678889923)
                ·
                  refine ⟨3222865664003927518334885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2148577109335951678889923 3222865664003927518334885)
                  ·
                    refine ⟨604287312000736409687791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3222865664003927518334885 604287312000736409687791)
                    ·
                      rfl

theorem cell22_1765268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_1765268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765268 prefixEnd_1765268 := by exact prefixLift 1765268
  have htrace : WordTrace (prefixWord ++ tailWord_1765268) baseStart_1765268 baseEnd_1765268 := by
    simpa [prefixWord, tailWord_1765268, baseEnd_1765268] using wordTrace_append hprefix tailTrace_1765268
  have hstable : (prefixWord ++ tailWord_1765268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765268).length < 2 ^ (prefixWord ++ tailWord_1765268).sum := by decide
  have hdescent : baseEnd_1765268 < baseStart_1765268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765281 : List Nat := [1, 2, 3, 4, 2, 1, 1, 2, 1, 5]
def baseStart_1765281 : Nat := 118140960795 + 1765281 * 2 ^ 59
def prefixEnd_1765281 : Nat := 4983230072969 + 3 ^ 40 * 1765281 * 2
def baseEnd_1765281 : Nat := 604291762166408709112751

theorem tailTrace_1765281 : CollatzResearch.WordTrace tailWord_1765281 prefixEnd_1765281 604291762166408709112751 := by
  unfold tailWord_1765281
  simp only [CollatzResearch.WordTrace]
  refine ⟨64385087517695897837383697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42923391678463931891589131 64385087517695897837383697)
  ·
    refine ⟨48288815638271923378037773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64385087517695897837383697 48288815638271923378037773)
    ·
      refine ⟨18108305864351971266764165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48288815638271923378037773 18108305864351971266764165)
      ·
        refine ⟨3395307349565994612518281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18108305864351971266764165 3395307349565994612518281)
        ·
          refine ⟨2546480512174495959388711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3395307349565994612518281 2546480512174495959388711)
          ·
            refine ⟨3819720768261743939083067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2546480512174495959388711 3819720768261743939083067)
            ·
              refine ⟨5729581152392615908624601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3819720768261743939083067 5729581152392615908624601)
              ·
                refine ⟨4297185864294461931468451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5729581152392615908624601 4297185864294461931468451)
                ·
                  refine ⟨6445778796441692897202677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4297185864294461931468451 6445778796441692897202677)
                  ·
                    refine ⟨604291762166408709112751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6445778796441692897202677 604291762166408709112751)
                    ·
                      rfl

theorem cell22_1765281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_1765281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765281 prefixEnd_1765281 := by exact prefixLift 1765281
  have htrace : WordTrace (prefixWord ++ tailWord_1765281) baseStart_1765281 baseEnd_1765281 := by
    simpa [prefixWord, tailWord_1765281, baseEnd_1765281] using wordTrace_append hprefix tailTrace_1765281
  have hstable : (prefixWord ++ tailWord_1765281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765281).length < 2 ^ (prefixWord ++ tailWord_1765281).sum := by decide
  have hdescent : baseEnd_1765281 < baseStart_1765281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765300 : List Nat := [2, 5, 2, 1, 2, 1, 1, 4, 4]
def baseStart_1765300 : Nat := 118140960795 + 1765300 * 2 ^ 59
def prefixEnd_1765300 : Nat := 4983230072969 + 3 ^ 40 * 1765300 * 2
def baseEnd_1765300 : Nat := 201432755418232997629231

theorem tailTrace_1765300 : CollatzResearch.WordTrace tailWord_1765300 prefixEnd_1765300 201432755418232997629231 := by
  unfold tailWord_1765300
  simp only [CollatzResearch.WordTrace]
  refine ⟨32192890252313532041162677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42923853669751376054883569 32192890252313532041162677)
  ·
    refine ⟨3018083461154393628859001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32192890252313532041162677 3018083461154393628859001)
    ·
      refine ⟨2263562595865795221644251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3018083461154393628859001 2263562595865795221644251)
      ·
        refine ⟨3395343893798692832466377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2263562595865795221644251 3395343893798692832466377)
        ·
          refine ⟨2546507920349019624349783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3395343893798692832466377 2546507920349019624349783)
          ·
            refine ⟨3819761880523529436524675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2546507920349019624349783 3819761880523529436524675)
            ·
              refine ⟨5729642820785294154787013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3819761880523529436524675 5729642820785294154787013)
              ·
                refine ⟨1074308028897242654022565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5729642820785294154787013 1074308028897242654022565)
                ·
                  refine ⟨201432755418232997629231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1074308028897242654022565 201432755418232997629231)
                  ·
                    rfl

theorem cell22_1765300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_1765300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765300 prefixEnd_1765300 := by exact prefixLift 1765300
  have htrace : WordTrace (prefixWord ++ tailWord_1765300) baseStart_1765300 baseEnd_1765300 := by
    simpa [prefixWord, tailWord_1765300, baseEnd_1765300] using wordTrace_append hprefix tailTrace_1765300
  have hstable : (prefixWord ++ tailWord_1765300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765300).length < 2 ^ (prefixWord ++ tailWord_1765300).sum := by decide
  have hdescent : baseEnd_1765300 < baseStart_1765300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765307 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 2, 6]
def baseStart_1765307 : Nat := 118140960795 + 1765307 * 2 ^ 59
def prefixEnd_1765307 : Nat := 4983230072969 + 3 ^ 40 * 1765307 * 2
def baseEnd_1765307 : Nat := 604300662497753307962671

theorem tailTrace_1765307 : CollatzResearch.WordTrace tailWord_1765307 prefixEnd_1765307 604300662497753307962671 := by
  unfold tailWord_1765307
  simp only [CollatzResearch.WordTrace]
  refine ⟨64386035815601704277830175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42924023877067802851886783 64386035815601704277830175)
  ·
    refine ⟨96579053723402556416745263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64386035815601704277830175 96579053723402556416745263)
    ·
      refine ⟨144868580585103834625117895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96579053723402556416745263 144868580585103834625117895)
      ·
        refine ⟨217302870877655751937676843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144868580585103834625117895 217302870877655751937676843)
        ·
          refine ⟨325954306316483627906515265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217302870877655751937676843 325954306316483627906515265)
          ·
            refine ⟨244465729737362720929886449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325954306316483627906515265 244465729737362720929886449)
            ·
              refine ⟨183349297303022040697414837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244465729737362720929886449 183349297303022040697414837)
              ·
                refine ⟨17188996622158316315382641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 183349297303022040697414837 17188996622158316315382641)
                ·
                  refine ⟨12891747466618737236536981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17188996622158316315382641 12891747466618737236536981)
                  ·
                    refine ⟨604300662497753307962671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12891747466618737236536981 604300662497753307962671)
                    ·
                      rfl

theorem cell22_1765307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 6].length) (baseStart_1765307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765307 prefixEnd_1765307 := by exact prefixLift 1765307
  have htrace : WordTrace (prefixWord ++ tailWord_1765307) baseStart_1765307 baseEnd_1765307 := by
    simpa [prefixWord, tailWord_1765307, baseEnd_1765307] using wordTrace_append hprefix tailTrace_1765307
  have hstable : (prefixWord ++ tailWord_1765307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765307).length < 2 ^ (prefixWord ++ tailWord_1765307).sum := by decide
  have hdescent : baseEnd_1765307 < baseStart_1765307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765326 : List Nat := [4, 1, 1, 1, 2, 2, 3, 2, 3, 3]
def baseStart_1765326 : Nat := 118140960795 + 1765326 * 2 ^ 59
def prefixEnd_1765326 : Nat := 4983230072969 + 3 ^ 40 * 1765326 * 2
def baseEnd_1765326 : Nat := 604307166586043591737613

theorem tailTrace_1765326 : CollatzResearch.WordTrace tailWord_1765326 prefixEnd_1765326 604307166586043591737613 := by
  unfold tailWord_1765326
  simp only [CollatzResearch.WordTrace]
  refine ⟨8048341100316608815346479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42924485868355247015181221 8048341100316608815346479)
  ·
    refine ⟨12072511650474913223019719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8048341100316608815346479 12072511650474913223019719)
    ·
      refine ⟨18108767475712369834529579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12072511650474913223019719 18108767475712369834529579)
      ·
        refine ⟨27163151213568554751794369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18108767475712369834529579 27163151213568554751794369)
        ·
          refine ⟨20372363410176416063845777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27163151213568554751794369 20372363410176416063845777)
          ·
            refine ⟨15279272557632312047884333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20372363410176416063845777 15279272557632312047884333)
            ·
              refine ⟨5729727209112117017956625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15279272557632312047884333 5729727209112117017956625)
              ·
                refine ⟨4297295406834087763467469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5729727209112117017956625 4297295406834087763467469)
                ·
                  refine ⟨1611485777562782911300301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4297295406834087763467469 1611485777562782911300301)
                  ·
                    refine ⟨604307166586043591737613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1611485777562782911300301 604307166586043591737613)
                    ·
                      rfl

theorem cell22_1765326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_1765326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765326 prefixEnd_1765326 := by exact prefixLift 1765326
  have htrace : WordTrace (prefixWord ++ tailWord_1765326) baseStart_1765326 baseEnd_1765326 := by
    simpa [prefixWord, tailWord_1765326, baseEnd_1765326] using wordTrace_append hprefix tailTrace_1765326
  have hstable : (prefixWord ++ tailWord_1765326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765326).length < 2 ^ (prefixWord ++ tailWord_1765326).sum := by decide
  have hdescent : baseEnd_1765326 < baseStart_1765326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765330 : List Nat := [3, 2, 2, 3, 3, 1, 1, 1, 2, 4]
def baseStart_1765330 : Nat := 118140960795 + 1765330 * 2 ^ 59
def prefixEnd_1765330 : Nat := 4983230072969 + 3 ^ 40 * 1765330 * 2
def baseEnd_1765330 : Nat := 604308535867788914637601

theorem tailTrace_1765330 : CollatzResearch.WordTrace tailWord_1765330 prefixEnd_1765330 604308535867788914637601 := by
  unfold tailWord_1765330
  simp only [CollatzResearch.WordTrace]
  refine ⟨16096718673629594801479361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42924583129678919470611629 16096718673629594801479361)
  ·
    refine ⟨12072539005222196101109521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16096718673629594801479361 12072539005222196101109521)
    ·
      refine ⟨9054404253916647075832141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12072539005222196101109521 9054404253916647075832141)
      ·
        refine ⟨3395401595218742653437053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9054404253916647075832141 3395401595218742653437053)
        ·
          refine ⟨1273275598207028495038895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3395401595218742653437053 1273275598207028495038895)
          ·
            refine ⟨1909913397310542742558343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273275598207028495038895 1909913397310542742558343)
            ·
              refine ⟨2864870095965814113837515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1909913397310542742558343 2864870095965814113837515)
              ·
                refine ⟨4297305143948721170756273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2864870095965814113837515 4297305143948721170756273)
                ·
                  refine ⟨3222978857961540878067205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4297305143948721170756273 3222978857961540878067205)
                  ·
                    refine ⟨604308535867788914637601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3222978857961540878067205 604308535867788914637601)
                    ·
                      rfl

theorem cell22_1765330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_1765330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765330 prefixEnd_1765330 := by exact prefixLift 1765330
  have htrace : WordTrace (prefixWord ++ tailWord_1765330) baseStart_1765330 baseEnd_1765330 := by
    simpa [prefixWord, tailWord_1765330, baseEnd_1765330] using wordTrace_append hprefix tailTrace_1765330
  have hstable : (prefixWord ++ tailWord_1765330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765330).length < 2 ^ (prefixWord ++ tailWord_1765330).sum := by decide
  have hdescent : baseEnd_1765330 < baseStart_1765330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765343 : List Nat := [1, 1, 2, 3, 4, 1, 1, 5, 1, 3]
def baseStart_1765343 : Nat := 118140960795 + 1765343 * 2 ^ 59
def prefixEnd_1765343 : Nat := 4983230072969 + 3 ^ 40 * 1765343 * 2
def baseEnd_1765343 : Nat := 604312986033461214062561

theorem tailTrace_1765343 : CollatzResearch.WordTrace tailWord_1765343 prefixEnd_1765343 604312986033461214062561 := by
  unfold tailWord_1765343
  simp only [CollatzResearch.WordTrace]
  refine ⟨64387348843471282426140683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42924899228980854950760455 64387348843471282426140683)
  ·
    refine ⟨96581023265206923639211025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64387348843471282426140683 96581023265206923639211025)
    ·
      refine ⟨72435767448905192729408269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96581023265206923639211025 72435767448905192729408269)
      ·
        refine ⟨27163412793339447273528101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72435767448905192729408269 27163412793339447273528101)
        ·
          refine ⟨5093139898751146363786519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27163412793339447273528101 5093139898751146363786519)
          ·
            refine ⟨7639709848126719545679779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5093139898751146363786519 7639709848126719545679779)
            ·
              refine ⟨11459564772190079318519669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7639709848126719545679779 11459564772190079318519669)
              ·
                refine ⟨1074334197392819936111219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11459564772190079318519669 1074334197392819936111219)
                ·
                  refine ⟨1611501296089229904166829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1074334197392819936111219 1611501296089229904166829)
                  ·
                    refine ⟨604312986033461214062561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1611501296089229904166829 604312986033461214062561)
                    ·
                      rfl

theorem cell22_1765343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 1, 3].length) (baseStart_1765343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765343 prefixEnd_1765343 := by exact prefixLift 1765343
  have htrace : WordTrace (prefixWord ++ tailWord_1765343) baseStart_1765343 baseEnd_1765343 := by
    simpa [prefixWord, tailWord_1765343, baseEnd_1765343] using wordTrace_append hprefix tailTrace_1765343
  have hstable : (prefixWord ++ tailWord_1765343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765343).length < 2 ^ (prefixWord ++ tailWord_1765343).sum := by decide
  have hdescent : baseEnd_1765343 < baseStart_1765343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765354 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 4, 5]
def baseStart_1765354 : Nat := 118140960795 + 1765354 * 2 ^ 59
def prefixEnd_1765354 : Nat := 4983230072969 + 3 ^ 40 * 1765354 * 2
def baseEnd_1765354 : Nat := 604316751558260852037527

theorem tailTrace_1765354 : CollatzResearch.WordTrace tailWord_1765354 prefixEnd_1765354 604316751558260852037527 := by
  unfold tailWord_1765354
  simp only [CollatzResearch.WordTrace]
  refine ⟨16096937511607857826197779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42925166697620954203194077 16096937511607857826197779)
  ·
    refine ⟨24145406267411786739296669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16096937511607857826197779 24145406267411786739296669)
    ·
      refine ⟨9054527350279420027236251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24145406267411786739296669 9054527350279420027236251)
      ·
        refine ⟨13581791025419130040854377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9054527350279420027236251 13581791025419130040854377)
        ·
          refine ⟨10186343269064347530640783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13581791025419130040854377 10186343269064347530640783)
          ·
            refine ⟨15279514903596521295961175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10186343269064347530640783 15279514903596521295961175)
            ·
              refine ⟨22919272355394781943941763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15279514903596521295961175 22919272355394781943941763)
              ·
                refine ⟨34378908533092172915912645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22919272355394781943941763 34378908533092172915912645)
                ·
                  refine ⟨6446045349954782421733621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34378908533092172915912645 6446045349954782421733621)
                  ·
                    refine ⟨604316751558260852037527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6446045349954782421733621 604316751558260852037527)
                    ·
                      rfl

theorem cell22_1765354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_1765354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765354 prefixEnd_1765354 := by exact prefixLift 1765354
  have htrace : WordTrace (prefixWord ++ tailWord_1765354) baseStart_1765354 baseEnd_1765354 := by
    simpa [prefixWord, tailWord_1765354, baseEnd_1765354] using wordTrace_append hprefix tailTrace_1765354
  have hstable : (prefixWord ++ tailWord_1765354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765354).length < 2 ^ (prefixWord ++ tailWord_1765354).sum := by decide
  have hdescent : baseEnd_1765354 < baseStart_1765354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765384 : List Nat := [2, 1, 3, 2, 1, 2, 1, 4, 6]
def baseStart_1765384 : Nat := 118140960795 + 1765384 * 2 ^ 59
def prefixEnd_1765384 : Nat := 4983230072969 + 3 ^ 40 * 1765384 * 2
def baseEnd_1765384 : Nat := 201442340390450257929145

theorem tailTrace_1765384 : CollatzResearch.WordTrace tailWord_1765384 prefixEnd_1765384 201442340390450257929145 := by
  unfold tailWord_1765384
  simp only [CollatzResearch.WordTrace]
  refine ⟨32194422118161373214191603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42925896157548497618922137 32194422118161373214191603)
  ·
    refine ⟨48291633177242059821287405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32194422118161373214191603 48291633177242059821287405)
    ·
      refine ⟨18109362441465772432982777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48291633177242059821287405 18109362441465772432982777)
      ·
        refine ⟨13582021831099329324737083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18109362441465772432982777 13582021831099329324737083)
        ·
          refine ⟨20373032746648993987105625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13582021831099329324737083 20373032746648993987105625)
          ·
            refine ⟨15279774559986745490329219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20373032746648993987105625 15279774559986745490329219)
            ·
              refine ⟨22919661839980118235493829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15279774559986745490329219 22919661839980118235493829)
              ·
                refine ⟨4297436594996272169155093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22919661839980118235493829 4297436594996272169155093)
                ·
                  refine ⟨201442340390450257929145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4297436594996272169155093 201442340390450257929145)
                  ·
                    rfl

theorem cell22_1765384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 6].length) (baseStart_1765384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765384 prefixEnd_1765384 := by exact prefixLift 1765384
  have htrace : WordTrace (prefixWord ++ tailWord_1765384) baseStart_1765384 baseEnd_1765384 := by
    simpa [prefixWord, tailWord_1765384, baseEnd_1765384] using wordTrace_append hprefix tailTrace_1765384
  have hstable : (prefixWord ++ tailWord_1765384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765384).length < 2 ^ (prefixWord ++ tailWord_1765384).sum := by decide
  have hdescent : baseEnd_1765384 < baseStart_1765384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765418 : List Nat := [3, 1, 4, 1, 2, 3, 1, 1, 6]
def baseStart_1765418 : Nat := 118140960795 + 1765418 * 2 ^ 59
def prefixEnd_1765418 : Nat := 4983230072969 + 3 ^ 40 * 1765418 * 2
def baseEnd_1765418 : Nat := 201446220022062006145777

theorem tailTrace_1765418 : CollatzResearch.WordTrace tailWord_1765418 prefixEnd_1765418 201446220022062006145777 := by
  unfold tailWord_1765418
  simp only [CollatzResearch.WordTrace]
  refine ⟨16097521079549892558780227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42926722878799713490080605 16097521079549892558780227)
  ·
    refine ⟨24146281619324838838170341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16097521079549892558780227 24146281619324838838170341)
    ·
      refine ⟨4527427803623407282156939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24146281619324838838170341 4527427803623407282156939)
      ·
        refine ⟨6791141705435110923235409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4527427803623407282156939 6791141705435110923235409)
        ·
          refine ⟨5093356279076333192426557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6791141705435110923235409 5093356279076333192426557)
          ·
            refine ⟨1910008604653624947159959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5093356279076333192426557 1910008604653624947159959)
            ·
              refine ⟨2865012906980437420739939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1910008604653624947159959 2865012906980437420739939)
              ·
                refine ⟨4297519360470656131109909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2865012906980437420739939 4297519360470656131109909)
                ·
                  refine ⟨201446220022062006145777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4297519360470656131109909 201446220022062006145777)
                  ·
                    rfl

theorem cell22_1765418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 6].length) (baseStart_1765418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765418 prefixEnd_1765418 := by exact prefixLift 1765418
  have htrace : WordTrace (prefixWord ++ tailWord_1765418) baseStart_1765418 baseEnd_1765418 := by
    simpa [prefixWord, tailWord_1765418, baseEnd_1765418] using wordTrace_append hprefix tailTrace_1765418
  have hstable : (prefixWord ++ tailWord_1765418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765418).length < 2 ^ (prefixWord ++ tailWord_1765418).sum := by decide
  have hdescent : baseEnd_1765418 < baseStart_1765418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765429 : List Nat := [1, 3, 3, 1, 1, 1, 3, 9]
def baseStart_1765429 : Nat := 118140960795 + 1765429 * 2 ^ 59
def prefixEnd_1765429 : Nat := 4983230072969 + 3 ^ 40 * 1765429 * 2
def baseEnd_1765429 : Nat := 67149158398998406268033

theorem tailTrace_1765429 : CollatzResearch.WordTrace tailWord_1765429 prefixEnd_1765429 67149158398998406268033 := by
  unfold tailWord_1765429
  simp only [CollatzResearch.WordTrace]
  refine ⟨64390485521159719113771341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42926990347439812742514227 64390485521159719113771341)
  ·
    refine ⟨24146432070434894667664253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64390485521159719113771341 24146432070434894667664253)
    ·
      refine ⟨9054912026413085500374095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24146432070434894667664253 9054912026413085500374095)
      ·
        refine ⟨13582368039619628250561143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9054912026413085500374095 13582368039619628250561143)
        ·
          refine ⟨20373552059429442375841715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13582368039619628250561143 20373552059429442375841715)
          ·
            refine ⟨30560328089144163563762573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20373552059429442375841715 30560328089144163563762573)
            ·
              refine ⟨11460123033429061336410965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30560328089144163563762573 11460123033429061336410965)
              ·
                refine ⟨67149158398998406268033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11460123033429061336410965 67149158398998406268033)
                ·
                  rfl

theorem cell22_1765429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 9].length) (baseStart_1765429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765429 prefixEnd_1765429 := by exact prefixLift 1765429
  have htrace : WordTrace (prefixWord ++ tailWord_1765429) baseStart_1765429 baseEnd_1765429 := by
    simpa [prefixWord, tailWord_1765429, baseEnd_1765429] using wordTrace_append hprefix tailTrace_1765429
  have hstable : (prefixWord ++ tailWord_1765429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765429).length < 2 ^ (prefixWord ++ tailWord_1765429).sum := by decide
  have hdescent : baseEnd_1765429 < baseStart_1765429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765512 : List Nat := [2, 1, 3, 4, 1, 2, 2, 3, 1, 3]
def baseStart_1765512 : Nat := 118140960795 + 1765512 * 2 ^ 59
def prefixEnd_1765512 : Nat := 4983230072969 + 3 ^ 40 * 1765512 * 2
def baseEnd_1765512 : Nat := 604370838187201106587043

theorem tailTrace_1765512 : CollatzResearch.WordTrace tailWord_1765512 prefixEnd_1765512 604370838187201106587043 := by
  unfold tailWord_1765512
  simp only [CollatzResearch.WordTrace]
  refine ⟨32196756389929512144521395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42929008519906016192695193 32196756389929512144521395)
  ·
    refine ⟨48295134584894268216782093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32196756389929512144521395 48295134584894268216782093)
    ·
      refine ⟨18110675469335350581293285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48295134584894268216782093 18110675469335350581293285)
      ·
        refine ⟨3395751650500378233992491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18110675469335350581293285 3395751650500378233992491)
        ·
          refine ⟨5093627475750567350988737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3395751650500378233992491 5093627475750567350988737)
          ·
            refine ⟨3820220606812925513241553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5093627475750567350988737 3820220606812925513241553)
            ·
              refine ⟨2865165455109694134931165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3820220606812925513241553 2865165455109694134931165)
              ·
                refine ⟨1074437045666135300599187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2865165455109694134931165 1074437045666135300599187)
                ·
                  refine ⟨1611655568499202950898781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1074437045666135300599187 1611655568499202950898781)
                  ·
                    refine ⟨604370838187201106587043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1611655568499202950898781 604370838187201106587043)
                    ·
                      rfl

theorem cell22_1765512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_1765512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765512 prefixEnd_1765512 := by exact prefixLift 1765512
  have htrace : WordTrace (prefixWord ++ tailWord_1765512) baseStart_1765512 baseEnd_1765512 := by
    simpa [prefixWord, tailWord_1765512, baseEnd_1765512] using wordTrace_append hprefix tailTrace_1765512
  have hstable : (prefixWord ++ tailWord_1765512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765512).length < 2 ^ (prefixWord ++ tailWord_1765512).sum := by decide
  have hdescent : baseEnd_1765512 < baseStart_1765512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765536 : List Nat := [2, 1, 1, 4, 2, 2, 1, 3, 6]
def baseStart_1765536 : Nat := 118140960795 + 1765536 * 2 ^ 59
def prefixEnd_1765536 : Nat := 4983230072969 + 3 ^ 40 * 1765536 * 2
def baseEnd_1765536 : Nat := 201459684625891014662323

theorem tailTrace_1765536 : CollatzResearch.WordTrace tailWord_1765536 prefixEnd_1765536 201459684625891014662323 := by
  unfold tailWord_1765536
  simp only [CollatzResearch.WordTrace]
  refine ⟨32197194065886038193958231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42929592087848050925277641 32197194065886038193958231)
  ·
    refine ⟨48295791098829057290937347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32197194065886038193958231 48295791098829057290937347)
    ·
      refine ⟨72443686648243585936406021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48295791098829057290937347 72443686648243585936406021)
      ·
        refine ⟨13583191246545672363076129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72443686648243585936406021 13583191246545672363076129)
        ·
          refine ⟨10187393434909254272307097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13583191246545672363076129 10187393434909254272307097)
          ·
            refine ⟨7640545076181940704230323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10187393434909254272307097 7640545076181940704230323)
            ·
              refine ⟨11460817614272911056345485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7640545076181940704230323 11460817614272911056345485)
              ·
                refine ⟨4297806605352341646129557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11460817614272911056345485 4297806605352341646129557)
                ·
                  refine ⟨201459684625891014662323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4297806605352341646129557 201459684625891014662323)
                  ·
                    rfl

theorem cell22_1765536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 6].length) (baseStart_1765536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765536 prefixEnd_1765536 := by exact prefixLift 1765536
  have htrace : WordTrace (prefixWord ++ tailWord_1765536) baseStart_1765536 baseEnd_1765536 := by
    simpa [prefixWord, tailWord_1765536, baseEnd_1765536] using wordTrace_append hprefix tailTrace_1765536
  have hstable : (prefixWord ++ tailWord_1765536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765536).length < 2 ^ (prefixWord ++ tailWord_1765536).sum := by decide
  have hdescent : baseEnd_1765536 < baseStart_1765536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765568 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 4, 3]
def baseStart_1765568 : Nat := 118140960795 + 1765568 * 2 ^ 59
def prefixEnd_1765568 : Nat := 4983230072969 + 3 ^ 40 * 1765568 * 2
def baseEnd_1765568 : Nat := 604390008131635627186871

theorem tailTrace_1765568 : CollatzResearch.WordTrace tailWord_1765568 prefixEnd_1765568 604390008131635627186871 := by
  unfold tailWord_1765568
  simp only [CollatzResearch.WordTrace]
  refine ⟨32197777633828072926540679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42930370178437430568720905 32197777633828072926540679)
  ·
    refine ⟨48296666450742109389811019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32197777633828072926540679 48296666450742109389811019)
    ·
      refine ⟨72444999676113164084716529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48296666450742109389811019 72444999676113164084716529)
      ·
        refine ⟨54333749757084873063537397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72444999676113164084716529 54333749757084873063537397)
        ·
          refine ⟨5093789039726706849706631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54333749757084873063537397 5093789039726706849706631)
          ·
            refine ⟨7640683559590060274559947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5093789039726706849706631 7640683559590060274559947)
            ·
              refine ⟨11461025339385090411839921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7640683559590060274559947 11461025339385090411839921)
              ·
                refine ⟨8595769004538817808879941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11461025339385090411839921 8595769004538817808879941)
                ·
                  refine ⟨1611706688351028339164989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8595769004538817808879941 1611706688351028339164989)
                  ·
                    refine ⟨604390008131635627186871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1611706688351028339164989 604390008131635627186871)
                    ·
                      rfl

theorem cell22_1765568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 4, 3].length) (baseStart_1765568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765568 prefixEnd_1765568 := by exact prefixLift 1765568
  have htrace : WordTrace (prefixWord ++ tailWord_1765568) baseStart_1765568 baseEnd_1765568 := by
    simpa [prefixWord, tailWord_1765568, baseEnd_1765568] using wordTrace_append hprefix tailTrace_1765568
  have hstable : (prefixWord ++ tailWord_1765568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765568).length < 2 ^ (prefixWord ++ tailWord_1765568).sum := by decide
  have hdescent : baseEnd_1765568 < baseStart_1765568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765643 : List Nat := [1, 1, 1, 1, 5, 2, 4, 2, 5]
def baseStart_1765643 : Nat := 118140960795 + 1765643 * 2 ^ 59
def prefixEnd_1765643 : Nat := 4983230072969 + 3 ^ 40 * 1765643 * 2
def baseEnd_1765643 : Nat := 201471894054786810520547

theorem tailTrace_1765643 : CollatzResearch.WordTrace tailWord_1765643 prefixEnd_1765643 201471894054786810520547 := by
  unfold tailWord_1765643
  simp only [CollatzResearch.WordTrace]
  refine ⟨64398290742384433662061583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42932193828256289108041055 64398290742384433662061583)
  ·
    refine ⟨96597436113576650493092375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64398290742384433662061583 96597436113576650493092375)
    ·
      refine ⟨144896154170364975739638563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96597436113576650493092375 144896154170364975739638563)
      ·
        refine ⟨217344231255547463609457845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144896154170364975739638563 217344231255547463609457845)
        ·
          refine ⟨20376021680207574713386673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 217344231255547463609457845 20376021680207574713386673)
          ·
            refine ⟨15282016260155681035040005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20376021680207574713386673 15282016260155681035040005)
            ·
              refine ⟨2865378048779190194070001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15282016260155681035040005 2865378048779190194070001)
              ·
                refine ⟨2149033536584392645552501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2865378048779190194070001 2149033536584392645552501)
                ·
                  refine ⟨201471894054786810520547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2149033536584392645552501 201471894054786810520547)
                  ·
                    rfl

theorem cell22_1765643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 5].length) (baseStart_1765643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765643 prefixEnd_1765643 := by exact prefixLift 1765643
  have htrace : WordTrace (prefixWord ++ tailWord_1765643) baseStart_1765643 baseEnd_1765643 := by
    simpa [prefixWord, tailWord_1765643, baseEnd_1765643] using wordTrace_append hprefix tailTrace_1765643
  have hstable : (prefixWord ++ tailWord_1765643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765643).length < 2 ^ (prefixWord ++ tailWord_1765643).sum := by decide
  have hdescent : baseEnd_1765643 < baseStart_1765643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765690 : List Nat := [3, 1, 1, 1, 4, 3, 1, 3, 1, 4]
def baseStart_1765690 : Nat := 118140960795 + 1765690 * 2 ^ 59
def prefixEnd_1765690 : Nat := 4983230072969 + 3 ^ 40 * 1765690 * 2
def baseEnd_1765690 : Nat := 604431771224867975636497

theorem tailTrace_1765690 : CollatzResearch.WordTrace tailWord_1765690 prefixEnd_1765690 604431771224867975636497 := by
  unfold tailWord_1765690
  simp only [CollatzResearch.WordTrace]
  refine ⟨16100001243303540172255631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42933336648809440459348349 16100001243303540172255631)
  ·
    refine ⟨24150001864955310258383447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16100001243303540172255631 24150001864955310258383447)
    ·
      refine ⟨36225002797432965387575171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24150001864955310258383447 36225002797432965387575171)
      ·
        refine ⟨54337504196149448081362757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36225002797432965387575171 54337504196149448081362757)
        ·
          refine ⟨10188282036778021515255517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54337504196149448081362757 10188282036778021515255517)
          ·
            refine ⟨3820605763791758068220819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10188282036778021515255517 3820605763791758068220819)
            ·
              refine ⟨5730908645687637102331229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3820605763791758068220819 5730908645687637102331229)
              ·
                refine ⟨2149090742132863913374211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5730908645687637102331229 2149090742132863913374211)
                ·
                  refine ⟨3223636113199295870061317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2149090742132863913374211 3223636113199295870061317)
                  ·
                    refine ⟨604431771224867975636497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3223636113199295870061317 604431771224867975636497)
                    ·
                      rfl

theorem cell22_1765690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_1765690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765690 prefixEnd_1765690 := by exact prefixLift 1765690
  have htrace : WordTrace (prefixWord ++ tailWord_1765690) baseStart_1765690 baseEnd_1765690 := by
    simpa [prefixWord, tailWord_1765690, baseEnd_1765690] using wordTrace_append hprefix tailTrace_1765690
  have hstable : (prefixWord ++ tailWord_1765690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765690).length < 2 ^ (prefixWord ++ tailWord_1765690).sum := by decide
  have hdescent : baseEnd_1765690 < baseStart_1765690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765724 : List Nat := [2, 2, 4, 3, 1, 1, 2, 2, 1, 4]
def baseStart_1765724 : Nat := 118140960795 + 1765724 * 2 ^ 59
def prefixEnd_1765724 : Nat := 4983230072969 + 3 ^ 40 * 1765724 * 2
def baseEnd_1765724 : Nat := 604443410119703220286393

theorem tailTrace_1765724 : CollatzResearch.WordTrace tailWord_1765724 prefixEnd_1765724 604443410119703220286393 := by
  unfold tailWord_1765724
  simp only [CollatzResearch.WordTrace]
  refine ⟨32200622527545492247880113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42934163370060656330506817 32200622527545492247880113)
  ·
    refine ⟨24150466895659119185910085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32200622527545492247880113 24150466895659119185910085)
    ·
      refine ⟨4528212542936084847358141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24150466895659119185910085 4528212542936084847358141)
      ·
        refine ⟨1698079703601031817759303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4528212542936084847358141 1698079703601031817759303)
        ·
          refine ⟨2547119555401547726638955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1698079703601031817759303 2547119555401547726638955)
          ·
            refine ⟨3820679333102321589958433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2547119555401547726638955 3820679333102321589958433)
            ·
              refine ⟨2865509499826741192468825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3820679333102321589958433 2865509499826741192468825)
              ·
                refine ⟨2149132124870055894351619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2865509499826741192468825 2149132124870055894351619)
                ·
                  refine ⟨3223698187305083841527429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2149132124870055894351619 3223698187305083841527429)
                  ·
                    refine ⟨604443410119703220286393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3223698187305083841527429 604443410119703220286393)
                    ·
                      rfl

theorem cell22_1765724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_1765724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765724 prefixEnd_1765724 := by exact prefixLift 1765724
  have htrace : WordTrace (prefixWord ++ tailWord_1765724) baseStart_1765724 baseEnd_1765724 := by
    simpa [prefixWord, tailWord_1765724, baseEnd_1765724] using wordTrace_append hprefix tailTrace_1765724
  have hstable : (prefixWord ++ tailWord_1765724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765724).length < 2 ^ (prefixWord ++ tailWord_1765724).sum := by decide
  have hdescent : baseEnd_1765724 < baseStart_1765724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765733 : List Nat := [1, 3, 1, 3, 1, 4, 1, 8]
def baseStart_1765733 : Nat := 118140960795 + 1765733 * 2 ^ 59
def prefixEnd_1765733 : Nat := 4983230072969 + 3 ^ 40 * 1765733 * 2
def baseEnd_1765733 : Nat := 67160721222625577423485

theorem tailTrace_1765733 : CollatzResearch.WordTrace tailWord_1765733 prefixEnd_1765733 67160721222625577423485 := by
  unfold tailWord_1765733
  simp only [CollatzResearch.WordTrace]
  refine ⟨64401573312058379032837853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42934382208038919355225235 64401573312058379032837853)
  ·
    refine ⟨24150589992021892137314195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64401573312058379032837853 24150589992021892137314195)
    ·
      refine ⟨36225884988032838205971293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24150589992021892137314195 36225884988032838205971293)
      ·
        refine ⟨13584706870512314327239235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36225884988032838205971293 13584706870512314327239235)
        ·
          refine ⟨20377060305768471490858853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13584706870512314327239235 20377060305768471490858853)
          ·
            refine ⟨3820698807331588404536035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20377060305768471490858853 3820698807331588404536035)
            ·
              refine ⟨5731048210997382606804053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3820698807331588404536035 5731048210997382606804053)
              ·
                refine ⟨67160721222625577423485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5731048210997382606804053 67160721222625577423485)
                ·
                  rfl

theorem cell22_1765733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 8].length) (baseStart_1765733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765733 prefixEnd_1765733 := by exact prefixLift 1765733
  have htrace : WordTrace (prefixWord ++ tailWord_1765733) baseStart_1765733 baseEnd_1765733 := by
    simpa [prefixWord, tailWord_1765733, baseEnd_1765733] using wordTrace_append hprefix tailTrace_1765733
  have hstable : (prefixWord ++ tailWord_1765733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765733).length < 2 ^ (prefixWord ++ tailWord_1765733).sum := by decide
  have hdescent : baseEnd_1765733 < baseStart_1765733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765855 : List Nat := [1, 1, 2, 3, 3, 2, 2, 2, 1, 5]
def baseStart_1765855 : Nat := 118140960795 + 1765855 * 2 ^ 59
def prefixEnd_1765855 : Nat := 4983230072969 + 3 ^ 40 * 1765855 * 2
def baseEnd_1765855 : Nat := 604488254096862545260991

theorem tailTrace_1765855 : CollatzResearch.WordTrace tailWord_1765855 prefixEnd_1765855 604488254096862545260991 := by
  unfold tailWord_1765855
  simp only [CollatzResearch.WordTrace]
  refine ⟨64406023017616393868779019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42937348678410929245852679 64406023017616393868779019)
  ·
    refine ⟨96609034526424590803168529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64406023017616393868779019 96609034526424590803168529)
    ·
      refine ⟨72456775894818443102376397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96609034526424590803168529 72456775894818443102376397)
      ·
        refine ⟨27171290960556916163391149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72456775894818443102376397 27171290960556916163391149)
        ·
          refine ⟨10189234110208843561271681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27171290960556916163391149 10189234110208843561271681)
          ·
            refine ⟨7641925582656632670953761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10189234110208843561271681 7641925582656632670953761)
            ·
              refine ⟨5731444186992474503215321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7641925582656632670953761 5731444186992474503215321)
              ·
                refine ⟨4298583140244355877411491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5731444186992474503215321 4298583140244355877411491)
                ·
                  refine ⟨6447874710366533816117237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4298583140244355877411491 6447874710366533816117237)
                  ·
                    refine ⟨604488254096862545260991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6447874710366533816117237 604488254096862545260991)
                    ·
                      rfl

theorem cell22_1765855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 5].length) (baseStart_1765855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765855 prefixEnd_1765855 := by exact prefixLift 1765855
  have htrace : WordTrace (prefixWord ++ tailWord_1765855) baseStart_1765855 baseEnd_1765855 := by
    simpa [prefixWord, tailWord_1765855, baseEnd_1765855] using wordTrace_append hprefix tailTrace_1765855
  have hstable : (prefixWord ++ tailWord_1765855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765855).length < 2 ^ (prefixWord ++ tailWord_1765855).sum := by decide
  have hdescent : baseEnd_1765855 < baseStart_1765855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765857 : List Nat := [1, 2, 3, 1, 2, 2, 4, 3, 4]
def baseStart_1765857 : Nat := 118140960795 + 1765857 * 2 ^ 59
def prefixEnd_1765857 : Nat := 4983230072969 + 3 ^ 40 * 1765857 * 2
def baseEnd_1765857 : Nat := 201496312912578402236995

theorem tailTrace_1765857 : CollatzResearch.WordTrace tailWord_1765857 prefixEnd_1765857 201496312912578402236995 := by
  unfold tailWord_1765857
  simp only [CollatzResearch.WordTrace]
  refine ⟨64406095963609148210351825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42937397309072765473567883 64406095963609148210351825)
  ·
    refine ⟨48304571972706861157763869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64406095963609148210351825 48304571972706861157763869)
    ·
      refine ⟨18114214489765072934161451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48304571972706861157763869 18114214489765072934161451)
      ·
        refine ⟨27171321734647609401242177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18114214489765072934161451 27171321734647609401242177)
        ·
          refine ⟨20378491300985707050931633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27171321734647609401242177 20378491300985707050931633)
          ·
            refine ⟨15283868475739280288198725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20378491300985707050931633 15283868475739280288198725)
            ·
              refine ⟨2865725339201115054037261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15283868475739280288198725 2865725339201115054037261)
              ·
                refine ⟨1074647002200418145263973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2865725339201115054037261 1074647002200418145263973)
                ·
                  refine ⟨201496312912578402236995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1074647002200418145263973 201496312912578402236995)
                  ·
                    rfl

theorem cell22_1765857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 4].length) (baseStart_1765857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765857 prefixEnd_1765857 := by exact prefixLift 1765857
  have htrace : WordTrace (prefixWord ++ tailWord_1765857) baseStart_1765857 baseEnd_1765857 := by
    simpa [prefixWord, tailWord_1765857, baseEnd_1765857] using wordTrace_append hprefix tailTrace_1765857
  have hstable : (prefixWord ++ tailWord_1765857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765857).length < 2 ^ (prefixWord ++ tailWord_1765857).sum := by decide
  have hdescent : baseEnd_1765857 < baseStart_1765857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765868 : List Nat := [2, 2, 1, 1, 2, 1, 13]
def baseStart_1765868 : Nat := 118140960795 + 1765868 * 2 ^ 59
def prefixEnd_1765868 : Nat := 4983230072969 + 3 ^ 40 * 1765868 * 2
def baseEnd_1765868 : Nat := 22388618676390179432813

theorem tailTrace_1765868 : CollatzResearch.WordTrace tailWord_1765868 prefixEnd_1765868 22388618676390179432813 := by
  unfold tailWord_1765868
  simp only [CollatzResearch.WordTrace]
  refine ⟨32203248583284648544501129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42937664777712864726001505 32203248583284648544501129)
  ·
    refine ⟨24152436437463486408375847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32203248583284648544501129 24152436437463486408375847)
    ·
      refine ⟨36228654656195229612563771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24152436437463486408375847 36228654656195229612563771)
      ·
        refine ⟨54342981984292844418845657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36228654656195229612563771 54342981984292844418845657)
        ·
          refine ⟨40757236488219633314134243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54342981984292844418845657 40757236488219633314134243)
          ·
            refine ⟨61135854732329449971201365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40757236488219633314134243 61135854732329449971201365)
            ·
              refine ⟨22388618676390179432813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 61135854732329449971201365 22388618676390179432813)
              ·
                rfl

theorem cell22_1765868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 13].length) (baseStart_1765868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765868 prefixEnd_1765868 := by exact prefixLift 1765868
  have htrace : WordTrace (prefixWord ++ tailWord_1765868) baseStart_1765868 baseEnd_1765868 := by
    simpa [prefixWord, tailWord_1765868, baseEnd_1765868] using wordTrace_append hprefix tailTrace_1765868
  have hstable : (prefixWord ++ tailWord_1765868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765868).length < 2 ^ (prefixWord ++ tailWord_1765868).sum := by decide
  have hdescent : baseEnd_1765868 < baseStart_1765868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765883 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 4, 7]
def baseStart_1765883 : Nat := 118140960795 + 1765883 * 2 ^ 59
def prefixEnd_1765883 : Nat := 4983230072969 + 3 ^ 40 * 1765883 * 2
def baseEnd_1765883 : Nat := 604497839069079805560905

theorem tailTrace_1765883 : CollatzResearch.WordTrace tailWord_1765883 prefixEnd_1765883 604497839069079805560905 := by
  unfold tailWord_1765883
  simp only [CollatzResearch.WordTrace]
  refine ⟨64407044261514954650798303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42938029507676636433865535 64407044261514954650798303)
  ·
    refine ⟨96610566392272431976197455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64407044261514954650798303 96610566392272431976197455)
    ·
      refine ⟨144915849588408647964296183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96610566392272431976197455 144915849588408647964296183)
      ·
        refine ⟨217373774382612971946444275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144915849588408647964296183 217373774382612971946444275)
        ·
          refine ⟨326060661573919457919666413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217373774382612971946444275 326060661573919457919666413)
          ·
            refine ⟨122272748090219796719874905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326060661573919457919666413 122272748090219796719874905)
            ·
              refine ⟨91704561067664847539906179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122272748090219796719874905 91704561067664847539906179)
              ·
                refine ⟨137556841601497271309859269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91704561067664847539906179 137556841601497271309859269)
                ·
                  refine ⟨25791907800280738370598613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137556841601497271309859269 25791907800280738370598613)
                  ·
                    refine ⟨604497839069079805560905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25791907800280738370598613 604497839069079805560905)
                    ·
                      rfl

theorem cell22_1765883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 7].length) (baseStart_1765883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765883 prefixEnd_1765883 := by exact prefixLift 1765883
  have htrace : WordTrace (prefixWord ++ tailWord_1765883) baseStart_1765883 baseEnd_1765883 := by
    simpa [prefixWord, tailWord_1765883, baseEnd_1765883] using wordTrace_append hprefix tailTrace_1765883
  have hstable : (prefixWord ++ tailWord_1765883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765883).length < 2 ^ (prefixWord ++ tailWord_1765883).sum := by decide
  have hdescent : baseEnd_1765883 < baseStart_1765883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765902 : List Nat := [4, 1, 1, 2, 3, 1, 4, 6]
def baseStart_1765902 : Nat := 118140960795 + 1765902 * 2 ^ 59
def prefixEnd_1765902 : Nat := 4983230072969 + 3 ^ 40 * 1765902 * 2
def baseEnd_1765902 : Nat := 67167149239707787703983

theorem tailTrace_1765902 : CollatzResearch.WordTrace tailWord_1765902 prefixEnd_1765902 67167149239707787703983 := by
  unfold tailWord_1765902
  simp only [CollatzResearch.WordTrace]
  refine ⟨8050967156055765111967495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42938491498964080597159973 8050967156055765111967495)
  ·
    refine ⟨12076450734083647667951243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8050967156055765111967495 12076450734083647667951243)
    ·
      refine ⟨18114676101125471501926865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12076450734083647667951243 18114676101125471501926865)
      ·
        refine ⟨13586007075844103626445149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18114676101125471501926865 13586007075844103626445149)
        ·
          refine ⟨5094752653441538859916931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13586007075844103626445149 5094752653441538859916931)
          ·
            refine ⟨7642128980162308289875397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5094752653441538859916931 7642128980162308289875397)
            ·
              refine ⟨1432899183780432804351637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7642128980162308289875397 1432899183780432804351637)
              ·
                refine ⟨67167149239707787703983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1432899183780432804351637 67167149239707787703983)
                ·
                  rfl

theorem cell22_1765902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_1765902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765902 prefixEnd_1765902 := by exact prefixLift 1765902
  have htrace : WordTrace (prefixWord ++ tailWord_1765902) baseStart_1765902 baseEnd_1765902 := by
    simpa [prefixWord, tailWord_1765902, baseEnd_1765902] using wordTrace_append hprefix tailTrace_1765902
  have hstable : (prefixWord ++ tailWord_1765902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765902).length < 2 ^ (prefixWord ++ tailWord_1765902).sum := by decide
  have hdescent : baseEnd_1765902 < baseStart_1765902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765940 : List Nat := [2, 5, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_1765940 : Nat := 118140960795 + 1765940 * 2 ^ 59
def prefixEnd_1765940 : Nat := 4983230072969 + 3 ^ 40 * 1765940 * 2
def baseEnd_1765940 : Nat := 604517351333950656885731

theorem tailTrace_1765940 : CollatzResearch.WordTrace tailWord_1765940 prefixEnd_1765940 604517351333950656885731 := by
  unfold tailWord_1765940
  simp only [CollatzResearch.WordTrace]
  refine ⟨32204561611154226692811637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42939415481538968923748849 32204561611154226692811637)
  ·
    refine ⟨3019177651045708752451091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32204561611154226692811637 3019177651045708752451091)
    ·
      refine ⟨4528766476568563128676637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3019177651045708752451091 4528766476568563128676637)
      ·
        refine ⟨1698287428713211173253739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4528766476568563128676637 1698287428713211173253739)
        ·
          refine ⟨2547431143069816759880609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1698287428713211173253739 2547431143069816759880609)
          ·
            refine ⟨1910573357302362569910457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2547431143069816759880609 1910573357302362569910457)
            ·
              refine ⟨1432930017976771927432843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1910573357302362569910457 1432930017976771927432843)
              ·
                refine ⟨2149395026965157891149265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1432930017976771927432843 2149395026965157891149265)
                ·
                  refine ⟨1612046270223868418361949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2149395026965157891149265 1612046270223868418361949)
                  ·
                    refine ⟨604517351333950656885731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1612046270223868418361949 604517351333950656885731)
                    ·
                      rfl

theorem cell22_1765940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_1765940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765940 prefixEnd_1765940 := by exact prefixLift 1765940
  have htrace : WordTrace (prefixWord ++ tailWord_1765940) baseStart_1765940 baseEnd_1765940 := by
    simpa [prefixWord, tailWord_1765940, baseEnd_1765940] using wordTrace_append hprefix tailTrace_1765940
  have hstable : (prefixWord ++ tailWord_1765940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765940).length < 2 ^ (prefixWord ++ tailWord_1765940).sum := by decide
  have hdescent : baseEnd_1765940 < baseStart_1765940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765945 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 1, 7]
def baseStart_1765945 : Nat := 118140960795 + 1765945 * 2 ^ 59
def prefixEnd_1765945 : Nat := 4983230072969 + 3 ^ 40 * 1765945 * 2
def baseEnd_1765945 : Nat := 604519062936132310510715

theorem tailTrace_1765945 : CollatzResearch.WordTrace tailWord_1765945 prefixEnd_1765945 604519062936132310510715 := by
  unfold tailWord_1765945
  simp only [CollatzResearch.WordTrace]
  refine ⟨64409305587290339239555289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42939537058193559493036859 64409305587290339239555289)
  ·
    refine ⟨48306979190467754429666467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64409305587290339239555289 48306979190467754429666467)
    ·
      refine ⟨72460468785701631644499701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48306979190467754429666467 72460468785701631644499701)
      ·
        refine ⟨6793168948659527966671847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72460468785701631644499701 6793168948659527966671847)
        ·
          refine ⟨10189753422989291950007771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6793168948659527966671847 10189753422989291950007771)
          ·
            refine ⟨15284630134483937925011657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10189753422989291950007771 15284630134483937925011657)
            ·
              refine ⟨11463472600862953443758743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15284630134483937925011657 11463472600862953443758743)
              ·
                refine ⟨17195208901294430165638115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11463472600862953443758743 17195208901294430165638115)
                ·
                  refine ⟨25792813351941645248457173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17195208901294430165638115 25792813351941645248457173)
                  ·
                    refine ⟨604519062936132310510715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25792813351941645248457173 604519062936132310510715)
                    ·
                      rfl

theorem cell22_1765945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_1765945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1765945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1765945 prefixEnd_1765945 := by exact prefixLift 1765945
  have htrace : WordTrace (prefixWord ++ tailWord_1765945) baseStart_1765945 baseEnd_1765945 := by
    simpa [prefixWord, tailWord_1765945, baseEnd_1765945] using wordTrace_append hprefix tailTrace_1765945
  have hstable : (prefixWord ++ tailWord_1765945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765945).length < 2 ^ (prefixWord ++ tailWord_1765945).sum := by decide
  have hdescent : baseEnd_1765945 < baseStart_1765945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766026 : List Nat := [3, 1, 2, 3, 3, 1, 2, 3, 4]
def baseStart_1766026 : Nat := 118140960795 + 1766026 * 2 ^ 59
def prefixEnd_1766026 : Nat := 4983230072969 + 3 ^ 40 * 1766026 * 2
def baseEnd_1766026 : Nat := 201515596963825033078489

theorem tailTrace_1766026 : CollatzResearch.WordTrace tailWord_1766026 prefixEnd_1766026 201515596963825033078489 := by
  unfold tailWord_1766026
  simp only [CollatzResearch.WordTrace]
  refine ⟨16103064974999222518313483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42941506599997926715502621 16103064974999222518313483)
  ·
    refine ⟨24154597462498833777470225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16103064974999222518313483 24154597462498833777470225)
    ·
      refine ⟨18115948096874125333102669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24154597462498833777470225 18115948096874125333102669)
      ·
        refine ⟨6793480536327796999913501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18115948096874125333102669 6793480536327796999913501)
        ·
          refine ⟨2547555201122923874967563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6793480536327796999913501 2547555201122923874967563)
          ·
            refine ⟨3821332801684385812451345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2547555201122923874967563 3821332801684385812451345)
            ·
              refine ⟨2865999601263289359338509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3821332801684385812451345 2865999601263289359338509)
              ·
                refine ⟨1074749850473733509751941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2865999601263289359338509 1074749850473733509751941)
                ·
                  refine ⟨201515596963825033078489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1074749850473733509751941 201515596963825033078489)
                  ·
                    rfl

theorem cell22_1766026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 4].length) (baseStart_1766026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766026 prefixEnd_1766026 := by exact prefixLift 1766026
  have htrace : WordTrace (prefixWord ++ tailWord_1766026) baseStart_1766026 baseEnd_1766026 := by
    simpa [prefixWord, tailWord_1766026, baseEnd_1766026] using wordTrace_append hprefix tailTrace_1766026
  have hstable : (prefixWord ++ tailWord_1766026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766026).length < 2 ^ (prefixWord ++ tailWord_1766026).sum := by decide
  have hdescent : baseEnd_1766026 < baseStart_1766026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766058 : List Nat := [3, 1, 5, 2, 1, 2, 1, 1, 1, 5]
def baseStart_1766058 : Nat := 118140960795 + 1766058 * 2 ^ 59
def prefixEnd_1766058 : Nat := 4983230072969 + 3 ^ 40 * 1766058 * 2
def baseEnd_1766058 : Nat := 604557745145437682435369

theorem tailTrace_1766058 : CollatzResearch.WordTrace tailWord_1766058 prefixEnd_1766058 604557745145437682435369 := by
  unfold tailWord_1766058
  simp only [CollatzResearch.WordTrace]
  refine ⟨16103356758970239884604707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42942284690587306358945885 16103356758970239884604707)
  ·
    refine ⟨24155035138455359826907061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16103356758970239884604707 24155035138455359826907061)
    ·
      refine ⟨2264534544230189983772537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24155035138455359826907061 2264534544230189983772537)
      ·
        refine ⟨1698400908172642487829403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2264534544230189983772537 1698400908172642487829403)
        ·
          refine ⟨2547601362258963731744105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1698400908172642487829403 2547601362258963731744105)
          ·
            refine ⟨1910701021694222798808079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2547601362258963731744105 1910701021694222798808079)
            ·
              refine ⟨2866051532541334198212119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1910701021694222798808079 2866051532541334198212119)
              ·
                refine ⟨4299077298812001297318179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2866051532541334198212119 4299077298812001297318179)
                ·
                  refine ⟨6448615948218001945977269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4299077298812001297318179 6448615948218001945977269)
                  ·
                    refine ⟨604557745145437682435369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6448615948218001945977269 604557745145437682435369)
                    ·
                      rfl

theorem cell22_1766058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_1766058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766058 prefixEnd_1766058 := by exact prefixLift 1766058
  have htrace : WordTrace (prefixWord ++ tailWord_1766058) baseStart_1766058 baseEnd_1766058 := by
    simpa [prefixWord, tailWord_1766058, baseEnd_1766058] using wordTrace_append hprefix tailTrace_1766058
  have hstable : (prefixWord ++ tailWord_1766058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766058).length < 2 ^ (prefixWord ++ tailWord_1766058).sum := by decide
  have hdescent : baseEnd_1766058 < baseStart_1766058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766071 : List Nat := [1, 1, 3, 1, 7, 1, 2, 6]
def baseStart_1766071 : Nat := 118140960795 + 1766071 * 2 ^ 59
def prefixEnd_1766071 : Nat := 4983230072969 + 3 ^ 40 * 1766071 * 2
def baseEnd_1766071 : Nat := 67173577256789997984481

theorem tailTrace_1766071 : CollatzResearch.WordTrace tailWord_1766071 prefixEnd_1766071 67173577256789997984481 := by
  unfold tailWord_1766071
  simp only [CollatzResearch.WordTrace]
  refine ⟨64413901184833862758642067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42942600789889241839094711 64413901184833862758642067)
  ·
    refine ⟨96620851777250794137963101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64413901184833862758642067 96620851777250794137963101)
    ·
      refine ⟨36232819416469047801736163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96620851777250794137963101 36232819416469047801736163)
      ·
        refine ⟨54349229124703571702604245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36232819416469047801736163 54349229124703571702604245)
        ·
          refine ⟨1273810057610239961779787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 54349229124703571702604245 1273810057610239961779787)
          ·
            refine ⟨1910715086415359942669681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273810057610239961779787 1910715086415359942669681)
            ·
              refine ⟨1433036314811519957002261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1910715086415359942669681 1433036314811519957002261)
              ·
                refine ⟨67173577256789997984481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1433036314811519957002261 67173577256789997984481)
                ·
                  rfl

theorem cell22_1766071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 6].length) (baseStart_1766071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766071 prefixEnd_1766071 := by exact prefixLift 1766071
  have htrace : WordTrace (prefixWord ++ tailWord_1766071) baseStart_1766071 baseEnd_1766071 := by
    simpa [prefixWord, tailWord_1766071, baseEnd_1766071] using wordTrace_append hprefix tailTrace_1766071
  have hstable : (prefixWord ++ tailWord_1766071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766071).length < 2 ^ (prefixWord ++ tailWord_1766071).sum := by decide
  have hdescent : baseEnd_1766071 < baseStart_1766071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766103 : List Nat := [1, 1, 3, 2, 1, 5, 3, 2, 1, 3]
def baseStart_1766103 : Nat := 118140960795 + 1766103 * 2 ^ 59
def prefixEnd_1766103 : Nat := 4983230072969 + 3 ^ 40 * 1766103 * 2
def baseEnd_1766103 : Nat := 604573149565072565060231

theorem tailTrace_1766103 : CollatzResearch.WordTrace tailWord_1766103 prefixEnd_1766103 604573149565072565060231 := by
  unfold tailWord_1766103
  simp only [CollatzResearch.WordTrace]
  refine ⟨64415068320717932223806963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42943378880478621482537975 64415068320717932223806963)
  ·
    refine ⟨96622602481076898335710445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64415068320717932223806963 96622602481076898335710445)
    ·
      refine ⟨36233475930403836875891417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96622602481076898335710445 36233475930403836875891417)
      ·
        refine ⟨27175106947802877656918563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36233475930403836875891417 27175106947802877656918563)
        ·
          refine ⟨40762660421704316485377845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27175106947802877656918563 40762660421704316485377845)
          ·
            refine ⟨3821499414534779670504173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40762660421704316485377845 3821499414534779670504173)
            ·
              refine ⟨1433062280450542376439065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3821499414534779670504173 1433062280450542376439065)
              ·
                refine ⟨1074796710337906782329299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1433062280450542376439065 1074796710337906782329299)
                ·
                  refine ⟨1612195065506860173493949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1074796710337906782329299 1612195065506860173493949)
                  ·
                    refine ⟨604573149565072565060231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1612195065506860173493949 604573149565072565060231)
                    ·
                      rfl

theorem cell22_1766103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 1, 3].length) (baseStart_1766103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766103 prefixEnd_1766103 := by exact prefixLift 1766103
  have htrace : WordTrace (prefixWord ++ tailWord_1766103) baseStart_1766103 baseEnd_1766103 := by
    simpa [prefixWord, tailWord_1766103, baseEnd_1766103] using wordTrace_append hprefix tailTrace_1766103
  have hstable : (prefixWord ++ tailWord_1766103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766103).length < 2 ^ (prefixWord ++ tailWord_1766103).sum := by decide
  have hdescent : baseEnd_1766103 < baseStart_1766103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
