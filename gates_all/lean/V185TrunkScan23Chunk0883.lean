import V185TrunkScan23Chunk0882

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5225524 : List Nat := [2, 5, 1, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_5225524 : Nat := 118140960795 + 5225524 * 2 ^ 59
def prefixEnd_5225524 : Nat := 4983230072969 + 3 ^ 40 * 5225524 * 2
def baseEnd_5225524 : Nat := 2683205483605118347018259

theorem tailTrace_5225524 : CollatzResearch.WordTrace tailWord_5225524 prefixEnd_5225524 2683205483605118347018259 := by
  unfold tailWord_5225524
  simp only [CollatzResearch.WordTrace]
  refine ⟨95295258960413235646429813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127060345280550980861906417 95295258960413235646429813)
  ·
    refine ⟨8933930527538740841852795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95295258960413235646429813 8933930527538740841852795)
    ·
      refine ⟨13400895791308111262779193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8933930527538740841852795 13400895791308111262779193)
      ·
        refine ⟨10050671843481083447084395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13400895791308111262779193 10050671843481083447084395)
        ·
          refine ⟨15076007765221625170626593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10050671843481083447084395 15076007765221625170626593)
          ·
            refine ⟨11307005823916218877969945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15076007765221625170626593 11307005823916218877969945)
            ·
              refine ⟨8480254367937164158477459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11307005823916218877969945 8480254367937164158477459)
              ·
                refine ⟨12720381551905746237716189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8480254367937164158477459 12720381551905746237716189)
                ·
                  refine ⟨4770143081964654839143571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12720381551905746237716189 4770143081964654839143571)
                  ·
                    refine ⟨7155214622946982258715357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4770143081964654839143571 7155214622946982258715357)
                    ·
                      refine ⟨2683205483605118347018259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7155214622946982258715357 2683205483605118347018259)
                      ·
                        rfl

theorem cell23_5225524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_5225524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225524 prefixEnd_5225524 := by exact prefixLift 5225524
  have htrace : WordTrace (prefixWord ++ tailWord_5225524) baseStart_5225524 baseEnd_5225524 := by
    simpa [prefixWord, tailWord_5225524, baseEnd_5225524] using wordTrace_append hprefix tailTrace_5225524
  have hstable : (prefixWord ++ tailWord_5225524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225524).length < 2 ^ (prefixWord ++ tailWord_5225524).sum := by decide
  have hdescent : baseEnd_5225524 < baseStart_5225524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225533 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 3, 1, 5]
def baseStart_5225533 : Nat := 118140960795 + 5225533 * 2 ^ 59
def prefixEnd_5225533 : Nat := 4983230072969 + 3 ^ 40 * 5225533 * 2
def baseEnd_5225533 : Nat := 2683210104931008811805717

theorem tailTrace_5225533 : CollatzResearch.WordTrace tailWord_5225533 prefixEnd_5225533 2683210104931008811805717 := by
  unfold tailWord_5225533
  simp only [CollatzResearch.WordTrace]
  refine ⟨190590846177793865829937253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127060564118529243886624835 190590846177793865829937253)
  ·
    refine ⟨35735783658336349843113235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190590846177793865829937253 35735783658336349843113235)
    ·
      refine ⟨53603675487504524764669853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35735783658336349843113235 53603675487504524764669853)
      ·
        refine ⟨20101378307814196786751195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53603675487504524764669853 20101378307814196786751195)
        ·
          refine ⟨30152067461721295180126793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20101378307814196786751195 30152067461721295180126793)
          ·
            refine ⟨22614050596290971385095095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30152067461721295180126793 22614050596290971385095095)
            ·
              refine ⟨33921075894436457077642643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22614050596290971385095095 33921075894436457077642643)
              ·
                refine ⟨50881613841654685616463965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33921075894436457077642643 50881613841654685616463965)
                ·
                  refine ⟨19080605190620507106173987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50881613841654685616463965 19080605190620507106173987)
                  ·
                    refine ⟨28620907785930760659260981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19080605190620507106173987 28620907785930760659260981)
                    ·
                      refine ⟨2683210104931008811805717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28620907785930760659260981 2683210104931008811805717)
                      ·
                        rfl

theorem cell23_5225533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_5225533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225533 prefixEnd_5225533 := by exact prefixLift 5225533
  have htrace : WordTrace (prefixWord ++ tailWord_5225533) baseStart_5225533 baseEnd_5225533 := by
    simpa [prefixWord, tailWord_5225533, baseEnd_5225533] using wordTrace_append hprefix tailTrace_5225533
  have hstable : (prefixWord ++ tailWord_5225533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225533).length < 2 ^ (prefixWord ++ tailWord_5225533).sum := by decide
  have hdescent : baseEnd_5225533 < baseStart_5225533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225536 : List Nat := [2, 1, 1, 2, 2, 3, 2, 10]
def baseStart_5225536 : Nat := 118140960795 + 5225536 * 2 ^ 59
def prefixEnd_5225536 : Nat := 4983230072969 + 3 ^ 40 * 5225536 * 2
def baseEnd_5225536 : Nat := 99378209087887862965489

theorem tailTrace_5225536 : CollatzResearch.WordTrace tailWord_5225536 prefixEnd_5225536 99378209087887862965489 := by
  unfold tailWord_5225536
  simp only [CollatzResearch.WordTrace]
  refine ⟨95295477798391498671148231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127060637064521998228197641 95295477798391498671148231)
  ·
    refine ⟨142943216697587248006722347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95295477798391498671148231 142943216697587248006722347)
    ·
      refine ⟨214414825046380872010083521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142943216697587248006722347 214414825046380872010083521)
      ·
        refine ⟨160811118784785654007562641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214414825046380872010083521 160811118784785654007562641)
        ·
          refine ⟨120608339088589240505671981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160811118784785654007562641 120608339088589240505671981)
          ·
            refine ⟨45228127158220965189626993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120608339088589240505671981 45228127158220965189626993)
            ·
              refine ⟨33921095368665723892220245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45228127158220965189626993 33921095368665723892220245)
              ·
                refine ⟨99378209087887862965489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33921095368665723892220245 99378209087887862965489)
                ·
                  rfl

theorem cell23_5225536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 10].length) (baseStart_5225536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225536 prefixEnd_5225536 := by exact prefixLift 5225536
  have htrace : WordTrace (prefixWord ++ tailWord_5225536) baseStart_5225536 baseEnd_5225536 := by
    simpa [prefixWord, tailWord_5225536, baseEnd_5225536] using wordTrace_append hprefix tailTrace_5225536
  have hstable : (prefixWord ++ tailWord_5225536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225536).length < 2 ^ (prefixWord ++ tailWord_5225536).sum := by decide
  have hdescent : baseEnd_5225536 < baseStart_5225536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225543 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 6]
def baseStart_5225543 : Nat := 118140960795 + 5225543 * 2 ^ 59
def prefixEnd_5225543 : Nat := 4983230072969 + 3 ^ 40 * 5225543 * 2
def baseEnd_5225543 : Nat := 2683215239737553772680671

theorem tailTrace_5225543 : CollatzResearch.WordTrace tailWord_5225543 prefixEnd_5225543 2683215239737553772680671 := by
  unfold tailWord_5225543
  simp only [CollatzResearch.WordTrace]
  refine ⟨190591210907757637537801283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127060807271838425025200855 190591210907757637537801283)
  ·
    refine ⟨285886816361636456306701925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190591210907757637537801283 285886816361636456306701925)
    ·
      refine ⟨53603778067806835557506611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 285886816361636456306701925 53603778067806835557506611)
      ·
        refine ⟨80405667101710253336259917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53603778067806835557506611 80405667101710253336259917)
        ·
          refine ⟨30152125163141345001097469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80405667101710253336259917 30152125163141345001097469)
          ·
            refine ⟨11307046936178004375411551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30152125163141345001097469 11307046936178004375411551)
            ·
              refine ⟨16960570404267006563117327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11307046936178004375411551 16960570404267006563117327)
              ·
                refine ⟨25440855606400509844675991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16960570404267006563117327 25440855606400509844675991)
                ·
                  refine ⟨38161283409600764767013987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25440855606400509844675991 38161283409600764767013987)
                  ·
                    refine ⟨57241925114401147150520981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38161283409600764767013987 57241925114401147150520981)
                    ·
                      refine ⟨2683215239737553772680671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57241925114401147150520981 2683215239737553772680671)
                      ·
                        rfl

theorem cell23_5225543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_5225543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225543 prefixEnd_5225543 := by exact prefixLift 5225543
  have htrace : WordTrace (prefixWord ++ tailWord_5225543) baseStart_5225543 baseEnd_5225543 := by
    simpa [prefixWord, tailWord_5225543, baseEnd_5225543] using wordTrace_append hprefix tailTrace_5225543
  have hstable : (prefixWord ++ tailWord_5225543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225543).length < 2 ^ (prefixWord ++ tailWord_5225543).sum := by decide
  have hdescent : baseEnd_5225543 < baseStart_5225543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225553 : List Nat := [1, 2, 2, 1, 3, 1, 6, 7]
def baseStart_5225553 : Nat := 118140960795 + 5225553 * 2 ^ 59
def prefixEnd_5225553 : Nat := 4983230072969 + 3 ^ 40 * 5225553 * 2
def baseEnd_5225553 : Nat := 99378532390522175316875

theorem tailTrace_5225553 : CollatzResearch.WordTrace tailWord_5225553 prefixEnd_5225553 99378532390522175316875 := by
  unfold tailWord_5225553
  simp only [CollatzResearch.WordTrace]
  refine ⟨190591575637721409245665313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127061050425147606163776875 190591575637721409245665313)
  ·
    refine ⟨142943681728291056934248985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190591575637721409245665313 142943681728291056934248985)
    ·
      refine ⟨107207761296218292700686739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142943681728291056934248985 107207761296218292700686739)
      ·
        refine ⟨160811641944327439051030109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107207761296218292700686739 160811641944327439051030109)
        ·
          refine ⟨60304365729122789644136291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160811641944327439051030109 60304365729122789644136291)
          ·
            refine ⟨90456548593684184466204437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60304365729122789644136291 90456548593684184466204437)
            ·
              refine ⟨4240150715328946146853333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90456548593684184466204437 4240150715328946146853333)
              ·
                refine ⟨99378532390522175316875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4240150715328946146853333 99378532390522175316875)
                ·
                  rfl

theorem cell23_5225553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 7].length) (baseStart_5225553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225553 prefixEnd_5225553 := by exact prefixLift 5225553
  have htrace : WordTrace (prefixWord ++ tailWord_5225553) baseStart_5225553 baseEnd_5225553 := by
    simpa [prefixWord, tailWord_5225553, baseEnd_5225553] using wordTrace_append hprefix tailTrace_5225553
  have hstable : (prefixWord ++ tailWord_5225553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225553).length < 2 ^ (prefixWord ++ tailWord_5225553).sum := by decide
  have hdescent : baseEnd_5225553 < baseStart_5225553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225570 : List Nat := [3, 3, 2, 2, 1, 3, 9]
def baseStart_5225570 : Nat := 118140960795 + 5225570 * 2 ^ 59
def prefixEnd_5225570 : Nat := 4983230072969 + 3 ^ 40 * 5225570 * 2
def baseEnd_5225570 : Nat := 33126285231052162556087

theorem tailTrace_5225570 : CollatzResearch.WordTrace tailWord_5225570 prefixEnd_5225570 33126285231052162556087 := by
  unfold tailWord_5225570
  simp only [CollatzResearch.WordTrace]
  refine ⟨47648048919664955287258541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127061463785773214099356109 47648048919664955287258541)
  ·
    refine ⟨17868018344874358232721953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47648048919664955287258541 17868018344874358232721953)
    ·
      refine ⟨13401013758655768674541465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17868018344874358232721953 13401013758655768674541465)
      ·
        refine ⟨10050760318991826505906099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13401013758655768674541465 10050760318991826505906099)
        ·
          refine ⟨15076140478487739758859149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10050760318991826505906099 15076140478487739758859149)
          ·
            refine ⟨5653552679432902409572181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15076140478487739758859149 5653552679432902409572181)
            ·
              refine ⟨33126285231052162556087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5653552679432902409572181 33126285231052162556087)
              ·
                rfl

theorem cell23_5225570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 9].length) (baseStart_5225570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225570 prefixEnd_5225570 := by exact prefixLift 5225570
  have htrace : WordTrace (prefixWord ++ tailWord_5225570) baseStart_5225570 baseEnd_5225570 := by
    simpa [prefixWord, tailWord_5225570, baseEnd_5225570] using wordTrace_append hprefix tailTrace_5225570
  have hstable : (prefixWord ++ tailWord_5225570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225570).length < 2 ^ (prefixWord ++ tailWord_5225570).sum := by decide
  have hdescent : baseEnd_5225570 < baseStart_5225570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225580 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 3]
def baseStart_5225580 : Nat := 118140960795 + 5225580 * 2 ^ 59
def prefixEnd_5225580 : Nat := 4983230072969 + 3 ^ 40 * 5225580 * 2
def baseEnd_5225580 : Nat := 2683234238521770127918001

theorem tailTrace_5225580 : CollatzResearch.WordTrace tailWord_5225580 prefixEnd_5225580 2683234238521770127918001 := by
  unfold tailWord_5225580
  simp only [CollatzResearch.WordTrace]
  refine ⟨95296280204311796428449097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127061706939082395237932129 95296280204311796428449097)
  ·
    refine ⟨71472210153233847321336823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95296280204311796428449097 71472210153233847321336823)
    ·
      refine ⟨107208315229850770982005235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71472210153233847321336823 107208315229850770982005235)
      ·
        refine ⟨160812472844776156473007853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107208315229850770982005235 160812472844776156473007853)
        ·
          refine ⟨60304677316791058677377945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160812472844776156473007853 60304677316791058677377945)
          ·
            refine ⟨45228507987593294008033459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60304677316791058677377945 45228507987593294008033459)
            ·
              refine ⟨67842761981389941012050189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45228507987593294008033459 67842761981389941012050189)
              ·
                refine ⟨25441035743021227879518821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67842761981389941012050189 25441035743021227879518821)
                ·
                  refine ⟨4770194201816480227409779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25441035743021227879518821 4770194201816480227409779)
                  ·
                    refine ⟨7155291302724720341114669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4770194201816480227409779 7155291302724720341114669)
                    ·
                      refine ⟨2683234238521770127918001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7155291302724720341114669 2683234238521770127918001)
                      ·
                        rfl

theorem cell23_5225580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 3].length) (baseStart_5225580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225580 prefixEnd_5225580 := by exact prefixLift 5225580
  have htrace : WordTrace (prefixWord ++ tailWord_5225580) baseStart_5225580 baseEnd_5225580 := by
    simpa [prefixWord, tailWord_5225580, baseEnd_5225580] using wordTrace_append hprefix tailTrace_5225580
  have hstable : (prefixWord ++ tailWord_5225580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225580).length < 2 ^ (prefixWord ++ tailWord_5225580).sum := by decide
  have hdescent : baseEnd_5225580 < baseStart_5225580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225597 : List Nat := [1, 4, 1, 1, 3, 1, 3, 3, 2, 1, 3]
def baseStart_5225597 : Nat := 118140960795 + 5225597 * 2 ^ 59
def prefixEnd_5225597 : Nat := 4983230072969 + 3 ^ 40 * 5225597 * 2
def baseEnd_5225597 : Nat := 2683242967692896561405423

theorem tailTrace_5225597 : CollatzResearch.WordTrace tailWord_5225597 prefixEnd_5225597 2683242967692896561405423 := by
  unfold tailWord_5225597
  simp only [CollatzResearch.WordTrace]
  refine ⟨190593180449562004760267045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127062120299708003173511363 190593180449562004760267045)
  ·
    refine ⟨35736221334292875892550071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190593180449562004760267045 35736221334292875892550071)
    ·
      refine ⟨53604332001439313838825107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35736221334292875892550071 53604332001439313838825107)
      ·
        refine ⟨80406498002158970758237661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53604332001439313838825107 80406498002158970758237661)
        ·
          refine ⟨30152436750809614034339123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80406498002158970758237661 30152436750809614034339123)
          ·
            refine ⟨45228655126214421051508685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30152436750809614034339123 45228655126214421051508685)
            ·
              refine ⟨16960745672330407894315757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45228655126214421051508685 16960745672330407894315757)
              ·
                refine ⟨6360279627123902960368409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16960745672330407894315757 6360279627123902960368409)
                ·
                  refine ⟨4770209720342927220276307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6360279627123902960368409 4770209720342927220276307)
                  ·
                    refine ⟨7155314580514390830414461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4770209720342927220276307 7155314580514390830414461)
                    ·
                      refine ⟨2683242967692896561405423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7155314580514390830414461 2683242967692896561405423)
                      ·
                        rfl

theorem cell23_5225597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_5225597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225597 prefixEnd_5225597 := by exact prefixLift 5225597
  have htrace : WordTrace (prefixWord ++ tailWord_5225597) baseStart_5225597 baseEnd_5225597 := by
    simpa [prefixWord, tailWord_5225597, baseEnd_5225597] using wordTrace_append hprefix tailTrace_5225597
  have hstable : (prefixWord ++ tailWord_5225597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225597).length < 2 ^ (prefixWord ++ tailWord_5225597).sum := by decide
  have hdescent : baseEnd_5225597 < baseStart_5225597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225598 : List Nat := [4, 2, 4, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_5225598 : Nat := 118140960795 + 5225598 * 2 ^ 59
def prefixEnd_5225598 : Nat := 4983230072969 + 3 ^ 40 * 5225598 * 2
def baseEnd_5225598 : Nat := 2683243481173551057492919

theorem tailTrace_5225598 : CollatzResearch.WordTrace tailWord_5225598 prefixEnd_5225598 2683243481173551057492919 := by
  unfold tailWord_5225598
  simp only [CollatzResearch.WordTrace]
  refine ⟨23824152115319797741381681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127062144615038921287368965 23824152115319797741381681)
  ·
    refine ⟨17868114086489848306036261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23824152115319797741381681 17868114086489848306036261)
    ·
      refine ⟨3350271391216846557381799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17868114086489848306036261 3350271391216846557381799)
      ·
        refine ⟨5025407086825269836072699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3350271391216846557381799 5025407086825269836072699)
        ·
          refine ⟨7538110630237904754109049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5025407086825269836072699 7538110630237904754109049)
          ·
            refine ⟨5653582972678428565581787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7538110630237904754109049 5653582972678428565581787)
            ·
              refine ⟨8480374459017642848372681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5653582972678428565581787 8480374459017642848372681)
              ·
                refine ⟨6360280844263232136279511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8480374459017642848372681 6360280844263232136279511)
                ·
                  refine ⟨9540421266394848204419267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6360280844263232136279511 9540421266394848204419267)
                  ·
                    refine ⟨14310631899592272306628901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9540421266394848204419267 14310631899592272306628901)
                    ·
                      refine ⟨2683243481173551057492919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14310631899592272306628901 2683243481173551057492919)
                      ·
                        rfl

theorem cell23_5225598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_5225598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225598 prefixEnd_5225598 := by exact prefixLift 5225598
  have htrace : WordTrace (prefixWord ++ tailWord_5225598) baseStart_5225598 baseEnd_5225598 := by
    simpa [prefixWord, tailWord_5225598, baseEnd_5225598] using wordTrace_append hprefix tailTrace_5225598
  have hstable : (prefixWord ++ tailWord_5225598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225598).length < 2 ^ (prefixWord ++ tailWord_5225598).sum := by decide
  have hdescent : baseEnd_5225598 < baseStart_5225598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225650 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4]
def baseStart_5225650 : Nat := 118140960795 + 5225650 * 2 ^ 59
def prefixEnd_5225650 : Nat := 4983230072969 + 3 ^ 40 * 5225650 * 2
def baseEnd_5225650 : Nat := 2683270182167584854042679

theorem tailTrace_5225650 : CollatzResearch.WordTrace tailWord_5225650 prefixEnd_5225650 2683270182167584854042679 := by
  unfold tailWord_5225650
  simp only [CollatzResearch.WordTrace]
  refine ⟨47648778379592498702986601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127063409012246663207964269 47648778379592498702986601)
  ·
    refine ⟨35736583784694374027239951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47648778379592498702986601 35736583784694374027239951)
    ·
      refine ⟨53604875677041561040859927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35736583784694374027239951 53604875677041561040859927)
      ·
        refine ⟨80407313515562341561289891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53604875677041561040859927 80407313515562341561289891)
        ·
          refine ⟨120610970273343512341934837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80407313515562341561289891 120610970273343512341934837)
          ·
            refine ⟨11307278463125954282056391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120610970273343512341934837 11307278463125954282056391)
            ·
              refine ⟨16960917694688931423084587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11307278463125954282056391 16960917694688931423084587)
              ·
                refine ⟨25441376542033397134626881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16960917694688931423084587 25441376542033397134626881)
                ·
                  refine ⟨19081032406525047850970161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25441376542033397134626881 19081032406525047850970161)
                  ·
                    refine ⟨14310774304893785888227621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19081032406525047850970161 14310774304893785888227621)
                    ·
                      refine ⟨2683270182167584854042679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14310774304893785888227621 2683270182167584854042679)
                      ·
                        rfl

theorem cell23_5225650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_5225650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225650 prefixEnd_5225650 := by exact prefixLift 5225650
  have htrace : WordTrace (prefixWord ++ tailWord_5225650) baseStart_5225650 baseEnd_5225650 := by
    simpa [prefixWord, tailWord_5225650, baseEnd_5225650] using wordTrace_append hprefix tailTrace_5225650
  have hstable : (prefixWord ++ tailWord_5225650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225650).length < 2 ^ (prefixWord ++ tailWord_5225650).sum := by decide
  have hdescent : baseEnd_5225650 < baseStart_5225650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225660 : List Nat := [2, 2, 2, 3, 2, 2, 1, 2, 7]
def baseStart_5225660 : Nat := 118140960795 + 5225660 * 2 ^ 59
def prefixEnd_5225660 : Nat := 4983230072969 + 3 ^ 40 * 5225660 * 2
def baseEnd_5225660 : Nat := 298141701886014423879737

theorem tailTrace_5225660 : CollatzResearch.WordTrace tailWord_5225660 prefixEnd_5225660 298141701886014423879737 := by
  unfold tailWord_5225660
  simp only [CollatzResearch.WordTrace]
  refine ⟨95297739124166883259905217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127063652165555844346540289 95297739124166883259905217)
  ·
    refine ⟨71473304343125162444928913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95297739124166883259905217 71473304343125162444928913)
    ·
      refine ⟨53604978257343871833696685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71473304343125162444928913 53604978257343871833696685)
      ·
        refine ⟨20101866846503951937636257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53604978257343871833696685 20101866846503951937636257)
        ·
          refine ⟨15076400134877963953227193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20101866846503951937636257 15076400134877963953227193)
          ·
            refine ⟨11307300101158472964920395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15076400134877963953227193 11307300101158472964920395)
            ·
              refine ⟨16960950151737709447380593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11307300101158472964920395 16960950151737709447380593)
              ·
                refine ⟨12720712613803282085535445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16960950151737709447380593 12720712613803282085535445)
                ·
                  refine ⟨298141701886014423879737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12720712613803282085535445 298141701886014423879737)
                  ·
                    rfl

theorem cell23_5225660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 7].length) (baseStart_5225660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225660 prefixEnd_5225660 := by exact prefixLift 5225660
  have htrace : WordTrace (prefixWord ++ tailWord_5225660) baseStart_5225660 baseEnd_5225660 := by
    simpa [prefixWord, tailWord_5225660, baseEnd_5225660] using wordTrace_append hprefix tailTrace_5225660
  have hstable : (prefixWord ++ tailWord_5225660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225660).length < 2 ^ (prefixWord ++ tailWord_5225660).sum := by decide
  have hdescent : baseEnd_5225660 < baseStart_5225660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225688 : List Nat := [2, 1, 2, 2, 6, 1, 1, 2, 2, 2, 2]
def baseStart_5225688 : Nat := 118140960795 + 5225688 * 2 ^ 59
def prefixEnd_5225688 : Nat := 4983230072969 + 3 ^ 40 * 5225688 * 2
def baseEnd_5225688 : Nat := 2683289694432455705367505

theorem tailTrace_5225688 : CollatzResearch.WordTrace tailWord_5225688 prefixEnd_5225688 2683289694432455705367505 := by
  unfold tailWord_5225688
  simp only [CollatzResearch.WordTrace]
  refine ⟨95298249746116163650914859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127064332994821551534553145 95298249746116163650914859)
  ·
    refine ⟨142947374619174245476372289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95298249746116163650914859 142947374619174245476372289)
    ·
      refine ⟨107210530964380684107279217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142947374619174245476372289 107210530964380684107279217)
      ·
        refine ⟨80407898223285513080459413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107210530964380684107279217 80407898223285513080459413)
        ·
          refine ⟨3769120229216508425646535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 80407898223285513080459413 3769120229216508425646535)
          ·
            refine ⟨5653680343824762638469803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3769120229216508425646535 5653680343824762638469803)
            ·
              refine ⟨8480520515737143957704705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5653680343824762638469803 8480520515737143957704705)
              ·
                refine ⟨6360390386802857968278529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8480520515737143957704705 6360390386802857968278529)
                ·
                  refine ⟨4770292790102143476208897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6360390386802857968278529 4770292790102143476208897)
                  ·
                    refine ⟨3577719592576607607156673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4770292790102143476208897 3577719592576607607156673)
                    ·
                      refine ⟨2683289694432455705367505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3577719592576607607156673 2683289694432455705367505)
                      ·
                        rfl

theorem cell23_5225688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 2, 2, 2].length) (baseStart_5225688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225688 prefixEnd_5225688 := by exact prefixLift 5225688
  have htrace : WordTrace (prefixWord ++ tailWord_5225688) baseStart_5225688 baseEnd_5225688 := by
    simpa [prefixWord, tailWord_5225688, baseEnd_5225688] using wordTrace_append hprefix tailTrace_5225688
  have hstable : (prefixWord ++ tailWord_5225688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225688).length < 2 ^ (prefixWord ++ tailWord_5225688).sum := by decide
  have hdescent : baseEnd_5225688 < baseStart_5225688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225710 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_5225710 : Nat := 118140960795 + 5225710 * 2 ^ 59
def prefixEnd_5225710 : Nat := 4983230072969 + 3 ^ 40 * 5225710 * 2
def baseEnd_5225710 : Nat := 2683300991006854619292403

theorem tailTrace_5225710 : CollatzResearch.WordTrace tailWord_5225710 prefixEnd_5225710 2683300991006854619292403 := by
  unfold tailWord_5225710
  simp only [CollatzResearch.WordTrace]
  refine ⟨23824662737269078132391323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127064867932101750039420389 23824662737269078132391323)
  ·
    refine ⟨35736994105903617198586985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23824662737269078132391323 35736994105903617198586985)
    ·
      refine ⟨26802745579427712898940239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35736994105903617198586985 26802745579427712898940239)
      ·
        refine ⟨40204118369141569348410359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26802745579427712898940239 40204118369141569348410359)
        ·
          refine ⟨60306177553712354022615539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40204118369141569348410359 60306177553712354022615539)
          ·
            refine ⟨90459266330568531033923309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60306177553712354022615539 90459266330568531033923309)
            ·
              refine ⟨33922224873963199137721241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90459266330568531033923309 33922224873963199137721241)
              ·
                refine ⟨25441668655472399353290931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33922224873963199137721241 25441668655472399353290931)
                ·
                  refine ⟨38162502983208599029936397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25441668655472399353290931 38162502983208599029936397)
                  ·
                    refine ⟨14310938618703224636226149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38162502983208599029936397 14310938618703224636226149)
                    ·
                      refine ⟨2683300991006854619292403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14310938618703224636226149 2683300991006854619292403)
                      ·
                        rfl

theorem cell23_5225710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_5225710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225710 prefixEnd_5225710 := by exact prefixLift 5225710
  have htrace : WordTrace (prefixWord ++ tailWord_5225710) baseStart_5225710 baseEnd_5225710 := by
    simpa [prefixWord, tailWord_5225710, baseEnd_5225710] using wordTrace_append hprefix tailTrace_5225710
  have hstable : (prefixWord ++ tailWord_5225710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225710).length < 2 ^ (prefixWord ++ tailWord_5225710).sum := by decide
  have hdescent : baseEnd_5225710 < baseStart_5225710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225733 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 10]
def baseStart_5225733 : Nat := 118140960795 + 5225733 * 2 ^ 59
def prefixEnd_5225733 : Nat := 4983230072969 + 3 ^ 40 * 5225733 * 2
def baseEnd_5225733 : Nat := 298145866784656447700533

theorem tailTrace_5225733 : CollatzResearch.WordTrace tailWord_5225733 prefixEnd_5225733 298145866784656447700533 := by
  unfold tailWord_5225733
  simp only [CollatzResearch.WordTrace]
  refine ⟨190598140777069299987217853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127065427184712866658145235 190598140777069299987217853)
  ·
    refine ⟨71474302791400987495206695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190598140777069299987217853 71474302791400987495206695)
    ·
      refine ⟨107211454187101481242810043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71474302791400987495206695 107211454187101481242810043)
      ·
        refine ⟨160817181280652221864215065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107211454187101481242810043 160817181280652221864215065)
        ·
          refine ⟨120612885960489166398161299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160817181280652221864215065 120612885960489166398161299)
          ·
            refine ⟨180919328940733749597241949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120612885960489166398161299 180919328940733749597241949)
            ·
              refine ⟨67844748352775156098965731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180919328940733749597241949 67844748352775156098965731)
              ·
                refine ⟨101767122529162734148448597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67844748352775156098965731 101767122529162734148448597)
                ·
                  refine ⟨298145866784656447700533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 101767122529162734148448597 298145866784656447700533)
                  ·
                    rfl

theorem cell23_5225733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 10].length) (baseStart_5225733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225733 prefixEnd_5225733 := by exact prefixLift 5225733
  have htrace : WordTrace (prefixWord ++ tailWord_5225733) baseStart_5225733 baseEnd_5225733 := by
    simpa [prefixWord, tailWord_5225733, baseEnd_5225733] using wordTrace_append hprefix tailTrace_5225733
  have hstable : (prefixWord ++ tailWord_5225733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225733).length < 2 ^ (prefixWord ++ tailWord_5225733).sum := by decide
  have hdescent : baseEnd_5225733 < baseStart_5225733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225754 : List Nat := [3, 1, 1, 3, 3, 3, 1, 1, 3, 4]
def baseStart_5225754 : Nat := 118140960795 + 5225754 * 2 ^ 59
def prefixEnd_5225754 : Nat := 4983230072969 + 3 ^ 40 * 5225754 * 2
def baseEnd_5225754 : Nat := 894441194718550815714067

theorem tailTrace_5225754 : CollatzResearch.WordTrace tailWord_5225754 prefixEnd_5225754 894441194718550815714067 := by
  unfold tailWord_5225754
  simp only [CollatzResearch.WordTrace]
  refine ⟨47649726677498305143433079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127065937806662147049154877 47649726677498305143433079)
  ·
    refine ⟨71474590016247457715149619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47649726677498305143433079 71474590016247457715149619)
    ·
      refine ⟨107211885024371186572724429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71474590016247457715149619 107211885024371186572724429)
      ·
        refine ⟨40204456884139194964771661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107211885024371186572724429 40204456884139194964771661)
        ·
          refine ⟨15076671331552198111789373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40204456884139194964771661 15076671331552198111789373)
          ·
            refine ⟨5653751749332074291921015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15076671331552198111789373 5653751749332074291921015)
            ·
              refine ⟨8480627623998111437881523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5653751749332074291921015 8480627623998111437881523)
              ·
                refine ⟨12720941435997167156822285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8480627623998111437881523 12720941435997167156822285)
                ·
                  refine ⟨4770353038498937683808357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12720941435997167156822285 4770353038498937683808357)
                  ·
                    refine ⟨894441194718550815714067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4770353038498937683808357 894441194718550815714067)
                    ·
                      rfl

theorem cell23_5225754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 3, 4].length) (baseStart_5225754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225754 prefixEnd_5225754 := by exact prefixLift 5225754
  have htrace : WordTrace (prefixWord ++ tailWord_5225754) baseStart_5225754 baseEnd_5225754 := by
    simpa [prefixWord, tailWord_5225754, baseEnd_5225754] using wordTrace_append hprefix tailTrace_5225754
  have hstable : (prefixWord ++ tailWord_5225754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225754).length < 2 ^ (prefixWord ++ tailWord_5225754).sum := by decide
  have hdescent : baseEnd_5225754 < baseStart_5225754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225804 : List Nat := [2, 2, 1, 3, 2, 2, 2, 2, 2, 3, 2]
def baseStart_5225804 : Nat := 118140960795 + 5225804 * 2 ^ 59
def prefixEnd_5225804 : Nat := 4983230072969 + 3 ^ 40 * 5225804 * 2
def baseEnd_5225804 : Nat := 2683349258188377251516971

theorem tailTrace_5225804 : CollatzResearch.WordTrace tailWord_5225804 prefixEnd_5225804 2683349258188377251516971 := by
  unfold tailWord_5225804
  simp only [CollatzResearch.WordTrace]
  refine ⟨95300365179906039556526233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127067153573208052742034977 95300365179906039556526233)
  ·
    refine ⟨71475273884929529667394675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95300365179906039556526233 71475273884929529667394675)
    ·
      refine ⟨107212910827394294501092013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71475273884929529667394675 107212910827394294501092013)
      ·
        refine ⟨40204841560272860437909505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107212910827394294501092013 40204841560272860437909505)
        ·
          refine ⟨30153631170204645328432129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40204841560272860437909505 30153631170204645328432129)
          ·
            refine ⟨22615223377653483996324097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30153631170204645328432129 22615223377653483996324097)
            ·
              refine ⟨16961417533240112997243073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22615223377653483996324097 16961417533240112997243073)
              ·
                refine ⟨12721063149930084747932305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16961417533240112997243073 12721063149930084747932305)
                ·
                  refine ⟨9540797362447563560949229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12721063149930084747932305 9540797362447563560949229)
                  ·
                    refine ⟨3577799010917836335355961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9540797362447563560949229 3577799010917836335355961)
                    ·
                      refine ⟨2683349258188377251516971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3577799010917836335355961 2683349258188377251516971)
                      ·
                        rfl

theorem cell23_5225804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_5225804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225804 prefixEnd_5225804 := by exact prefixLift 5225804
  have htrace : WordTrace (prefixWord ++ tailWord_5225804) baseStart_5225804 baseEnd_5225804 := by
    simpa [prefixWord, tailWord_5225804, baseEnd_5225804] using wordTrace_append hprefix tailTrace_5225804
  have hstable : (prefixWord ++ tailWord_5225804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225804).length < 2 ^ (prefixWord ++ tailWord_5225804).sum := by decide
  have hdescent : baseEnd_5225804 < baseStart_5225804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225810 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 5, 6]
def baseStart_5225810 : Nat := 118140960795 + 5225810 * 2 ^ 59
def prefixEnd_5225810 : Nat := 4983230072969 + 3 ^ 40 * 5225810 * 2
def baseEnd_5225810 : Nat := 894450779690768076013981

theorem tailTrace_5225810 : CollatzResearch.WordTrace tailWord_5225810 prefixEnd_5225810 894450779690768076013981 := by
  unfold tailWord_5225810
  simp only [CollatzResearch.WordTrace]
  refine ⟨47650237299447585534442721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127067299465193561425180589 47650237299447585534442721)
  ·
    refine ⟨35737677974585689150832041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47650237299447585534442721 35737677974585689150832041)
    ·
      refine ⟨26803258480939266863124031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35737677974585689150832041 26803258480939266863124031)
      ·
        refine ⟨40204887721408900294686047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26803258480939266863124031 40204887721408900294686047)
        ·
          refine ⟨60307331582113350442029071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40204887721408900294686047 60307331582113350442029071)
          ·
            refine ⟨90460997373170025663043607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60307331582113350442029071 90460997373170025663043607)
            ·
              refine ⟨135691496059755038494565411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90460997373170025663043607 135691496059755038494565411)
              ·
                refine ⟨203537244089632557741848117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135691496059755038494565411 203537244089632557741848117)
                ·
                  refine ⟨19081616633403052288298261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 203537244089632557741848117 19081616633403052288298261)
                  ·
                    refine ⟨894450779690768076013981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19081616633403052288298261 894450779690768076013981)
                    ·
                      rfl

theorem cell23_5225810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_5225810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225810 prefixEnd_5225810 := by exact prefixLift 5225810
  have htrace : WordTrace (prefixWord ++ tailWord_5225810) baseStart_5225810 baseEnd_5225810 := by
    simpa [prefixWord, tailWord_5225810, baseEnd_5225810] using wordTrace_append hprefix tailTrace_5225810
  have hstable : (prefixWord ++ tailWord_5225810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225810).length < 2 ^ (prefixWord ++ tailWord_5225810).sum := by decide
  have hdescent : baseEnd_5225810 < baseStart_5225810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225827 : List Nat := [1, 1, 1, 5, 2, 3, 2, 1, 1, 6]
def baseStart_5225827 : Nat := 118140960795 + 5225827 * 2 ^ 59
def prefixEnd_5225827 : Nat := 4983230072969 + 3 ^ 40 * 5225827 * 2
def baseEnd_5225827 : Nat := 894453689414476887176455

theorem tailTrace_5225827 : CollatzResearch.WordTrace tailWord_5225827 prefixEnd_5225827 894453689414476887176455 := by
  unfold tailWord_5225827
  simp only [CollatzResearch.WordTrace]
  refine ⟨190601569238728754041139735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127067712825819169360759823 190601569238728754041139735)
  ·
    refine ⟨285902353858093131061709603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190601569238728754041139735 285902353858093131061709603)
    ·
      refine ⟨428853530787139696592564405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285902353858093131061709603 428853530787139696592564405)
      ·
        refine ⟨40205018511294346555552913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 428853530787139696592564405 40205018511294346555552913)
        ·
          refine ⟨30153763883470759916664685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40205018511294346555552913 30153763883470759916664685)
          ·
            refine ⟨11307661456301534968749257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30153763883470759916664685 11307661456301534968749257)
            ·
              refine ⟨8480746092226151226561943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11307661456301534968749257 8480746092226151226561943)
              ·
                refine ⟨12721119138339226839842915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8480746092226151226561943 12721119138339226839842915)
                ·
                  refine ⟨19081678707508840259764373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12721119138339226839842915 19081678707508840259764373)
                  ·
                    refine ⟨894453689414476887176455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19081678707508840259764373 894453689414476887176455)
                    ·
                      rfl

theorem cell23_5225827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 6].length) (baseStart_5225827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225827 prefixEnd_5225827 := by exact prefixLift 5225827
  have htrace : WordTrace (prefixWord ++ tailWord_5225827) baseStart_5225827 baseEnd_5225827 := by
    simpa [prefixWord, tailWord_5225827, baseEnd_5225827] using wordTrace_append hprefix tailTrace_5225827
  have hstable : (prefixWord ++ tailWord_5225827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225827).length < 2 ^ (prefixWord ++ tailWord_5225827).sum := by decide
  have hdescent : baseEnd_5225827 < baseStart_5225827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225857 : List Nat := [1, 2, 4, 3, 2, 1, 10]
def baseStart_5225857 : Nat := 118140960795 + 5225857 * 2 ^ 59
def prefixEnd_5225857 : Nat := 4983230072969 + 3 ^ 40 * 5225857 * 2
def baseEnd_5225857 : Nat := 33128104600778586964867

theorem tailTrace_5225857 : CollatzResearch.WordTrace tailWord_5225857 prefixEnd_5225857 33128104600778586964867 := by
  unfold tailWord_5225857
  simp only [CollatzResearch.WordTrace]
  refine ⟨190602663428620069164731825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127068442285746712776487883 190602663428620069164731825)
  ·
    refine ⟨142951997571465051873548869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190602663428620069164731825 142951997571465051873548869)
    ·
      refine ⟨26803499544649697226290413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142951997571465051873548869 26803499544649697226290413)
      ·
        refine ⟨10051312329243636459858905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26803499544649697226290413 10051312329243636459858905)
        ·
          refine ⟨7538484246932727344894179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10051312329243636459858905 7538484246932727344894179)
          ·
            refine ⟨11307726370399091017341269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7538484246932727344894179 11307726370399091017341269)
            ·
              refine ⟨33128104600778586964867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11307726370399091017341269 33128104600778586964867)
              ·
                rfl

theorem cell23_5225857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 10].length) (baseStart_5225857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225857 prefixEnd_5225857 := by exact prefixLift 5225857
  have htrace : WordTrace (prefixWord ++ tailWord_5225857) baseStart_5225857 baseEnd_5225857 := by
    simpa [prefixWord, tailWord_5225857, baseEnd_5225857] using wordTrace_append hprefix tailTrace_5225857
  have hstable : (prefixWord ++ tailWord_5225857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225857).length < 2 ^ (prefixWord ++ tailWord_5225857).sum := by decide
  have hdescent : baseEnd_5225857 < baseStart_5225857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225900 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 1, 8]
def baseStart_5225900 : Nat := 118140960795 + 5225900 * 2 ^ 59
def prefixEnd_5225900 : Nat := 4983230072969 + 3 ^ 40 * 5225900 * 2
def baseEnd_5225900 : Nat := 894466184110402958638843

theorem tailTrace_5225900 : CollatzResearch.WordTrace tailWord_5225900 prefixEnd_5225900 894466184110402958638843 := by
  unfold tailWord_5225900
  simp only [CollatzResearch.WordTrace]
  refine ⟨95302115883732143754273577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127069487844976191672364769 95302115883732143754273577)
  ·
    refine ⟨71476586912799107815705183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95302115883732143754273577 71476586912799107815705183)
    ·
      refine ⟨107214880369198661723557775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71476586912799107815705183 107214880369198661723557775)
      ·
        refine ⟨160822320553797992585336663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107214880369198661723557775 160822320553797992585336663)
        ·
          refine ⟨241233480830696988878004995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160822320553797992585336663 241233480830696988878004995)
          ·
            refine ⟨361850221246045483317007493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241233480830696988878004995 361850221246045483317007493)
            ·
              refine ⟨67846916483633528121938905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 361850221246045483317007493 67846916483633528121938905)
              ·
                refine ⟨50885187362725146091454179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67846916483633528121938905 50885187362725146091454179)
                ·
                  refine ⟨76327781044087719137181269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50885187362725146091454179 76327781044087719137181269)
                  ·
                    refine ⟨894466184110402958638843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76327781044087719137181269 894466184110402958638843)
                    ·
                      rfl

theorem cell23_5225900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_5225900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225900 prefixEnd_5225900 := by exact prefixLift 5225900
  have htrace : WordTrace (prefixWord ++ tailWord_5225900) baseStart_5225900 baseEnd_5225900 := by
    simpa [prefixWord, tailWord_5225900, baseEnd_5225900] using wordTrace_append hprefix tailTrace_5225900
  have hstable : (prefixWord ++ tailWord_5225900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225900).length < 2 ^ (prefixWord ++ tailWord_5225900).sum := by decide
  have hdescent : baseEnd_5225900 < baseStart_5225900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225901 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_5225901 : Nat := 118140960795 + 5225901 * 2 ^ 59
def prefixEnd_5225901 : Nat := 4983230072969 + 3 ^ 40 * 5225901 * 2
def baseEnd_5225901 : Nat := 2683399065811863372004025

theorem tailTrace_5225901 : CollatzResearch.WordTrace tailWord_5225901 prefixEnd_5225901 2683399065811863372004025 := by
  unfold tailWord_5225901
  simp only [CollatzResearch.WordTrace]
  refine ⟨190604268240460664679333557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127069512160307109786222371 190604268240460664679333557)
  ·
    refine ⟨17869150147543187313687521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 190604268240460664679333557 17869150147543187313687521)
    ·
      refine ⟨13401862610657390485265641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17869150147543187313687521 13401862610657390485265641)
      ·
        refine ⟨10051396957993042863949231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13401862610657390485265641 10051396957993042863949231)
        ·
          refine ⟨15077095436989564295923847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10051396957993042863949231 15077095436989564295923847)
          ·
            refine ⟨22615643155484346443885771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15077095436989564295923847 22615643155484346443885771)
            ·
              refine ⟨33923464733226519665828657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22615643155484346443885771 33923464733226519665828657)
              ·
                refine ⟨25442598549919889749371493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33923464733226519665828657 25442598549919889749371493)
                ·
                  refine ⟨4770487228109979328007155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25442598549919889749371493 4770487228109979328007155)
                  ·
                    refine ⟨7155730842164968992010733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4770487228109979328007155 7155730842164968992010733)
                    ·
                      refine ⟨2683399065811863372004025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7155730842164968992010733 2683399065811863372004025)
                      ·
                        rfl

theorem cell23_5225901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_5225901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225901 prefixEnd_5225901 := by exact prefixLift 5225901
  have htrace : WordTrace (prefixWord ++ tailWord_5225901) baseStart_5225901 baseEnd_5225901 := by
    simpa [prefixWord, tailWord_5225901, baseEnd_5225901] using wordTrace_append hprefix tailTrace_5225901
  have hstable : (prefixWord ++ tailWord_5225901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225901).length < 2 ^ (prefixWord ++ tailWord_5225901).sum := by decide
  have hdescent : baseEnd_5225901 < baseStart_5225901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225927 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 3]
def baseStart_5225927 : Nat := 118140960795 + 5225927 * 2 ^ 59
def prefixEnd_5225927 : Nat := 4983230072969 + 3 ^ 40 * 5225927 * 2
def baseEnd_5225927 : Nat := 2683412416308880270278905

theorem tailTrace_5225927 : CollatzResearch.WordTrace tailWord_5225927 prefixEnd_5225927 2683412416308880270278905 := by
  unfold tailWord_5225927
  simp only [CollatzResearch.WordTrace]
  refine ⟨190605216538366471119780035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127070144358910980746520023 190605216538366471119780035)
  ·
    refine ⟨285907824807549706679670053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190605216538366471119780035 285907824807549706679670053)
    ·
      refine ⟨53607717151415570002438135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 285907824807549706679670053 53607717151415570002438135)
      ·
        refine ⟨80411575727123355003657203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53607717151415570002438135 80411575727123355003657203)
        ·
          refine ⟨120617363590685032505485805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80411575727123355003657203 120617363590685032505485805)
          ·
            refine ⟨45231511346506887189557177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120617363590685032505485805 45231511346506887189557177)
            ·
              refine ⟨33923633509880165392167883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45231511346506887189557177 33923633509880165392167883)
              ·
                refine ⟨50885450264820248088251825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33923633509880165392167883 50885450264820248088251825)
                ·
                  refine ⟨38164087698615186066188869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50885450264820248088251825 38164087698615186066188869)
                  ·
                    refine ⟨7155766443490347387410413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38164087698615186066188869 7155766443490347387410413)
                    ·
                      refine ⟨2683412416308880270278905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7155766443490347387410413 2683412416308880270278905)
                      ·
                        rfl

theorem cell23_5225927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_5225927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225927 prefixEnd_5225927 := by exact prefixLift 5225927
  have htrace : WordTrace (prefixWord ++ tailWord_5225927) baseStart_5225927 baseEnd_5225927 := by
    simpa [prefixWord, tailWord_5225927, baseEnd_5225927] using wordTrace_append hprefix tailTrace_5225927
  have hstable : (prefixWord ++ tailWord_5225927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225927).length < 2 ^ (prefixWord ++ tailWord_5225927).sum := by decide
  have hdescent : baseEnd_5225927 < baseStart_5225927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225981 : List Nat := [1, 4, 1, 1, 1, 4, 4, 2, 5]
def baseStart_5225981 : Nat := 118140960795 + 5225981 * 2 ^ 59
def prefixEnd_5225981 : Nat := 4983230072969 + 3 ^ 40 * 5225981 * 2
def baseEnd_5225981 : Nat := 298160016029358117667073

theorem tailTrace_5225981 : CollatzResearch.WordTrace tailWord_5225981 prefixEnd_5225981 298160016029358117667073 := by
  unfold tailWord_5225981
  simp only [CollatzResearch.WordTrace]
  refine ⟨190607186080170838342245797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127071457386780558894830531 190607186080170838342245797)
  ·
    refine ⟨35738847390032032189171087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190607186080170838342245797 35738847390032032189171087)
    ·
      refine ⟨53608271085048048283756631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35738847390032032189171087 53608271085048048283756631)
      ·
        refine ⟨80412406627572072425634947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53608271085048048283756631 80412406627572072425634947)
        ·
          refine ⟨120618609941358108638452421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80412406627572072425634947 120618609941358108638452421)
          ·
            refine ⟨22615989364004645369709829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120618609941358108638452421 22615989364004645369709829)
            ·
              refine ⟨4240498005750871006820593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22615989364004645369709829 4240498005750871006820593)
              ·
                refine ⟨3180373504313153255115445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4240498005750871006820593 3180373504313153255115445)
                ·
                  refine ⟨298160016029358117667073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3180373504313153255115445 298160016029358117667073)
                  ·
                    rfl

theorem cell23_5225981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_5225981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225981 prefixEnd_5225981 := by exact prefixLift 5225981
  have htrace : WordTrace (prefixWord ++ tailWord_5225981) baseStart_5225981 baseEnd_5225981 := by
    simpa [prefixWord, tailWord_5225981, baseEnd_5225981] using wordTrace_append hprefix tailTrace_5225981
  have hstable : (prefixWord ++ tailWord_5225981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225981).length < 2 ^ (prefixWord ++ tailWord_5225981).sum := by decide
  have hdescent : baseEnd_5225981 < baseStart_5225981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226034 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3]
def baseStart_5226034 : Nat := 118140960795 + 5226034 * 2 ^ 59
def prefixEnd_5226034 : Nat := 4983230072969 + 3 ^ 40 * 5226034 * 2
def baseEnd_5226034 : Nat := 2683467358738911351640913

theorem tailTrace_5226034 : CollatzResearch.WordTrace tailWord_5226034 prefixEnd_5226034 2683467358738911351640913 := by
  unfold tailWord_5226034
  simp only [CollatzResearch.WordTrace]
  refine ⟨47652279787244707098481289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127072746099319218929283437 47652279787244707098481289)
  ·
    refine ⟨35739209840433530323860967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47652279787244707098481289 35739209840433530323860967)
    ·
      refine ⟨53608814760650295485791451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35739209840433530323860967 53608814760650295485791451)
      ·
        refine ⟨80413222140975443228687177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53608814760650295485791451 80413222140975443228687177)
        ·
          refine ⟨60309916605731582421515383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80413222140975443228687177 60309916605731582421515383)
          ·
            refine ⟨90464874908597373632273075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60309916605731582421515383 90464874908597373632273075)
            ·
              refine ⟨135697312362896060448409613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90464874908597373632273075 135697312362896060448409613)
              ·
                refine ⟨50886492136086022668153605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135697312362896060448409613 50886492136086022668153605)
                ·
                  refine ⟨9541217275516129250278801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50886492136086022668153605 9541217275516129250278801)
                  ·
                    refine ⟨7155912956637096937709101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9541217275516129250278801 7155912956637096937709101)
                    ·
                      refine ⟨2683467358738911351640913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7155912956637096937709101 2683467358738911351640913)
                      ·
                        rfl

theorem cell23_5226034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_5226034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226034 prefixEnd_5226034 := by exact prefixLift 5226034
  have htrace : WordTrace (prefixWord ++ tailWord_5226034) baseStart_5226034 baseEnd_5226034 := by
    simpa [prefixWord, tailWord_5226034, baseEnd_5226034] using wordTrace_append hprefix tailTrace_5226034
  have hstable : (prefixWord ++ tailWord_5226034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226034).length < 2 ^ (prefixWord ++ tailWord_5226034).sum := by decide
  have hdescent : baseEnd_5226034 < baseStart_5226034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226041 : List Nat := [1, 2, 1, 5, 1, 3, 2, 1, 3, 4]
def baseStart_5226041 : Nat := 118140960795 + 5226041 * 2 ^ 59
def prefixEnd_5226041 : Nat := 4983230072969 + 3 ^ 40 * 5226041 * 2
def baseEnd_5226041 : Nat := 894490317701164274751127

theorem tailTrace_5226041 : CollatzResearch.WordTrace tailWord_5226041 prefixEnd_5226041 894490317701164274751127 := by
  unfold tailWord_5226041
  simp only [CollatzResearch.WordTrace]
  refine ⟨190609374459953468589429977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127072916306635645726286651 190609374459953468589429977)
  ·
    refine ⟨142957030844965101442072483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190609374459953468589429977 142957030844965101442072483)
    ·
      refine ⟨214435546267447652163108725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142957030844965101442072483 214435546267447652163108725)
      ·
        refine ⟨20103332462573217390291443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 214435546267447652163108725 20103332462573217390291443)
        ·
          refine ⟨30154998693859826085437165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20103332462573217390291443 30154998693859826085437165)
          ·
            refine ⟨11308124510197434782038937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30154998693859826085437165 11308124510197434782038937)
            ·
              refine ⟨8481093382648076086529203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11308124510197434782038937 8481093382648076086529203)
              ·
                refine ⟨12721640073972114129793805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8481093382648076086529203 12721640073972114129793805)
                ·
                  refine ⟨4770615027739542798672677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12721640073972114129793805 4770615027739542798672677)
                  ·
                    refine ⟨894490317701164274751127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4770615027739542798672677 894490317701164274751127)
                    ·
                      rfl

theorem cell23_5226041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 4].length) (baseStart_5226041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226041 prefixEnd_5226041 := by exact prefixLift 5226041
  have htrace : WordTrace (prefixWord ++ tailWord_5226041) baseStart_5226041 baseEnd_5226041 := by
    simpa [prefixWord, tailWord_5226041, baseEnd_5226041] using wordTrace_append hprefix tailTrace_5226041
  have hstable : (prefixWord ++ tailWord_5226041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226041).length < 2 ^ (prefixWord ++ tailWord_5226041).sum := by decide
  have hdescent : baseEnd_5226041 < baseStart_5226041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226098 : List Nat := [3, 2, 1, 2, 3, 1, 3, 1, 3, 1, 3]
def baseStart_5226098 : Nat := 118140960795 + 5226098 * 2 ^ 59
def prefixEnd_5226098 : Nat := 4983230072969 + 3 ^ 40 * 5226098 * 2
def baseEnd_5226098 : Nat := 2683500221500799101240619

theorem tailTrace_5226098 : CollatzResearch.WordTrace tailWord_5226098 prefixEnd_5226098 2683500221500799101240619 := by
  unfold tailWord_5226098
  simp only [CollatzResearch.WordTrace]
  refine ⟨47652863355186741831063737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127074302280497978216169965 47652863355186741831063737)
  ·
    refine ⟨35739647516390056373297803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47652863355186741831063737 35739647516390056373297803)
    ·
      refine ⟨53609471274585084559946705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35739647516390056373297803 53609471274585084559946705)
      ·
        refine ⟨40207103455938813419960029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53609471274585084559946705 40207103455938813419960029)
        ·
          refine ⟨15077663795977055032485011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40207103455938813419960029 15077663795977055032485011)
          ·
            refine ⟨22616495693965582548727517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15077663795977055032485011 22616495693965582548727517)
            ·
              refine ⟨8481185885237093455772819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22616495693965582548727517 8481185885237093455772819)
              ·
                refine ⟨12721778827855640183659229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8481185885237093455772819 12721778827855640183659229)
                ·
                  refine ⟨4770667060445865068872211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12721778827855640183659229 4770667060445865068872211)
                  ·
                    refine ⟨7156000590668797603308317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4770667060445865068872211 7156000590668797603308317)
                    ·
                      refine ⟨2683500221500799101240619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7156000590668797603308317 2683500221500799101240619)
                      ·
                        rfl

theorem cell23_5226098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_5226098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226098 prefixEnd_5226098 := by exact prefixLift 5226098
  have htrace : WordTrace (prefixWord ++ tailWord_5226098) baseStart_5226098 baseEnd_5226098 := by
    simpa [prefixWord, tailWord_5226098, baseEnd_5226098] using wordTrace_append hprefix tailTrace_5226098
  have hstable : (prefixWord ++ tailWord_5226098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226098).length < 2 ^ (prefixWord ++ tailWord_5226098).sum := by decide
  have hdescent : baseEnd_5226098 < baseStart_5226098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226121 : List Nat := [1, 2, 1, 1, 4, 1, 5, 2, 1, 1, 4]
def baseStart_5226121 : Nat := 118140960795 + 5226121 * 2 ^ 59
def prefixEnd_5226121 : Nat := 4983230072969 + 3 ^ 40 * 5226121 * 2
def baseEnd_5226121 : Nat := 2683512031555852511253013

theorem tailTrace_5226121 : CollatzResearch.WordTrace tailWord_5226121 prefixEnd_5226121 2683512031555852511253013 := by
  unfold tailWord_5226121
  simp only [CollatzResearch.WordTrace]
  refine ⟨190612292299663642252342217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127074861533109094834894811 190612292299663642252342217)
  ·
    refine ⟨142959219224747731689256663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190612292299663642252342217 142959219224747731689256663)
    ·
      refine ⟨214438828837121597533884995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142959219224747731689256663 214438828837121597533884995)
      ·
        refine ⟨321658243255682396300827493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214438828837121597533884995 321658243255682396300827493)
        ·
          refine ⟨60310920610440449306405155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 321658243255682396300827493 60310920610440449306405155)
          ·
            refine ⟨90466380915660673959607733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60310920610440449306405155 90466380915660673959607733)
            ·
              refine ⟨8481223210843188183713225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90466380915660673959607733 8481223210843188183713225)
              ·
                refine ⟨6360917408132391137784919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8481223210843188183713225 6360917408132391137784919)
                ·
                  refine ⟨9541376112198586706677379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6360917408132391137784919 9541376112198586706677379)
                  ·
                    refine ⟨14312064168297880060016069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9541376112198586706677379 14312064168297880060016069)
                    ·
                      refine ⟨2683512031555852511253013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14312064168297880060016069 2683512031555852511253013)
                      ·
                        rfl

theorem cell23_5226121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 1, 4].length) (baseStart_5226121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226121 prefixEnd_5226121 := by exact prefixLift 5226121
  have htrace : WordTrace (prefixWord ++ tailWord_5226121) baseStart_5226121 baseEnd_5226121 := by
    simpa [prefixWord, tailWord_5226121, baseEnd_5226121] using wordTrace_append hprefix tailTrace_5226121
  have hstable : (prefixWord ++ tailWord_5226121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226121).length < 2 ^ (prefixWord ++ tailWord_5226121).sum := by decide
  have hdescent : baseEnd_5226121 < baseStart_5226121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226148 : List Nat := [2, 3, 1, 2, 2, 3, 2, 2, 2, 4]
def baseStart_5226148 : Nat := 118140960795 + 5226148 * 2 ^ 59
def prefixEnd_5226148 : Nat := 4983230072969 + 3 ^ 40 * 5226148 * 2
def baseEnd_5226148 : Nat := 894508631844507968538463

theorem tailTrace_5226148 : CollatzResearch.WordTrace tailWord_5226148 prefixEnd_5226148 894508631844507968538463 := by
  unfold tailWord_5226148
  simp only [CollatzResearch.WordTrace]
  refine ⟨95306638535282912931787549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127075518047043883909050065 95306638535282912931787549)
  ·
    refine ⟨35739989450731092349420331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95306638535282912931787549 35739989450731092349420331)
    ·
      refine ⟨53609984176096638524130497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35739989450731092349420331 53609984176096638524130497)
      ·
        refine ⟨40207488132072478893097873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53609984176096638524130497 40207488132072478893097873)
        ·
          refine ⟨30155616099054359169823405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40207488132072478893097873 30155616099054359169823405)
          ·
            refine ⟨11308356037145384688683777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30155616099054359169823405 11308356037145384688683777)
            ·
              refine ⟨8481267027859038516512833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11308356037145384688683777 8481267027859038516512833)
              ·
                refine ⟨6360950270894278887384625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8481267027859038516512833 6360950270894278887384625)
                ·
                  refine ⟨4770712703170709165538469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6360950270894278887384625 4770712703170709165538469)
                  ·
                    refine ⟨894508631844507968538463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4770712703170709165538469 894508631844507968538463)
                    ·
                      rfl

theorem cell23_5226148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_5226148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226148 prefixEnd_5226148 := by exact prefixLift 5226148
  have htrace : WordTrace (prefixWord ++ tailWord_5226148) baseStart_5226148 baseEnd_5226148 := by
    simpa [prefixWord, tailWord_5226148, baseEnd_5226148] using wordTrace_append hprefix tailTrace_5226148
  have hstable : (prefixWord ++ tailWord_5226148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226148).length < 2 ^ (prefixWord ++ tailWord_5226148).sum := by decide
  have hdescent : baseEnd_5226148 < baseStart_5226148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226184 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 2, 2, 5]
def baseStart_5226184 : Nat := 118140960795 + 5226184 * 2 ^ 59
def prefixEnd_5226184 : Nat := 4983230072969 + 3 ^ 40 * 5226184 * 2
def baseEnd_5226184 : Nat := 2683544380837085764765223

theorem tailTrace_5226184 : CollatzResearch.WordTrace tailWord_5226184 prefixEnd_5226184 2683544380837085764765223 := by
  unfold tailWord_5226184
  simp only [CollatzResearch.WordTrace]
  refine ⟨95307295049217702005942803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127076393398956936007923737 95307295049217702005942803)
  ·
    refine ⟨142960942573826553008914205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95307295049217702005942803 142960942573826553008914205)
    ·
      refine ⟨53610353465184957378342827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142960942573826553008914205 53610353465184957378342827)
      ·
        refine ⟨80415530197777436067514241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53610353465184957378342827 80415530197777436067514241)
        ·
          refine ⟨60311647648333077050635681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80415530197777436067514241 60311647648333077050635681)
          ·
            refine ⟨45233735736249807787976761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60311647648333077050635681 45233735736249807787976761)
            ·
              refine ⟨33925301802187355840982571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45233735736249807787976761 33925301802187355840982571)
              ·
                refine ⟨50887952703281033761473857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33925301802187355840982571 50887952703281033761473857)
                ·
                  refine ⟨38165964527460775321105393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50887952703281033761473857 38165964527460775321105393)
                  ·
                    refine ⟨28624473395595581490829045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38165964527460775321105393 28624473395595581490829045)
                    ·
                      refine ⟨2683544380837085764765223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28624473395595581490829045 2683544380837085764765223)
                      ·
                        rfl

theorem cell23_5226184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_5226184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226184 prefixEnd_5226184 := by exact prefixLift 5226184
  have htrace : WordTrace (prefixWord ++ tailWord_5226184) baseStart_5226184 baseEnd_5226184 := by
    simpa [prefixWord, tailWord_5226184, baseEnd_5226184] using wordTrace_append hprefix tailTrace_5226184
  have hstable : (prefixWord ++ tailWord_5226184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226184).length < 2 ^ (prefixWord ++ tailWord_5226184).sum := by decide
  have hdescent : baseEnd_5226184 < baseStart_5226184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226189 : List Nat := [1, 6, 2, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_5226189 : Nat := 118140960795 + 5226189 * 2 ^ 59
def prefixEnd_5226189 : Nat := 4983230072969 + 3 ^ 40 * 5226189 * 2
def baseEnd_5226189 : Nat := 2683546948240358245202701

theorem tailTrace_5226189 : CollatzResearch.WordTrace tailWord_5226189 prefixEnd_5226189 2683546948240358245202701 := by
  unfold tailWord_5226189
  simp only [CollatzResearch.WordTrace]
  refine ⟨190614772463417289865817621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127076514975611526577211747 190614772463417289865817621)
  ·
    refine ⟨8935067459222685462460201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 190614772463417289865817621 8935067459222685462460201)
    ·
      refine ⟨6701300594417014096845151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8935067459222685462460201 6701300594417014096845151)
      ·
        refine ⟨10051950891625521145267727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6701300594417014096845151 10051950891625521145267727)
        ·
          refine ⟨15077926337438281717901591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10051950891625521145267727 15077926337438281717901591)
          ·
            refine ⟨22616889506157422576852387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15077926337438281717901591 22616889506157422576852387)
            ·
              refine ⟨33925334259236133865278581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22616889506157422576852387 33925334259236133865278581)
              ·
                refine ⟨3180500086803387549869867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33925334259236133865278581 3180500086803387549869867)
                ·
                  refine ⟨4770750130205081324804801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3180500086803387549869867 4770750130205081324804801)
                  ·
                    refine ⟨3578062597653810993603601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4770750130205081324804801 3578062597653810993603601)
                    ·
                      refine ⟨2683546948240358245202701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3578062597653810993603601 2683546948240358245202701)
                      ·
                        rfl

theorem cell23_5226189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_5226189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226189 prefixEnd_5226189 := by exact prefixLift 5226189
  have htrace : WordTrace (prefixWord ++ tailWord_5226189) baseStart_5226189 baseEnd_5226189 := by
    simpa [prefixWord, tailWord_5226189, baseEnd_5226189] using wordTrace_append hprefix tailTrace_5226189
  have hstable : (prefixWord ++ tailWord_5226189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226189).length < 2 ^ (prefixWord ++ tailWord_5226189).sum := by decide
  have hdescent : baseEnd_5226189 < baseStart_5226189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226221 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 2, 6]
def baseStart_5226221 : Nat := 118140960795 + 5226221 * 2 ^ 59
def prefixEnd_5226221 : Nat := 4983230072969 + 3 ^ 40 * 5226221 * 2
def baseEnd_5226221 : Nat := 894521126540434040000851

theorem tailTrace_5226221 : CollatzResearch.WordTrace tailWord_5226221 prefixEnd_5226221 894521126540434040000851 := by
  unfold tailWord_5226221
  simp only [CollatzResearch.WordTrace]
  refine ⟨190615939599301359330982517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127077293066200906220655011 190615939599301359330982517)
  ·
    refine ⟨17870244337434502437279611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 190615939599301359330982517 17870244337434502437279611)
    ·
      refine ⟨26805366506151753655919417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17870244337434502437279611 26805366506151753655919417)
      ·
        refine ⟨20104024879613815241939563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26805366506151753655919417 20104024879613815241939563)
        ·
          refine ⟨30156037319420722862909345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20104024879613815241939563 30156037319420722862909345)
          ·
            refine ⟨22617027989565542147182009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30156037319420722862909345 22617027989565542147182009)
            ·
              refine ⟨16962770992174156610386507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22617027989565542147182009 16962770992174156610386507)
              ·
                refine ⟨25444156488261234915579761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16962770992174156610386507 25444156488261234915579761)
                ·
                  refine ⟨19083117366195926186684821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25444156488261234915579761 19083117366195926186684821)
                  ·
                    refine ⟨894521126540434040000851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19083117366195926186684821 894521126540434040000851)
                    ·
                      rfl

theorem cell23_5226221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_5226221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226221 prefixEnd_5226221 := by exact prefixLift 5226221
  have htrace : WordTrace (prefixWord ++ tailWord_5226221) baseStart_5226221 baseEnd_5226221 := by
    simpa [prefixWord, tailWord_5226221, baseEnd_5226221] using wordTrace_append hprefix tailTrace_5226221
  have hstable : (prefixWord ++ tailWord_5226221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226221).length < 2 ^ (prefixWord ++ tailWord_5226221).sum := by decide
  have hdescent : baseEnd_5226221 < baseStart_5226221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226224 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 4]
def baseStart_5226224 : Nat := 118140960795 + 5226224 * 2 ^ 59
def prefixEnd_5226224 : Nat := 4983230072969 + 3 ^ 40 * 5226224 * 2
def baseEnd_5226224 : Nat := 2683564920063265608265039

theorem tailTrace_5226224 : CollatzResearch.WordTrace tailWord_5226224 prefixEnd_5226224 2683564920063265608265039 := by
  unfold tailWord_5226224
  simp only [CollatzResearch.WordTrace]
  refine ⟨95308024509145245421670863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127077366012193660562227817 95308024509145245421670863)
  ·
    refine ⟨142962036763717868132506295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95308024509145245421670863 142962036763717868132506295)
    ·
      refine ⟨214443055145576802198759443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142962036763717868132506295 214443055145576802198759443)
      ·
        refine ⟨321664582718365203298139165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214443055145576802198759443 321664582718365203298139165)
        ·
          refine ⟨120624218519386951236802187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 321664582718365203298139165 120624218519386951236802187)
          ·
            refine ⟨180936327779080426855203281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120624218519386951236802187 180936327779080426855203281)
            ·
              refine ⟨135702245834310320141402461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180936327779080426855203281 135702245834310320141402461)
              ·
                refine ⟨50888342187866370053025923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135702245834310320141402461 50888342187866370053025923)
                ·
                  refine ⟨76332513281799555079538885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50888342187866370053025923 76332513281799555079538885)
                  ·
                    refine ⟨14312346240337416577413541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 76332513281799555079538885 14312346240337416577413541)
                    ·
                      refine ⟨2683564920063265608265039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14312346240337416577413541 2683564920063265608265039)
                      ·
                        rfl

theorem cell23_5226224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 4].length) (baseStart_5226224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226224 prefixEnd_5226224 := by exact prefixLift 5226224
  have htrace : WordTrace (prefixWord ++ tailWord_5226224) baseStart_5226224 baseEnd_5226224 := by
    simpa [prefixWord, tailWord_5226224, baseEnd_5226224] using wordTrace_append hprefix tailTrace_5226224
  have hstable : (prefixWord ++ tailWord_5226224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226224).length < 2 ^ (prefixWord ++ tailWord_5226224).sum := by decide
  have hdescent : baseEnd_5226224 < baseStart_5226224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226298 : List Nat := [3, 1, 1, 1, 5, 2, 2, 1, 2, 5]
def baseStart_5226298 : Nat := 118140960795 + 5226298 * 2 ^ 59
def prefixEnd_5226298 : Nat := 4983230072969 + 3 ^ 40 * 5226298 * 2
def baseEnd_5226298 : Nat := 894534305877232772913233

theorem tailTrace_5226298 : CollatzResearch.WordTrace tailWord_5226298 prefixEnd_5226298 894534305877232772913233 := by
  unfold tailWord_5226298
  simp only [CollatzResearch.WordTrace]
  refine ⟨47654687005005600370383887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127079165346681600987690365 47654687005005600370383887)
  ·
    refine ⟨71482030507508400555575831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47654687005005600370383887 71482030507508400555575831)
    ·
      refine ⟨107223045761262600833363747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71482030507508400555575831 107223045761262600833363747)
      ·
        refine ⟨160834568641893901250045621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107223045761262600833363747 160834568641893901250045621)
        ·
          refine ⟨15078240810177553242191777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 160834568641893901250045621 15078240810177553242191777)
          ·
            refine ⟨11308680607633164931643833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15078240810177553242191777 11308680607633164931643833)
            ·
              refine ⟨8481510455724873698732875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11308680607633164931643833 8481510455724873698732875)
              ·
                refine ⟨12722265683587310548099313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8481510455724873698732875 12722265683587310548099313)
                ·
                  refine ⟨9541699262690482911074485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12722265683587310548099313 9541699262690482911074485)
                  ·
                    refine ⟨894534305877232772913233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9541699262690482911074485 894534305877232772913233)
                    ·
                      rfl

theorem cell23_5226298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 2, 5].length) (baseStart_5226298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226298 prefixEnd_5226298 := by exact prefixLift 5226298
  have htrace : WordTrace (prefixWord ++ tailWord_5226298) baseStart_5226298 baseEnd_5226298 := by
    simpa [prefixWord, tailWord_5226298, baseEnd_5226298] using wordTrace_append hprefix tailTrace_5226298
  have hstable : (prefixWord ++ tailWord_5226298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226298).length < 2 ^ (prefixWord ++ tailWord_5226298).sum := by decide
  have hdescent : baseEnd_5226298 < baseStart_5226298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226304 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 9]
def baseStart_5226304 : Nat := 118140960795 + 5226304 * 2 ^ 59
def prefixEnd_5226304 : Nat := 4983230072969 + 3 ^ 40 * 5226304 * 2
def baseEnd_5226304 : Nat := 2683605998515625295264671

theorem tailTrace_5226304 : CollatzResearch.WordTrace tailWord_5226304 prefixEnd_5226304 2683605998515625295264671 := by
  unfold tailWord_5226304
  simp only [CollatzResearch.WordTrace]
  refine ⟨95309483429000332253126983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127079311238667109670835977 95309483429000332253126983)
  ·
    refine ⟨142964225143500498379690475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95309483429000332253126983 142964225143500498379690475)
    ·
      refine ⟨214446337715250747569535713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142964225143500498379690475 214446337715250747569535713)
      ·
        refine ⟨160834753286438060677151785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214446337715250747569535713 160834753286438060677151785)
        ·
          refine ⟨120626064964828545507863839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160834753286438060677151785 120626064964828545507863839)
          ·
            refine ⟨180939097447242818261795759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120626064964828545507863839 180939097447242818261795759)
            ·
              refine ⟨271408646170864227392693639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180939097447242818261795759 271408646170864227392693639)
              ·
                refine ⟨407112969256296341089040459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271408646170864227392693639 407112969256296341089040459)
                ·
                  refine ⟨610669453884444511633560689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 407112969256296341089040459 610669453884444511633560689)
                  ·
                    refine ⟨458002090413333383725170517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 610669453884444511633560689 458002090413333383725170517)
                    ·
                      refine ⟨2683605998515625295264671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 458002090413333383725170517 2683605998515625295264671)
                      ·
                        rfl

theorem cell23_5226304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_5226304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226304 prefixEnd_5226304 := by exact prefixLift 5226304
  have htrace : WordTrace (prefixWord ++ tailWord_5226304) baseStart_5226304 baseEnd_5226304 := by
    simpa [prefixWord, tailWord_5226304, baseEnd_5226304] using wordTrace_append hprefix tailTrace_5226304
  have hstable : (prefixWord ++ tailWord_5226304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226304).length < 2 ^ (prefixWord ++ tailWord_5226304).sum := by decide
  have hdescent : baseEnd_5226304 < baseStart_5226304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226368 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 5, 1, 3]
def baseStart_5226368 : Nat := 118140960795 + 5226368 * 2 ^ 59
def prefixEnd_5226368 : Nat := 4983230072969 + 3 ^ 40 * 5226368 * 2
def baseEnd_5226368 : Nat := 2683638861277513044864377

theorem tailTrace_5226368 : CollatzResearch.WordTrace tailWord_5226368 prefixEnd_5226368 2683638861277513044864377 := by
  unfold tailWord_5226368
  simp only [CollatzResearch.WordTrace]
  refine ⟨95310650564884401718291879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127080867419845868957722505 95310650564884401718291879)
  ·
    refine ⟨142965975847326602577437819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95310650564884401718291879 142965975847326602577437819)
    ·
      refine ⟨214448963770989903866156729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142965975847326602577437819 214448963770989903866156729)
      ·
        refine ⟨160836722828242427899617547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214448963770989903866156729 160836722828242427899617547)
        ·
          refine ⟨241255084242363641849426321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160836722828242427899617547 241255084242363641849426321)
          ·
            refine ⟨180941313181772731387069741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241255084242363641849426321 180941313181772731387069741)
            ·
              refine ⟨67852992443164774270151153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180941313181772731387069741 67852992443164774270151153)
              ·
                refine ⟨50889744332373580702613365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67852992443164774270151153 50889744332373580702613365)
                ·
                  refine ⟨4770913531160023190870003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50889744332373580702613365 4770913531160023190870003)
                  ·
                    refine ⟨7156370296740034786305005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4770913531160023190870003 7156370296740034786305005)
                    ·
                      refine ⟨2683638861277513044864377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7156370296740034786305005 2683638861277513044864377)
                      ·
                        rfl

theorem cell23_5226368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 5, 1, 3].length) (baseStart_5226368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226368 prefixEnd_5226368 := by exact prefixLift 5226368
  have htrace : WordTrace (prefixWord ++ tailWord_5226368) baseStart_5226368 baseEnd_5226368 := by
    simpa [prefixWord, tailWord_5226368, baseEnd_5226368] using wordTrace_append hprefix tailTrace_5226368
  have hstable : (prefixWord ++ tailWord_5226368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226368).length < 2 ^ (prefixWord ++ tailWord_5226368).sum := by decide
  have hdescent : baseEnd_5226368 < baseStart_5226368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226375 : List Nat := [1, 1, 4, 2, 4, 2, 1, 2, 6]
def baseStart_5226375 : Nat := 118140960795 + 5226375 * 2 ^ 59
def prefixEnd_5226375 : Nat := 4983230072969 + 3 ^ 40 * 5226375 * 2
def baseEnd_5226375 : Nat := 298182495071343835275205

theorem tailTrace_5226375 : CollatzResearch.WordTrace tailWord_5226375 prefixEnd_5226375 298182495071343835275205 := by
  unfold tailWord_5226375
  simp only [CollatzResearch.WordTrace]
  refine ⟨190621556440743443632088579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127081037627162295754725719 190621556440743443632088579)
  ·
    refine ⟨285932334661115165448132869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190621556440743443632088579 285932334661115165448132869)
    ·
      refine ⟨53612312748959093521524913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 285932334661115165448132869 53612312748959093521524913)
      ·
        refine ⟨40209234561719320141143685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53612312748959093521524913 40209234561719320141143685)
        ·
          refine ⟨7539231480322372526464441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40209234561719320141143685 7539231480322372526464441)
          ·
            refine ⟨5654423610241779394848331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7539231480322372526464441 5654423610241779394848331)
            ·
              refine ⟨8481635415362669092272497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5654423610241779394848331 8481635415362669092272497)
              ·
                refine ⟨6361226561522001819204373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8481635415362669092272497 6361226561522001819204373)
                ·
                  refine ⟨298182495071343835275205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6361226561522001819204373 298182495071343835275205)
                  ·
                    rfl

theorem cell23_5226375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 6].length) (baseStart_5226375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226375 prefixEnd_5226375 := by exact prefixLift 5226375
  have htrace : WordTrace (prefixWord ++ tailWord_5226375) baseStart_5226375 baseEnd_5226375 := by
    simpa [prefixWord, tailWord_5226375, baseEnd_5226375] using wordTrace_append hprefix tailTrace_5226375
  have hstable : (prefixWord ++ tailWord_5226375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226375).length < 2 ^ (prefixWord ++ tailWord_5226375).sum := by decide
  have hdescent : baseEnd_5226375 < baseStart_5226375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226392 : List Nat := [2, 1, 2, 6, 1, 1, 3, 1, 6]
def baseStart_5226392 : Nat := 118140960795 + 5226392 * 2 ^ 59
def prefixEnd_5226392 : Nat := 4983230072969 + 3 ^ 40 * 5226392 * 2
def baseEnd_5226392 : Nat := 298183464979246772329363

theorem tailTrace_5226392 : CollatzResearch.WordTrace tailWord_5226392 prefixEnd_5226392 298183464979246772329363 := by
  unfold tailWord_5226392
  simp only [CollatzResearch.WordTrace]
  refine ⟨95311088240840927767728715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127081450987787903690304953 95311088240840927767728715)
  ·
    refine ⟨142966632361261391651593073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95311088240840927767728715 142966632361261391651593073)
    ·
      refine ⟨107224974270946043738694805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142966632361261391651593073 107224974270946043738694805)
      ·
        refine ⟨5026170668950595800251319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 107224974270946043738694805 5026170668950595800251319)
        ·
          refine ⟨7539256003425893700376979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5026170668950595800251319 7539256003425893700376979)
          ·
            refine ⟨11308884005138840550565469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7539256003425893700376979 11308884005138840550565469)
            ·
              refine ⟨4240831501927065206462051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11308884005138840550565469 4240831501927065206462051)
              ·
                refine ⟨6361247252890597809693077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4240831501927065206462051 6361247252890597809693077)
                ·
                  refine ⟨298183464979246772329363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6361247252890597809693077 298183464979246772329363)
                  ·
                    rfl

theorem cell23_5226392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 6].length) (baseStart_5226392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226392 prefixEnd_5226392 := by exact prefixLift 5226392
  have htrace : WordTrace (prefixWord ++ tailWord_5226392) baseStart_5226392 baseEnd_5226392 := by
    simpa [prefixWord, tailWord_5226392, baseEnd_5226392] using wordTrace_append hprefix tailTrace_5226392
  have hstable : (prefixWord ++ tailWord_5226392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226392).length < 2 ^ (prefixWord ++ tailWord_5226392).sum := by decide
  have hdescent : baseEnd_5226392 < baseStart_5226392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226442 : List Nat := [3, 1, 2, 1, 2, 1, 5, 1, 3, 2, 2]
def baseStart_5226442 : Nat := 118140960795 + 5226442 * 2 ^ 59
def prefixEnd_5226442 : Nat := 4983230072969 + 3 ^ 40 * 5226442 * 2
def baseEnd_5226442 : Nat := 2683676858845945755339037

theorem tailTrace_5226442 : CollatzResearch.WordTrace tailWord_5226442 prefixEnd_5226442 2683676858845945755339037 := by
  unfold tailWord_5226442
  simp only [CollatzResearch.WordTrace]
  refine ⟨47656000032875178518694395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127082666754333809383185053 47656000032875178518694395)
  ·
    refine ⟨71484000049312767778041593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47656000032875178518694395 71484000049312767778041593)
    ·
      refine ⟨53613000036984575833531195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71484000049312767778041593 53613000036984575833531195)
      ·
        refine ⟨80419500055476863750296793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53613000036984575833531195 80419500055476863750296793)
        ·
          refine ⟨60314625041607647812722595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80419500055476863750296793 60314625041607647812722595)
          ·
            refine ⟨90471937562411471719083893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60314625041607647812722595 90471937562411471719083893)
            ·
              refine ⟨8481744146476075473664115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90471937562411471719083893 8481744146476075473664115)
              ·
                refine ⟨12722616219714113210496173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8481744146476075473664115 12722616219714113210496173)
                ·
                  refine ⟨4770981082392792453936065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12722616219714113210496173 4770981082392792453936065)
                  ·
                    refine ⟨3578235811794594340452049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4770981082392792453936065 3578235811794594340452049)
                    ·
                      refine ⟨2683676858845945755339037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3578235811794594340452049 2683676858845945755339037)
                      ·
                        rfl

theorem cell23_5226442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 3, 2, 2].length) (baseStart_5226442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226442 prefixEnd_5226442 := by exact prefixLift 5226442
  have htrace : WordTrace (prefixWord ++ tailWord_5226442) baseStart_5226442 baseEnd_5226442 := by
    simpa [prefixWord, tailWord_5226442, baseEnd_5226442] using wordTrace_append hprefix tailTrace_5226442
  have hstable : (prefixWord ++ tailWord_5226442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226442).length < 2 ^ (prefixWord ++ tailWord_5226442).sum := by decide
  have hdescent : baseEnd_5226442 < baseStart_5226442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226492 : List Nat := [2, 2, 2, 1, 2, 2, 4, 2, 2, 1, 3]
def baseStart_5226492 : Nat := 118140960795 + 5226492 * 2 ^ 59
def prefixEnd_5226492 : Nat := 4983230072969 + 3 ^ 40 * 5226492 * 2
def baseEnd_5226492 : Nat := 2683702532878670559713807

theorem tailTrace_5226492 : CollatzResearch.WordTrace tailWord_5226492 prefixEnd_5226492 2683702532878670559713807 := by
  unfold tailWord_5226492
  simp only [CollatzResearch.WordTrace]
  refine ⟨95312911890659786307048865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127083882520879715076065153 95312911890659786307048865)
  ·
    refine ⟨71484683917994839730286649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95312911890659786307048865 71484683917994839730286649)
    ·
      refine ⟨53613512938496129797714987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71484683917994839730286649 53613512938496129797714987)
      ·
        refine ⟨80420269407744194696572481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53613512938496129797714987 80420269407744194696572481)
        ·
          refine ⟨60315202055808146022429361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80420269407744194696572481 60315202055808146022429361)
          ·
            refine ⟨45236401541856109516822021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60315202055808146022429361 45236401541856109516822021)
            ·
              refine ⟨8481825289098020534404129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45236401541856109516822021 8481825289098020534404129)
              ·
                refine ⟨6361368966823515400803097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8481825289098020534404129 6361368966823515400803097)
                ·
                  refine ⟨4771026725117636550602323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6361368966823515400803097 4771026725117636550602323)
                  ·
                    refine ⟨7156540087676454825903485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4771026725117636550602323 7156540087676454825903485)
                    ·
                      refine ⟨2683702532878670559713807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7156540087676454825903485 2683702532878670559713807)
                      ·
                        rfl

theorem cell23_5226492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_5226492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226492 prefixEnd_5226492 := by exact prefixLift 5226492
  have htrace : WordTrace (prefixWord ++ tailWord_5226492) baseStart_5226492 baseEnd_5226492 := by
    simpa [prefixWord, tailWord_5226492, baseEnd_5226492] using wordTrace_append hprefix tailTrace_5226492
  have hstable : (prefixWord ++ tailWord_5226492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226492).length < 2 ^ (prefixWord ++ tailWord_5226492).sum := by decide
  have hdescent : baseEnd_5226492 < baseStart_5226492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226508 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 2, 6]
def baseStart_5226508 : Nat := 118140960795 + 5226508 * 2 ^ 59
def prefixEnd_5226508 : Nat := 4983230072969 + 3 ^ 40 * 5226508 * 2
def baseEnd_5226508 : Nat := 894570249523047499037911

theorem tailTrace_5226508 : CollatzResearch.WordTrace tailWord_5226508 prefixEnd_5226508 894570249523047499037911 := by
  unfold tailWord_5226508
  simp only [CollatzResearch.WordTrace]
  refine ⟨95313203674630803673340089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127084271566174404897786785 95313203674630803673340089)
  ·
    refine ⟨71484902755973102755005067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95313203674630803673340089 71484902755973102755005067)
    ·
      refine ⟨107227354133959654132507601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71484902755973102755005067 107227354133959654132507601)
      ·
        refine ⟨80420515600469740599380701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107227354133959654132507601 80420515600469740599380701)
        ·
          refine ⟨30157693350176152724767763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80420515600469740599380701 30157693350176152724767763)
          ·
            refine ⟨45236540025264229087151645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30157693350176152724767763 45236540025264229087151645)
            ·
              refine ⟨16963702509474085907681867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45236540025264229087151645 16963702509474085907681867)
              ·
                refine ⟨25445553764211128861522801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16963702509474085907681867 25445553764211128861522801)
                ·
                  refine ⟨19084165323158346646142101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25445553764211128861522801 19084165323158346646142101)
                  ·
                    refine ⟨894570249523047499037911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19084165323158346646142101 894570249523047499037911)
                    ·
                      rfl

theorem cell23_5226508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_5226508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226508 prefixEnd_5226508 := by exact prefixLift 5226508
  have htrace : WordTrace (prefixWord ++ tailWord_5226508) baseStart_5226508 baseEnd_5226508 := by
    simpa [prefixWord, tailWord_5226508, baseEnd_5226508] using wordTrace_append hprefix tailTrace_5226508
  have hstable : (prefixWord ++ tailWord_5226508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226508).length < 2 ^ (prefixWord ++ tailWord_5226508).sum := by decide
  have hdescent : baseEnd_5226508 < baseStart_5226508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226511 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 10]
def baseStart_5226511 : Nat := 118140960795 + 5226511 * 2 ^ 59
def prefixEnd_5226511 : Nat := 4983230072969 + 3 ^ 40 * 5226511 * 2
def baseEnd_5226511 : Nat := 2683712289011105985376219

theorem tailTrace_5226511 : CollatzResearch.WordTrace tailWord_5226511 prefixEnd_5226511 2683712289011105985376219 := by
  unfold tailWord_5226511
  simp only [CollatzResearch.WordTrace]
  refine ⟨190626516768250738859039387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127084344512167159239359591 190626516768250738859039387)
  ·
    refine ⟨285939775152376108288559081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190626516768250738859039387 285939775152376108288559081)
    ·
      refine ⟨214454831364282081216419311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285939775152376108288559081 214454831364282081216419311)
      ·
        refine ⟨321682247046423121824628967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214454831364282081216419311 321682247046423121824628967)
        ·
          refine ⟨482523370569634682736943451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321682247046423121824628967 482523370569634682736943451)
          ·
            refine ⟨723785055854452024105415177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482523370569634682736943451 723785055854452024105415177)
            ·
              refine ⟨542838791890839018079061383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 723785055854452024105415177 542838791890839018079061383)
              ·
                refine ⟨814258187836258527118592075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 542838791890839018079061383 814258187836258527118592075)
                ·
                  refine ⟨1221387281754387790677888113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 814258187836258527118592075 1221387281754387790677888113)
                  ·
                    refine ⟨916040461315790843008416085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1221387281754387790677888113 916040461315790843008416085)
                    ·
                      refine ⟨2683712289011105985376219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 916040461315790843008416085 2683712289011105985376219)
                      ·
                        rfl

theorem cell23_5226511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_5226511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226511 prefixEnd_5226511 := by exact prefixLift 5226511
  have htrace : WordTrace (prefixWord ++ tailWord_5226511) baseStart_5226511 baseEnd_5226511 := by
    simpa [prefixWord, tailWord_5226511, baseEnd_5226511] using wordTrace_append hprefix tailTrace_5226511
  have hstable : (prefixWord ++ tailWord_5226511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226511).length < 2 ^ (prefixWord ++ tailWord_5226511).sum := by decide
  have hdescent : baseEnd_5226511 < baseStart_5226511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226515 : List Nat := [1, 1, 1, 2, 1, 4, 3, 3, 1, 4, 2]
def baseStart_5226515 : Nat := 118140960795 + 5226515 * 2 ^ 59
def prefixEnd_5226515 : Nat := 4983230072969 + 3 ^ 40 * 5226515 * 2
def baseEnd_5226515 : Nat := 2683714342933723969726201

theorem tailTrace_5226515 : CollatzResearch.WordTrace tailWord_5226515 prefixEnd_5226515 2683714342933723969726201 := by
  unfold tailWord_5226515
  simp only [CollatzResearch.WordTrace]
  refine ⟨190626662660236247542184999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127084441773490831694789999 190626662660236247542184999)
  ·
    refine ⟨285939993990354371313277499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190626662660236247542184999 285939993990354371313277499)
    ·
      refine ⟨428909990985531556969916249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285939993990354371313277499 428909990985531556969916249)
      ·
        refine ⟨321682493239148667727437187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428909990985531556969916249 321682493239148667727437187)
        ·
          refine ⟨482523739858723001591155781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321682493239148667727437187 482523739858723001591155781)
          ·
            refine ⟨90473201223510562798341709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 482523739858723001591155781 90473201223510562798341709)
            ·
              refine ⟨33927450458816461049378141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90473201223510562798341709 33927450458816461049378141)
              ·
                refine ⟨12722793922056172893516803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33927450458816461049378141 12722793922056172893516803)
                ·
                  refine ⟨19084190883084259340275205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12722793922056172893516803 19084190883084259340275205)
                  ·
                    refine ⟨3578285790578298626301601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19084190883084259340275205 3578285790578298626301601)
                    ·
                      refine ⟨2683714342933723969726201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3578285790578298626301601 2683714342933723969726201)
                      ·
                        rfl

theorem cell23_5226515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 4, 2].length) (baseStart_5226515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226515 prefixEnd_5226515 := by exact prefixLift 5226515
  have htrace : WordTrace (prefixWord ++ tailWord_5226515) baseStart_5226515 baseEnd_5226515 := by
    simpa [prefixWord, tailWord_5226515, baseEnd_5226515] using wordTrace_append hprefix tailTrace_5226515
  have hstable : (prefixWord ++ tailWord_5226515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226515).length < 2 ^ (prefixWord ++ tailWord_5226515).sum := by decide
  have hdescent : baseEnd_5226515 < baseStart_5226515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226536 : List Nat := [2, 1, 5, 3, 1, 1, 1, 3, 1, 3, 2]
def baseStart_5226536 : Nat := 118140960795 + 5226536 * 2 ^ 59
def prefixEnd_5226536 : Nat := 4983230072969 + 3 ^ 40 * 5226536 * 2
def baseEnd_5226536 : Nat := 2683725126027468387563605

theorem tailTrace_5226536 : CollatzResearch.WordTrace tailWord_5226536 prefixEnd_5226536 2683725126027468387563605 := by
  unfold tailWord_5226536
  simp only [CollatzResearch.WordTrace]
  refine ⟨95313714296580084064349731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127084952395440112085799641 95313714296580084064349731)
  ·
    refine ⟨142970571444870126096524597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95313714296580084064349731 142970571444870126096524597)
    ·
      refine ⟨13403491072956574321549181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142970571444870126096524597 13403491072956574321549181)
      ·
        refine ⟨5026309152358715370580943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13403491072956574321549181 5026309152358715370580943)
        ·
          refine ⟨7539463728538073055871415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5026309152358715370580943 7539463728538073055871415)
          ·
            refine ⟨11309195592807109583807123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7539463728538073055871415 11309195592807109583807123)
            ·
              refine ⟨16963793389210664375710685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11309195592807109583807123 16963793389210664375710685)
              ·
                refine ⟨6361422520953999140891507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16963793389210664375710685 6361422520953999140891507)
                ·
                  refine ⟨9542133781430998711337261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6361422520953999140891507 9542133781430998711337261)
                  ·
                    refine ⟨3578300168036624516751473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9542133781430998711337261 3578300168036624516751473)
                    ·
                      refine ⟨2683725126027468387563605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3578300168036624516751473 2683725126027468387563605)
                      ·
                        rfl

theorem cell23_5226536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_5226536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226536 prefixEnd_5226536 := by exact prefixLift 5226536
  have htrace : WordTrace (prefixWord ++ tailWord_5226536) baseStart_5226536 baseEnd_5226536 := by
    simpa [prefixWord, tailWord_5226536, baseEnd_5226536] using wordTrace_append hprefix tailTrace_5226536
  have hstable : (prefixWord ++ tailWord_5226536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226536).length < 2 ^ (prefixWord ++ tailWord_5226536).sum := by decide
  have hdescent : baseEnd_5226536 < baseStart_5226536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226549 : List Nat := [1, 3, 3, 1, 1, 1, 5, 2, 2, 2, 2]
def baseStart_5226549 : Nat := 118140960795 + 5226549 * 2 ^ 59
def prefixEnd_5226549 : Nat := 4983230072969 + 3 ^ 40 * 5226549 * 2
def baseEnd_5226549 : Nat := 2683731801275976836701045

theorem tailTrace_5226549 : CollatzResearch.WordTrace tailWord_5226549 prefixEnd_5226549 2683731801275976836701045 := by
  unfold tailWord_5226549
  simp only [CollatzResearch.WordTrace]
  refine ⟨190627902742113071348922701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127085268494742047565948467 190627902742113071348922701)
  ·
    refine ⟨71485463528292401755846013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190627902742113071348922701 71485463528292401755846013)
    ·
      refine ⟨26807048823109650658442255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71485463528292401755846013 26807048823109650658442255)
      ·
        refine ⟨40210573234664475987663383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26807048823109650658442255 40210573234664475987663383)
        ·
          refine ⟨60315859851996713981495075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40210573234664475987663383 60315859851996713981495075)
          ·
            refine ⟨90473789777995070972242613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60315859851996713981495075 90473789777995070972242613)
            ·
              refine ⟨8481917791687037903647745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90473789777995070972242613 8481917791687037903647745)
              ·
                refine ⟨6361438343765278427735809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8481917791687037903647745 6361438343765278427735809)
                ·
                  refine ⟨4771078757823958820801857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6361438343765278427735809 4771078757823958820801857)
                  ·
                    refine ⟨3578309068367969115601393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4771078757823958820801857 3578309068367969115601393)
                    ·
                      refine ⟨2683731801275976836701045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3578309068367969115601393 2683731801275976836701045)
                      ·
                        rfl

theorem cell23_5226549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_5226549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226549 prefixEnd_5226549 := by exact prefixLift 5226549
  have htrace : WordTrace (prefixWord ++ tailWord_5226549) baseStart_5226549 baseEnd_5226549 := by
    simpa [prefixWord, tailWord_5226549, baseEnd_5226549] using wordTrace_append hprefix tailTrace_5226549
  have hstable : (prefixWord ++ tailWord_5226549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226549).length < 2 ^ (prefixWord ++ tailWord_5226549).sum := by decide
  have hdescent : baseEnd_5226549 < baseStart_5226549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226568 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 6, 5]
def baseStart_5226568 : Nat := 118140960795 + 5226568 * 2 ^ 59
def prefixEnd_5226568 : Nat := 4983230072969 + 3 ^ 40 * 5226568 * 2
def baseEnd_5226568 : Nat := 894580519136137420787819

theorem tailTrace_5226568 : CollatzResearch.WordTrace tailWord_5226568 prefixEnd_5226568 894580519136137420787819 := by
  unfold tailWord_5226568
  simp only [CollatzResearch.WordTrace]
  refine ⟨95314297864522118796932179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127085730486029491729242905 95314297864522118796932179)
  ·
    refine ⟨142971446796783178195398269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95314297864522118796932179 142971446796783178195398269)
    ·
      refine ⟨53614292548793691823274351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142971446796783178195398269 53614292548793691823274351)
      ·
        refine ⟨80421438823190537734911527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53614292548793691823274351 80421438823190537734911527)
        ·
          refine ⟨120632158234785806602367291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80421438823190537734911527 120632158234785806602367291)
          ·
            refine ⟨180948237352178709903550937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120632158234785806602367291 180948237352178709903550937)
            ·
              refine ⟨135711178014134032427663203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180948237352178709903550937 135711178014134032427663203)
              ·
                refine ⟨203566767021201048641494805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135711178014134032427663203 203566767021201048641494805)
                ·
                  refine ⟨9542192204118799155070069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 203566767021201048641494805 9542192204118799155070069)
                  ·
                    refine ⟨894580519136137420787819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9542192204118799155070069 894580519136137420787819)
                    ·
                      rfl

theorem cell23_5226568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_5226568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226568 prefixEnd_5226568 := by exact prefixLift 5226568
  have htrace : WordTrace (prefixWord ++ tailWord_5226568) baseStart_5226568 baseEnd_5226568 := by
    simpa [prefixWord, tailWord_5226568, baseEnd_5226568] using wordTrace_append hprefix tailTrace_5226568
  have hstable : (prefixWord ++ tailWord_5226568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226568).length < 2 ^ (prefixWord ++ tailWord_5226568).sum := by decide
  have hdescent : baseEnd_5226568 < baseStart_5226568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226589 : List Nat := [1, 4, 4, 1, 1, 1, 3, 3, 5]
def baseStart_5226589 : Nat := 118140960795 + 5226589 * 2 ^ 59
def prefixEnd_5226589 : Nat := 4983230072969 + 3 ^ 40 * 5226589 * 2
def baseEnd_5226589 : Nat := 298194704500239631133429

theorem tailTrace_5226589 : CollatzResearch.WordTrace tailWord_5226589 prefixEnd_5226589 298194704500239631133429 := by
  unfold tailWord_5226589
  simp only [CollatzResearch.WordTrace]
  refine ⟨190629361661968158180378821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127086241107978772120252547 190629361661968158180378821)
  ·
    refine ⟨35743005311619029658821029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190629361661968158180378821 35743005311619029658821029)
    ·
      refine ⟨6701813495928568061028943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35743005311619029658821029 6701813495928568061028943)
      ·
        refine ⟨10052720243892852091543415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6701813495928568061028943 10052720243892852091543415)
        ·
          refine ⟨15079080365839278137315123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10052720243892852091543415 15079080365839278137315123)
          ·
            refine ⟨22618620548758917205972685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15079080365839278137315123 22618620548758917205972685)
            ·
              refine ⟨8481982705784593952239757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22618620548758917205972685 8481982705784593952239757)
              ·
                refine ⟨3180743514669222732089909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8481982705784593952239757 3180743514669222732089909)
                ·
                  refine ⟨298194704500239631133429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3180743514669222732089909 298194704500239631133429)
                  ·
                    rfl

theorem cell23_5226589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_5226589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226589 prefixEnd_5226589 := by exact prefixLift 5226589
  have htrace : WordTrace (prefixWord ++ tailWord_5226589) baseStart_5226589 baseEnd_5226589 := by
    simpa [prefixWord, tailWord_5226589, baseEnd_5226589] using wordTrace_append hprefix tailTrace_5226589
  have hstable : (prefixWord ++ tailWord_5226589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226589).length < 2 ^ (prefixWord ++ tailWord_5226589).sum := by decide
  have hdescent : baseEnd_5226589 < baseStart_5226589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226602 : List Nat := [3, 1, 3, 2, 3, 1, 1, 2, 2, 5]
def baseStart_5226602 : Nat := 118140960795 + 5226602 * 2 ^ 59
def prefixEnd_5226602 : Nat := 4983230072969 + 3 ^ 40 * 5226602 * 2
def baseEnd_5226602 : Nat := 894586338583555043112767

theorem tailTrace_5226602 : CollatzResearch.WordTrace tailWord_5226602 prefixEnd_5226602 894586338583555043112767 := by
  unfold tailWord_5226602
  simp only [CollatzResearch.WordTrace]
  refine ⟨47657458952730265350150515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127086557207280707600401373 47657458952730265350150515)
  ·
    refine ⟨71486188429095398025225773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47657458952730265350150515 71486188429095398025225773)
    ·
      refine ⟨26807320660910774259459665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71486188429095398025225773 26807320660910774259459665)
      ·
        refine ⟨20105490495683080694594749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26807320660910774259459665 20105490495683080694594749)
        ·
          refine ⟨7539558935881155260473031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20105490495683080694594749 7539558935881155260473031)
          ·
            refine ⟨11309338403821732890709547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7539558935881155260473031 11309338403821732890709547)
            ·
              refine ⟨16964007605732599336064321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11309338403821732890709547 16964007605732599336064321)
              ·
                refine ⟨12723005704299449502048241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16964007605732599336064321 12723005704299449502048241)
                ·
                  refine ⟨9542254278224587126536181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12723005704299449502048241 9542254278224587126536181)
                  ·
                    refine ⟨894586338583555043112767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9542254278224587126536181 894586338583555043112767)
                    ·
                      rfl

theorem cell23_5226602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_5226602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226602 prefixEnd_5226602 := by exact prefixLift 5226602
  have htrace : WordTrace (prefixWord ++ tailWord_5226602) baseStart_5226602 baseEnd_5226602 := by
    simpa [prefixWord, tailWord_5226602, baseEnd_5226602] using wordTrace_append hprefix tailTrace_5226602
  have hstable : (prefixWord ++ tailWord_5226602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226602).length < 2 ^ (prefixWord ++ tailWord_5226602).sum := by decide
  have hdescent : baseEnd_5226602 < baseStart_5226602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226682 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2]
def baseStart_5226682 : Nat := 118140960795 + 5226682 * 2 ^ 59
def prefixEnd_5226682 : Nat := 4983230072969 + 3 ^ 40 * 5226682 * 2
def baseEnd_5226682 : Nat := 2683800094203024816337933

theorem tailTrace_5226682 : CollatzResearch.WordTrace tailWord_5226682 prefixEnd_5226682 2683800094203024816337933 := by
  unfold tailWord_5226682
  simp only [CollatzResearch.WordTrace]
  refine ⟨47658188412657808765878575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127088502433754156709009533 47658188412657808765878575)
  ·
    refine ⟨71487282618986713148817863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47658188412657808765878575 71487282618986713148817863)
    ·
      refine ⟨107230923928480069723226795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71487282618986713148817863 107230923928480069723226795)
      ·
        refine ⟨160846385892720104584840193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107230923928480069723226795 160846385892720104584840193)
        ·
          refine ⟨120634789419540078438630145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160846385892720104584840193 120634789419540078438630145)
          ·
            refine ⟨90476092064655058828972609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120634789419540078438630145 90476092064655058828972609)
            ·
              refine ⟨67857069048491294121729457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90476092064655058828972609 67857069048491294121729457)
              ·
                refine ⟨50892801786368470591297093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67857069048491294121729457 50892801786368470591297093)
                ·
                  refine ⟨9542400334944088235868205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50892801786368470591297093 9542400334944088235868205)
                  ·
                    refine ⟨3578400125604033088450577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9542400334944088235868205 3578400125604033088450577)
                    ·
                      refine ⟨2683800094203024816337933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3578400125604033088450577 2683800094203024816337933)
                      ·
                        rfl

theorem cell23_5226682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2].length) (baseStart_5226682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226682 prefixEnd_5226682 := by exact prefixLift 5226682
  have htrace : WordTrace (prefixWord ++ tailWord_5226682) baseStart_5226682 baseEnd_5226682 := by
    simpa [prefixWord, tailWord_5226682, baseEnd_5226682] using wordTrace_append hprefix tailTrace_5226682
  have hstable : (prefixWord ++ tailWord_5226682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226682).length < 2 ^ (prefixWord ++ tailWord_5226682).sum := by decide
  have hdescent : baseEnd_5226682 < baseStart_5226682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226692 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 3, 5]
def baseStart_5226692 : Nat := 118140960795 + 5226692 * 2 ^ 59
def prefixEnd_5226692 : Nat := 4983230072969 + 3 ^ 40 * 5226692 * 2
def baseEnd_5226692 : Nat := 894601743003189925737629

theorem tailTrace_5226692 : CollatzResearch.WordTrace tailWord_5226692 prefixEnd_5226692 894601743003189925737629 := by
  unfold tailWord_5226692
  simp only [CollatzResearch.WordTrace]
  refine ⟨95316559190297503385689165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127088745587063337847585553 95316559190297503385689165)
  ·
    refine ⟨35743709696361563769633437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95316559190297503385689165 35743709696361563769633437)
    ·
      refine ⟨13403891136135586413612539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35743709696361563769633437 13403891136135586413612539)
      ·
        refine ⟨20105836704203379620418809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13403891136135586413612539 20105836704203379620418809)
        ·
          refine ⟨15079377528152534715314107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20105836704203379620418809 15079377528152534715314107)
          ·
            refine ⟨22619066292228802072971161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15079377528152534715314107 22619066292228802072971161)
            ·
              refine ⟨16964299719171601554728371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22619066292228802072971161 16964299719171601554728371)
              ·
                refine ⟨25446449578757402332092557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16964299719171601554728371 25446449578757402332092557)
                ·
                  refine ⟨9542418592034025874534709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25446449578757402332092557 9542418592034025874534709)
                  ·
                    refine ⟨894601743003189925737629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9542418592034025874534709 894601743003189925737629)
                    ·
                      rfl

theorem cell23_5226692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_5226692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226692 prefixEnd_5226692 := by exact prefixLift 5226692
  have htrace : WordTrace (prefixWord ++ tailWord_5226692) baseStart_5226692 baseEnd_5226692 := by
    simpa [prefixWord, tailWord_5226692, baseEnd_5226692] using wordTrace_append hprefix tailTrace_5226692
  have hstable : (prefixWord ++ tailWord_5226692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226692).length < 2 ^ (prefixWord ++ tailWord_5226692).sum := by decide
  have hdescent : baseEnd_5226692 < baseStart_5226692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226705 : List Nat := [1, 2, 2, 1, 2, 2, 4, 2, 1, 6]
def baseStart_5226705 : Nat := 118140960795 + 5226705 * 2 ^ 59
def prefixEnd_5226705 : Nat := 4983230072969 + 3 ^ 40 * 5226705 * 2
def baseEnd_5226705 : Nat := 894603968086026075450109

theorem tailTrace_5226705 : CollatzResearch.WordTrace tailWord_5226705 prefixEnd_5226705 894603968086026075450109 := by
  unfold tailWord_5226705
  simp only [CollatzResearch.WordTrace]
  refine ⟨190633592529547909991601569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127089061686365273327734379 190633592529547909991601569)
  ·
    refine ⟨142975194397160932493701177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190633592529547909991601569 142975194397160932493701177)
    ·
      refine ⟨107231395797870699370275883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142975194397160932493701177 107231395797870699370275883)
      ·
        refine ⟨160847093696806049055413825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107231395797870699370275883 160847093696806049055413825)
        ·
          refine ⟨120635320272604536791560369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160847093696806049055413825 120635320272604536791560369)
          ·
            refine ⟨90476490204453402593670277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120635320272604536791560369 90476490204453402593670277)
            ·
              refine ⟨16964341913335012986313177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90476490204453402593670277 16964341913335012986313177)
              ·
                refine ⟨12723256435001259739734883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16964341913335012986313177 12723256435001259739734883)
                ·
                  refine ⟨19084884652501889609602325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12723256435001259739734883 19084884652501889609602325)
                  ·
                    refine ⟨894603968086026075450109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19084884652501889609602325 894603968086026075450109)
                    ·
                      rfl

theorem cell23_5226705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_5226705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226705 prefixEnd_5226705 := by exact prefixLift 5226705
  have htrace : WordTrace (prefixWord ++ tailWord_5226705) baseStart_5226705 baseEnd_5226705 := by
    simpa [prefixWord, tailWord_5226705, baseEnd_5226705] using wordTrace_append hprefix tailTrace_5226705
  have hstable : (prefixWord ++ tailWord_5226705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226705).length < 2 ^ (prefixWord ++ tailWord_5226705).sum := by decide
  have hdescent : baseEnd_5226705 < baseStart_5226705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226706 : List Nat := [3, 2, 2, 2, 1, 2, 1, 5, 1, 1, 3]
def baseStart_5226706 : Nat := 118140960795 + 5226706 * 2 ^ 59
def prefixEnd_5226706 : Nat := 4983230072969 + 3 ^ 40 * 5226706 * 2
def baseEnd_5226706 : Nat := 2683812417738732722437823

theorem tailTrace_5226706 : CollatzResearch.WordTrace tailWord_5226706 prefixEnd_5226706 2683812417738732722437823 := by
  unfold tailWord_5226706
  simp only [CollatzResearch.WordTrace]
  refine ⟨47658407250636071790596993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127089086001696191441591981 47658407250636071790596993)
  ·
    refine ⟨35743805437977053842947745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47658407250636071790596993 35743805437977053842947745)
    ·
      refine ⟨26807854078482790382210809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35743805437977053842947745 26807854078482790382210809)
      ·
        refine ⟨20105890558862092786658107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26807854078482790382210809 20105890558862092786658107)
        ·
          refine ⟨30158835838293139179987161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20105890558862092786658107 30158835838293139179987161)
          ·
            refine ⟨22619126878719854384990371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30158835838293139179987161 22619126878719854384990371)
            ·
              refine ⟨33928690318079781577485557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22619126878719854384990371 33928690318079781577485557)
              ·
                refine ⟨3180814717319979522889271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33928690318079781577485557 3180814717319979522889271)
                ·
                  refine ⟨4771222075979969284333907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3180814717319979522889271 4771222075979969284333907)
                  ·
                    refine ⟨7156833113969953926500861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4771222075979969284333907 7156833113969953926500861)
                    ·
                      refine ⟨2683812417738732722437823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7156833113969953926500861 2683812417738732722437823)
                      ·
                        rfl

theorem cell23_5226706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_5226706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226706 prefixEnd_5226706 := by exact prefixLift 5226706
  have htrace : WordTrace (prefixWord ++ tailWord_5226706) baseStart_5226706 baseEnd_5226706 := by
    simpa [prefixWord, tailWord_5226706, baseEnd_5226706] using wordTrace_append hprefix tailTrace_5226706
  have hstable : (prefixWord ++ tailWord_5226706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226706).length < 2 ^ (prefixWord ++ tailWord_5226706).sum := by decide
  have hdescent : baseEnd_5226706 < baseStart_5226706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226709 : List Nat := [1, 3, 2, 4, 2, 1, 1, 3, 1, 5]
def baseStart_5226709 : Nat := 118140960795 + 5226709 * 2 ^ 59
def prefixEnd_5226709 : Nat := 4983230072969 + 3 ^ 40 * 5226709 * 2
def baseEnd_5226709 : Nat := 894604652726898736900103

theorem tailTrace_5226709 : CollatzResearch.WordTrace tailWord_5226709 prefixEnd_5226709 894604652726898736900103 := by
  unfold tailWord_5226709
  simp only [CollatzResearch.WordTrace]
  refine ⟨190633738421533418674747181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127089158947688945783164787 190633738421533418674747181)
  ·
    refine ⟨71487651908075032003030193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190633738421533418674747181 71487651908075032003030193)
    ·
      refine ⟨53615738931056274002272645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71487651908075032003030193 53615738931056274002272645)
      ·
        refine ⟨10052951049573051375426121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53615738931056274002272645 10052951049573051375426121)
        ·
          refine ⟨7539713287179788531569591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10052951049573051375426121 7539713287179788531569591)
          ·
            refine ⟨11309569930769682797354387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7539713287179788531569591 11309569930769682797354387)
            ·
              refine ⟨16964354896154524196031581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11309569930769682797354387 16964354896154524196031581)
              ·
                refine ⟨6361633086057946573511843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16964354896154524196031581 6361633086057946573511843)
                ·
                  refine ⟨9542449629086919860267765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6361633086057946573511843 9542449629086919860267765)
                  ·
                    refine ⟨894604652726898736900103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9542449629086919860267765 894604652726898736900103)
                    ·
                      rfl

theorem cell23_5226709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_5226709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226709 prefixEnd_5226709 := by exact prefixLift 5226709
  have htrace : WordTrace (prefixWord ++ tailWord_5226709) baseStart_5226709 baseEnd_5226709 := by
    simpa [prefixWord, tailWord_5226709, baseEnd_5226709] using wordTrace_append hprefix tailTrace_5226709
  have hstable : (prefixWord ++ tailWord_5226709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226709).length < 2 ^ (prefixWord ++ tailWord_5226709).sum := by decide
  have hdescent : baseEnd_5226709 < baseStart_5226709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226739 : List Nat := [1, 1, 1, 2, 2, 4, 5, 1, 2, 4]
def baseStart_5226739 : Nat := 118140960795 + 5226739 * 2 ^ 59
def prefixEnd_5226739 : Nat := 4983230072969 + 3 ^ 40 * 5226739 * 2
def baseEnd_5226739 : Nat := 894609787533443697775057

theorem tailTrace_5226739 : CollatzResearch.WordTrace tailWord_5226739 prefixEnd_5226739 894609787533443697775057 := by
  unfold tailWord_5226739
  simp only [CollatzResearch.WordTrace]
  refine ⟨190634832611424733798339271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127089888407616489198892847 190634832611424733798339271)
  ·
    refine ⟨285952248917137100697508907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190634832611424733798339271 285952248917137100697508907)
    ·
      refine ⟨428928373375705651046263361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285952248917137100697508907 428928373375705651046263361)
      ·
        refine ⟨321696280031779238284697521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428928373375705651046263361 321696280031779238284697521)
        ·
          refine ⟨241272210023834428713523141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321696280031779238284697521 241272210023834428713523141)
          ·
            refine ⟨45238539379468955383785589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 241272210023834428713523141 45238539379468955383785589)
            ·
              refine ⟨4241113066825214567229899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45238539379468955383785589 4241113066825214567229899)
              ·
                refine ⟨6361669600237821850844849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4241113066825214567229899 6361669600237821850844849)
                ·
                  refine ⟨4771252200178366388133637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6361669600237821850844849 4771252200178366388133637)
                  ·
                    refine ⟨894609787533443697775057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4771252200178366388133637 894609787533443697775057)
                    ·
                      rfl

theorem cell23_5226739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 2, 4].length) (baseStart_5226739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226739 prefixEnd_5226739 := by exact prefixLift 5226739
  have htrace : WordTrace (prefixWord ++ tailWord_5226739) baseStart_5226739 baseEnd_5226739 := by
    simpa [prefixWord, tailWord_5226739, baseEnd_5226739] using wordTrace_append hprefix tailTrace_5226739
  have hstable : (prefixWord ++ tailWord_5226739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226739).length < 2 ^ (prefixWord ++ tailWord_5226739).sum := by decide
  have hdescent : baseEnd_5226739 < baseStart_5226739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226762 : List Nat := [3, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3]
def baseStart_5226762 : Nat := 118140960795 + 5226762 * 2 ^ 59
def prefixEnd_5226762 : Nat := 4983230072969 + 3 ^ 40 * 5226762 * 2
def baseEnd_5226762 : Nat := 2683841172655384503337565

theorem tailTrace_5226762 : CollatzResearch.WordTrace tailWord_5226762 prefixEnd_5226762 2683841172655384503337565 := by
  unfold tailWord_5226762
  simp only [CollatzResearch.WordTrace]
  refine ⟨47658917872585352181606635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127090447660227605817617693 47658917872585352181606635)
  ·
    refine ⟨71488376808878028272409953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47658917872585352181606635 71488376808878028272409953)
    ·
      refine ⟨53616282606658521204307465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71488376808878028272409953 53616282606658521204307465)
      ·
        refine ⟨40212211954993890903230599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53616282606658521204307465 40212211954993890903230599)
        ·
          refine ⟨60318317932490836354845899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40212211954993890903230599 60318317932490836354845899)
          ·
            refine ⟨90477476898736254532268849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60318317932490836354845899 90477476898736254532268849)
            ·
              refine ⟨67858107674052190899201637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90477476898736254532268849 67858107674052190899201637)
              ·
                refine ⟨12723395188884785793600307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67858107674052190899201637 12723395188884785793600307)
                ·
                  refine ⟨19085092783327178690400461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12723395188884785793600307 19085092783327178690400461)
                  ·
                    refine ⟨7156909793747692008900173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19085092783327178690400461 7156909793747692008900173)
                    ·
                      refine ⟨2683841172655384503337565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7156909793747692008900173 2683841172655384503337565)
                      ·
                        rfl

theorem cell23_5226762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_5226762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226762 prefixEnd_5226762 := by exact prefixLift 5226762
  have htrace : WordTrace (prefixWord ++ tailWord_5226762) baseStart_5226762 baseEnd_5226762 := by
    simpa [prefixWord, tailWord_5226762, baseEnd_5226762] using wordTrace_append hprefix tailTrace_5226762
  have hstable : (prefixWord ++ tailWord_5226762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226762).length < 2 ^ (prefixWord ++ tailWord_5226762).sum := by decide
  have hdescent : baseEnd_5226762 < baseStart_5226762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226796 : List Nat := [2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 3]
def baseStart_5226796 : Nat := 118140960795 + 5226796 * 2 ^ 59
def prefixEnd_5226796 : Nat := 4983230072969 + 3 ^ 40 * 5226796 * 2
def baseEnd_5226796 : Nat := 2683858630997637370312409

theorem tailTrace_5226796 : CollatzResearch.WordTrace tailWord_5226796 prefixEnd_5226796 2683858630997637370312409 := by
  unfold tailWord_5226796
  simp only [CollatzResearch.WordTrace]
  refine ⟨95318455786109116266582121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127091274381478821688776161 95318455786109116266582121)
  ·
    refine ⟨71488841839581837199936591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95318455786109116266582121 71488841839581837199936591)
    ·
      refine ⟨107233262759372755799904887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71488841839581837199936591 107233262759372755799904887)
      ·
        refine ⟨160849894139059133699857331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107233262759372755799904887 160849894139059133699857331)
        ·
          refine ⟨241274841208588700549785997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160849894139059133699857331 241274841208588700549785997)
          ·
            refine ⟨90478065453220762706169749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 241274841208588700549785997 90478065453220762706169749)
            ·
              refine ⟨4241159318119723251851707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90478065453220762706169749 4241159318119723251851707)
              ·
                refine ⟨6361738977179584877777561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4241159318119723251851707 6361738977179584877777561)
                ·
                  refine ⟨4771304232884688658333171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6361738977179584877777561 4771304232884688658333171)
                  ·
                    refine ⟨7156956349327032987499757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4771304232884688658333171 7156956349327032987499757)
                    ·
                      refine ⟨2683858630997637370312409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7156956349327032987499757 2683858630997637370312409)
                      ·
                        rfl

theorem cell23_5226796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 3].length) (baseStart_5226796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226796 prefixEnd_5226796 := by exact prefixLift 5226796
  have htrace : WordTrace (prefixWord ++ tailWord_5226796) baseStart_5226796 baseEnd_5226796 := by
    simpa [prefixWord, tailWord_5226796, baseEnd_5226796] using wordTrace_append hprefix tailTrace_5226796
  have hstable : (prefixWord ++ tailWord_5226796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226796).length < 2 ^ (prefixWord ++ tailWord_5226796).sum := by decide
  have hdescent : baseEnd_5226796 < baseStart_5226796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226819 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 6, 2, 2]
def baseStart_5226819 : Nat := 118140960795 + 5226819 * 2 ^ 59
def prefixEnd_5226819 : Nat := 4983230072969 + 3 ^ 40 * 5226819 * 2
def baseEnd_5226819 : Nat := 2683870441052690780324803

theorem tailTrace_5226819 : CollatzResearch.WordTrace tailWord_5226819 prefixEnd_5226819 2683870441052690780324803 := by
  unfold tailWord_5226819
  simp only [CollatzResearch.WordTrace]
  refine ⟨190637750451134907461251511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127091833634089938307501007 190637750451134907461251511)
  ·
    refine ⟨285956625676702361191877267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190637750451134907461251511 285956625676702361191877267)
    ·
      refine ⟨428934938515053541787815901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285956625676702361191877267 428934938515053541787815901)
      ·
        refine ⟨160850601943145078170430963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 428934938515053541787815901 160850601943145078170430963)
        ·
          refine ⟨241275902914717617255646445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160850601943145078170430963 241275902914717617255646445)
          ·
            refine ⟨90478463593019106470867417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 241275902914717617255646445 90478463593019106470867417)
            ·
              refine ⟨67858847694764329853150563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90478463593019106470867417 67858847694764329853150563)
              ·
                refine ⟨101788271542146494779725845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67858847694764329853150563 101788271542146494779725845)
                ·
                  refine ⟨4771325228538116942799649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 101788271542146494779725845 4771325228538116942799649)
                  ·
                    refine ⟨3578493921403587707099737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4771325228538116942799649 3578493921403587707099737)
                    ·
                      refine ⟨2683870441052690780324803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3578493921403587707099737 2683870441052690780324803)
                      ·
                        rfl

theorem cell23_5226819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 2, 2].length) (baseStart_5226819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226819 prefixEnd_5226819 := by exact prefixLift 5226819
  have htrace : WordTrace (prefixWord ++ tailWord_5226819) baseStart_5226819 baseEnd_5226819 := by
    simpa [prefixWord, tailWord_5226819, baseEnd_5226819] using wordTrace_append hprefix tailTrace_5226819
  have hstable : (prefixWord ++ tailWord_5226819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226819).length < 2 ^ (prefixWord ++ tailWord_5226819).sum := by decide
  have hdescent : baseEnd_5226819 < baseStart_5226819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226929 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 1, 4, 3]
def baseStart_5226929 : Nat := 118140960795 + 5226929 * 2 ^ 59
def prefixEnd_5226929 : Nat := 4983230072969 + 3 ^ 40 * 5226929 * 2
def baseEnd_5226929 : Nat := 2683926923924685349949297

theorem tailTrace_5226929 : CollatzResearch.WordTrace tailWord_5226929 prefixEnd_5226929 2683926923924685349949297 := by
  unfold tailWord_5226929
  simp only [CollatzResearch.WordTrace]
  refine ⟨190641762480736396247755841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127094508320490930831837227 190641762480736396247755841)
  ·
    refine ⟨142981321860552297185816881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190641762480736396247755841 142981321860552297185816881)
    ·
      refine ⟨107235991395414222889362661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142981321860552297185816881 107235991395414222889362661)
      ·
        refine ⟨20106748386640166791755499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107235991395414222889362661 20106748386640166791755499)
        ·
          refine ⟨30160122579960250187633249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20106748386640166791755499 30160122579960250187633249)
          ·
            refine ⟨22620091934970187640724937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30160122579960250187633249 22620091934970187640724937)
            ·
              refine ⟨16965068951227640730543703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22620091934970187640724937 16965068951227640730543703)
              ·
                refine ⟨25447603426841461095815555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16965068951227640730543703 25447603426841461095815555)
                ·
                  refine ⟨38171405140262191643723333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25447603426841461095815555 38171405140262191643723333)
                  ·
                    refine ⟨7157138463799160933198125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38171405140262191643723333 7157138463799160933198125)
                    ·
                      refine ⟨2683926923924685349949297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7157138463799160933198125 2683926923924685349949297)
                      ·
                        rfl

theorem cell23_5226929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_5226929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226929 prefixEnd_5226929 := by exact prefixLift 5226929
  have htrace : WordTrace (prefixWord ++ tailWord_5226929) baseStart_5226929 baseEnd_5226929 := by
    simpa [prefixWord, tailWord_5226929, baseEnd_5226929] using wordTrace_append hprefix tailTrace_5226929
  have hstable : (prefixWord ++ tailWord_5226929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226929).length < 2 ^ (prefixWord ++ tailWord_5226929).sum := by decide
  have hdescent : baseEnd_5226929 < baseStart_5226929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226966 : List Nat := [5, 2, 1, 1, 1, 1, 3, 3, 6]
def baseStart_5226966 : Nat := 118140960795 + 5226966 * 2 ^ 59
def prefixEnd_5226966 : Nat := 4983230072969 + 3 ^ 40 * 5226966 * 2
def baseEnd_5226966 : Nat := 298216213634322411687403

theorem tailTrace_5226966 : CollatzResearch.WordTrace tailWord_5226966 prefixEnd_5226966 298216213634322411687403 := by
  unfold tailWord_5226966
  simp only [CollatzResearch.WordTrace]
  refine ⟨11915194498850146972928297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127095407987734901044568501 11915194498850146972928297)
  ·
    refine ⟨8936395874137610229696223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11915194498850146972928297 8936395874137610229696223)
    ·
      refine ⟨13404593811206415344544335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8936395874137610229696223 13404593811206415344544335)
      ·
        refine ⟨20106890716809623016816503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13404593811206415344544335 20106890716809623016816503)
        ·
          refine ⟨30160336075214434525224755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20106890716809623016816503 30160336075214434525224755)
          ·
            refine ⟨45240504112821651787837133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30160336075214434525224755 45240504112821651787837133)
            ·
              refine ⟨16965189042308119420438925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45240504112821651787837133 16965189042308119420438925)
              ·
                refine ⟨6361945890865544782664597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16965189042308119420438925 6361945890865544782664597)
                ·
                  refine ⟨298216213634322411687403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6361945890865544782664597 298216213634322411687403)
                  ·
                    rfl

theorem cell23_5226966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_5226966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226966 prefixEnd_5226966 := by exact prefixLift 5226966
  have htrace : WordTrace (prefixWord ++ tailWord_5226966) baseStart_5226966 baseEnd_5226966 := by
    simpa [prefixWord, tailWord_5226966, baseEnd_5226966] using wordTrace_append hprefix tailTrace_5226966
  have hstable : (prefixWord ++ tailWord_5226966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226966).length < 2 ^ (prefixWord ++ tailWord_5226966).sum := by decide
  have hdescent : baseEnd_5226966 < baseStart_5226966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226993 : List Nat := [1, 2, 2, 2, 3, 1, 2, 5, 1, 1, 3]
def baseStart_5226993 : Nat := 118140960795 + 5226993 * 2 ^ 59
def prefixEnd_5226993 : Nat := 4983230072969 + 3 ^ 40 * 5226993 * 2
def baseEnd_5226993 : Nat := 2683959786686573099549003

theorem tailTrace_5226993 : CollatzResearch.WordTrace tailWord_5226993 prefixEnd_5226993 2683959786686573099549003 := by
  unfold tailWord_5226993
  simp only [CollatzResearch.WordTrace]
  refine ⟨190644096752504535178085633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127096064501669690118723755 190644096752504535178085633)
  ·
    refine ⟨142983072564378401383564225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190644096752504535178085633 142983072564378401383564225)
    ·
      refine ⟨107237304423283801037673169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142983072564378401383564225 107237304423283801037673169)
      ·
        refine ⟨80427978317462850778254877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107237304423283801037673169 80427978317462850778254877)
        ·
          refine ⟨30160491869048569041845579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80427978317462850778254877 30160491869048569041845579)
          ·
            refine ⟨45240737803572853562768369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30160491869048569041845579 45240737803572853562768369)
            ·
              refine ⟨33930553352679640172076277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45240737803572853562768369 33930553352679640172076277)
              ·
                refine ⟨3180989376813716266132151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33930553352679640172076277 3180989376813716266132151)
                ·
                  refine ⟨4771484065220574399198227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3180989376813716266132151 4771484065220574399198227)
                  ·
                    refine ⟨7157226097830861598797341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4771484065220574399198227 7157226097830861598797341)
                    ·
                      refine ⟨2683959786686573099549003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7157226097830861598797341 2683959786686573099549003)
                      ·
                        rfl

theorem cell23_5226993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 1, 1, 3].length) (baseStart_5226993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226993 prefixEnd_5226993 := by exact prefixLift 5226993
  have htrace : WordTrace (prefixWord ++ tailWord_5226993) baseStart_5226993 baseEnd_5226993 := by
    simpa [prefixWord, tailWord_5226993, baseEnd_5226993] using wordTrace_append hprefix tailTrace_5226993
  have hstable : (prefixWord ++ tailWord_5226993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226993).length < 2 ^ (prefixWord ++ tailWord_5226993).sum := by decide
  have hdescent : baseEnd_5226993 < baseStart_5226993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226999 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 4, 6, 2]
def baseStart_5226999 : Nat := 118140960795 + 5226999 * 2 ^ 59
def prefixEnd_5226999 : Nat := 4983230072969 + 3 ^ 40 * 5226999 * 2
def baseEnd_5226999 : Nat := 2683962867570500076073975

theorem tailTrace_5226999 : CollatzResearch.WordTrace tailWord_5226999 prefixEnd_5226999 2683962867570500076073975 := by
  unfold tailWord_5226999
  simp only [CollatzResearch.WordTrace]
  refine ⟨190644315590482798202804051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127096210393655198801869367 190644315590482798202804051)
  ·
    refine ⟨285966473385724197304206077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190644315590482798202804051 285966473385724197304206077)
    ·
      refine ⟨107237427519646573989077279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285966473385724197304206077 107237427519646573989077279)
      ·
        refine ⟨160856141279469860983615919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107237427519646573989077279 160856141279469860983615919)
        ·
          refine ⟨241284211919204791475423879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160856141279469860983615919 241284211919204791475423879)
          ·
            refine ⟨361926317878807187213135819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241284211919204791475423879 361926317878807187213135819)
            ·
              refine ⟨542889476818210780819703729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361926317878807187213135819 542889476818210780819703729)
              ·
                refine ⟨407167107613658085614777797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 542889476818210780819703729 407167107613658085614777797)
                ·
                  refine ⟨76343832677560891052770837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 407167107613658085614777797 76343832677560891052770837)
                  ·
                    refine ⟨3578617156760666768098633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76343832677560891052770837 3578617156760666768098633)
                    ·
                      refine ⟨2683962867570500076073975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3578617156760666768098633 2683962867570500076073975)
                      ·
                        rfl

theorem cell23_5226999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 6, 2].length) (baseStart_5226999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5226999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5226999 prefixEnd_5226999 := by exact prefixLift 5226999
  have htrace : WordTrace (prefixWord ++ tailWord_5226999) baseStart_5226999 baseEnd_5226999 := by
    simpa [prefixWord, tailWord_5226999, baseEnd_5226999] using wordTrace_append hprefix tailTrace_5226999
  have hstable : (prefixWord ++ tailWord_5226999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226999).length < 2 ^ (prefixWord ++ tailWord_5226999).sum := by decide
  have hdescent : baseEnd_5226999 < baseStart_5226999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227036 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 3, 2, 3]
def baseStart_5227036 : Nat := 118140960795 + 5227036 * 2 ^ 59
def prefixEnd_5227036 : Nat := 4983230072969 + 3 ^ 40 * 5227036 * 2
def baseEnd_5227036 : Nat := 2683981866354716431311305

theorem tailTrace_5227036 : CollatzResearch.WordTrace tailWord_5227036 prefixEnd_5227036 2683981866354716431311305 := by
  unfold tailWord_5227036
  simp only [CollatzResearch.WordTrace]
  refine ⟨95322832545674376760950481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127097110060899169014600641 95322832545674376760950481)
  ·
    refine ⟨71492124409255782570712861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95322832545674376760950481 71492124409255782570712861)
    ·
      refine ⟨26809546653470918464017323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71492124409255782570712861 26809546653470918464017323)
      ·
        refine ⟨40214319980206377696025985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26809546653470918464017323 40214319980206377696025985)
        ·
          refine ⟨30160739985154783272019489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40214319980206377696025985 30160739985154783272019489)
          ·
            refine ⟨22620554988866087454014617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30160739985154783272019489 22620554988866087454014617)
            ·
              refine ⟨16965416241649565590510963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22620554988866087454014617 16965416241649565590510963)
              ·
                refine ⟨25448124362474348385766445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16965416241649565590510963 25448124362474348385766445)
                ·
                  refine ⟨9543046635927880644662417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25448124362474348385766445 9543046635927880644662417)
                  ·
                    refine ⟨7157284976945910483496813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9543046635927880644662417 7157284976945910483496813)
                    ·
                      refine ⟨2683981866354716431311305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7157284976945910483496813 2683981866354716431311305)
                      ·
                        rfl

theorem cell23_5227036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_5227036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227036 prefixEnd_5227036 := by exact prefixLift 5227036
  have htrace : WordTrace (prefixWord ++ tailWord_5227036) baseStart_5227036 baseEnd_5227036 := by
    simpa [prefixWord, tailWord_5227036, baseEnd_5227036] using wordTrace_append hprefix tailTrace_5227036
  have hstable : (prefixWord ++ tailWord_5227036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227036).length < 2 ^ (prefixWord ++ tailWord_5227036).sum := by decide
  have hdescent : baseEnd_5227036 < baseStart_5227036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227047 : List Nat := [1, 1, 7, 2, 1, 2, 2, 1, 1, 5]
def baseStart_5227047 : Nat := 118140960795 + 5227047 * 2 ^ 59
def prefixEnd_5227047 : Nat := 4983230072969 + 3 ^ 40 * 5227047 * 2
def baseEnd_5227047 : Nat := 894662504880638629424585

theorem tailTrace_5227047 : CollatzResearch.WordTrace tailWord_5227047 prefixEnd_5227047 894662504880638629424585 := by
  unfold tailWord_5227047
  simp only [CollatzResearch.WordTrace]
  refine ⟨190646066294308902400551395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127097377529539268267034263 190646066294308902400551395)
  ·
    refine ⟨285969099441463353600827093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190646066294308902400551395 285969099441463353600827093)
    ·
      refine ⟨6702400768159297350019385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 285969099441463353600827093 6702400768159297350019385)
      ·
        refine ⟨5026800576119473012514539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6702400768159297350019385 5026800576119473012514539)
        ·
          refine ⟨7540200864179209518771809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5026800576119473012514539 7540200864179209518771809)
          ·
            refine ⟨5655150648134407139078857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7540200864179209518771809 5655150648134407139078857)
            ·
              refine ⟨4241362986100805354309143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5655150648134407139078857 4241362986100805354309143)
              ·
                refine ⟨6362044479151208031463715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4241362986100805354309143 6362044479151208031463715)
                ·
                  refine ⟨9543066718726812047195573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6362044479151208031463715 9543066718726812047195573)
                  ·
                    refine ⟨894662504880638629424585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9543066718726812047195573 894662504880638629424585)
                    ·
                      rfl

theorem cell23_5227047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_5227047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227047 prefixEnd_5227047 := by exact prefixLift 5227047
  have htrace : WordTrace (prefixWord ++ tailWord_5227047) baseStart_5227047 baseEnd_5227047 := by
    simpa [prefixWord, tailWord_5227047, baseEnd_5227047] using wordTrace_append hprefix tailTrace_5227047
  have hstable : (prefixWord ++ tailWord_5227047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227047).length < 2 ^ (prefixWord ++ tailWord_5227047).sum := by decide
  have hdescent : baseEnd_5227047 < baseStart_5227047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227050 : List Nat := [3, 1, 4, 1, 1, 4, 2, 1, 1, 1, 4]
def baseStart_5227050 : Nat := 118140960795 + 5227050 * 2 ^ 59
def prefixEnd_5227050 : Nat := 4983230072969 + 3 ^ 40 * 5227050 * 2
def baseEnd_5227050 : Nat := 2683989055083879376536241

theorem tailTrace_5227050 : CollatzResearch.WordTrace tailWord_5227050 prefixEnd_5227050 2683989055083879376536241 := by
  unfold tailWord_5227050
  simp only [CollatzResearch.WordTrace]
  refine ⟨47661543928324508478227651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127097450475532022608607069 47661543928324508478227651)
  ·
    refine ⟨71492315892486762717341477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47661543928324508478227651 71492315892486762717341477)
    ·
      refine ⟨13404809229841268009501527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71492315892486762717341477 13404809229841268009501527)
      ·
        refine ⟨20107213844761902014252291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13404809229841268009501527 20107213844761902014252291)
        ·
          refine ⟨30160820767142853021378437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20107213844761902014252291 30160820767142853021378437)
          ·
            refine ⟨5655153893839284941508457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30160820767142853021378437 5655153893839284941508457)
            ·
              refine ⟨4241365420379463706131343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5655153893839284941508457 4241365420379463706131343)
              ·
                refine ⟨6362048130569195559197015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4241365420379463706131343 6362048130569195559197015)
                ·
                  refine ⟨9543072195853793338795523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6362048130569195559197015 9543072195853793338795523)
                  ·
                    refine ⟨14314608293780690008193285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9543072195853793338795523 14314608293780690008193285)
                    ·
                      refine ⟨2683989055083879376536241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14314608293780690008193285 2683989055083879376536241)
                      ·
                        rfl

theorem cell23_5227050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_5227050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227050 prefixEnd_5227050 := by exact prefixLift 5227050
  have htrace : WordTrace (prefixWord ++ tailWord_5227050) baseStart_5227050 baseEnd_5227050 := by
    simpa [prefixWord, tailWord_5227050, baseEnd_5227050] using wordTrace_append hprefix tailTrace_5227050
  have hstable : (prefixWord ++ tailWord_5227050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227050).length < 2 ^ (prefixWord ++ tailWord_5227050).sum := by decide
  have hdescent : baseEnd_5227050 < baseStart_5227050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227060 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_5227060 : Nat := 118140960795 + 5227060 * 2 ^ 59
def prefixEnd_5227060 : Nat := 4983230072969 + 3 ^ 40 * 5227060 * 2
def baseEnd_5227060 : Nat := 894664729963474779137065

theorem tailTrace_5227060 : CollatzResearch.WordTrace tailWord_5227060 prefixEnd_5227060 894664729963474779137065 := by
  unfold tailWord_5227060
  simp only [CollatzResearch.WordTrace]
  refine ⟨95323270221630902810387317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127097693628841203747183089 95323270221630902810387317)
  ·
    refine ⟨8936556583277897138473811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95323270221630902810387317 8936556583277897138473811)
    ·
      refine ⟨13404834874916845707710717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8936556583277897138473811 13404834874916845707710717)
      ·
        refine ⟨5026813078093817140391519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13404834874916845707710717 5026813078093817140391519)
        ·
          refine ⟨7540219617140725710587279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5026813078093817140391519 7540219617140725710587279)
          ·
            refine ⟨11310329425711088565880919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7540219617140725710587279 11310329425711088565880919)
            ·
              refine ⟨16965494138566632848821379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11310329425711088565880919 16965494138566632848821379)
              ·
                refine ⟨25448241207849949273232069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16965494138566632848821379 25448241207849949273232069)
                ·
                  refine ⟨4771545226471865488731013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25448241207849949273232069 4771545226471865488731013)
                  ·
                    refine ⟨894664729963474779137065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4771545226471865488731013 894664729963474779137065)
                    ·
                      rfl

theorem cell23_5227060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_5227060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227060 prefixEnd_5227060 := by exact prefixLift 5227060
  have htrace : WordTrace (prefixWord ++ tailWord_5227060) baseStart_5227060 baseEnd_5227060 := by
    simpa [prefixWord, tailWord_5227060, baseEnd_5227060] using wordTrace_append hprefix tailTrace_5227060
  have hstable : (prefixWord ++ tailWord_5227060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227060).length < 2 ^ (prefixWord ++ tailWord_5227060).sum := by decide
  have hdescent : baseEnd_5227060 < baseStart_5227060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227093 : List Nat := [1, 3, 2, 2, 1, 1, 3, 4, 1, 3, 2]
def baseStart_5227093 : Nat := 118140960795 + 5227093 * 2 ^ 59
def prefixEnd_5227093 : Nat := 4983230072969 + 3 ^ 40 * 5227093 * 2
def baseEnd_5227093 : Nat := 2684011134752022708298543

theorem tailTrace_5227093 : CollatzResearch.WordTrace tailWord_5227093 prefixEnd_5227093 2684011134752022708298543 := by
  unfold tailWord_5227093
  simp only [CollatzResearch.WordTrace]
  refine ⟨190647744052142252256725933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127098496034761501504483955 190647744052142252256725933)
  ·
    refine ⟨71492904019553344596272225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190647744052142252256725933 71492904019553344596272225)
    ·
      refine ⟨53619678014665008447204169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71492904019553344596272225 53619678014665008447204169)
      ·
        refine ⟨40214758510998756335403127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53619678014665008447204169 40214758510998756335403127)
        ·
          refine ⟨60322137766498134503104691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40214758510998756335403127 60322137766498134503104691)
          ·
            refine ⟨90483206649747201754657037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60322137766498134503104691 90483206649747201754657037)
            ·
              refine ⟨33931202493655200657996389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90483206649747201754657037 33931202493655200657996389)
              ·
                refine ⟨6362100467560350123374323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33931202493655200657996389 6362100467560350123374323)
                ·
                  refine ⟨9543150701340525185061485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6362100467560350123374323 9543150701340525185061485)
                  ·
                    refine ⟨3578681513002696944398057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9543150701340525185061485 3578681513002696944398057)
                    ·
                      refine ⟨2684011134752022708298543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3578681513002696944398057 2684011134752022708298543)
                      ·
                        rfl

theorem cell23_5227093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_5227093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227093 prefixEnd_5227093 := by exact prefixLift 5227093
  have htrace : WordTrace (prefixWord ++ tailWord_5227093) baseStart_5227093 baseEnd_5227093 := by
    simpa [prefixWord, tailWord_5227093, baseEnd_5227093] using wordTrace_append hprefix tailTrace_5227093
  have hstable : (prefixWord ++ tailWord_5227093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227093).length < 2 ^ (prefixWord ++ tailWord_5227093).sum := by decide
  have hdescent : baseEnd_5227093 < baseStart_5227093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227119 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 4]
def baseStart_5227119 : Nat := 118140960795 + 5227119 * 2 ^ 59
def prefixEnd_5227119 : Nat := 4983230072969 + 3 ^ 40 * 5227119 * 2
def baseEnd_5227119 : Nat := 2684024485249039606573423

theorem tailTrace_5227119 : CollatzResearch.WordTrace tailWord_5227119 prefixEnd_5227119 2684024485249039606573423 := by
  unfold tailWord_5227119
  simp only [CollatzResearch.WordTrace]
  refine ⟨190648692350048058697172411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127099128233365372464781607 190648692350048058697172411)
  ·
    refine ⟨285973038525072088045758617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190648692350048058697172411 285973038525072088045758617)
    ·
      refine ⟨214479778893804066034318963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285973038525072088045758617 214479778893804066034318963)
      ·
        refine ⟨321719668340706099051478445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214479778893804066034318963 321719668340706099051478445)
        ·
          refine ⟨120644875627764787144304417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 321719668340706099051478445 120644875627764787144304417)
          ·
            refine ⟨90483656720823590358228313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120644875627764787144304417 90483656720823590358228313)
            ·
              refine ⟨67862742540617692768671235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90483656720823590358228313 67862742540617692768671235)
              ·
                refine ⟨101794113810926539153006853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67862742540617692768671235 101794113810926539153006853)
                ·
                  refine ⟨19086396339548726091188785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101794113810926539153006853 19086396339548726091188785)
                  ·
                    refine ⟨14314797254661544568391589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19086396339548726091188785 14314797254661544568391589)
                    ·
                      refine ⟨2684024485249039606573423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14314797254661544568391589 2684024485249039606573423)
                      ·
                        rfl

theorem cell23_5227119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 4].length) (baseStart_5227119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227119 prefixEnd_5227119 := by exact prefixLift 5227119
  have htrace : WordTrace (prefixWord ++ tailWord_5227119) baseStart_5227119 baseEnd_5227119 := by
    simpa [prefixWord, tailWord_5227119, baseEnd_5227119] using wordTrace_append hprefix tailTrace_5227119
  have hstable : (prefixWord ++ tailWord_5227119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227119).length < 2 ^ (prefixWord ++ tailWord_5227119).sum := by decide
  have hdescent : baseEnd_5227119 < baseStart_5227119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227196 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 1, 3, 4]
def baseStart_5227196 : Nat := 118140960795 + 5227196 * 2 ^ 59
def prefixEnd_5227196 : Nat := 4983230072969 + 3 ^ 40 * 5227196 * 2
def baseEnd_5227196 : Nat := 2684064023259435805310569

theorem tailTrace_5227196 : CollatzResearch.WordTrace tailWord_5227196 prefixEnd_5227196 2684064023259435805310569 := by
  unfold tailWord_5227196
  simp only [CollatzResearch.WordTrace]
  refine ⟨95325750385384550423862721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127101000513846067231816961 95325750385384550423862721)
  ·
    refine ⟨71494312789038412817897041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95325750385384550423862721 71494312789038412817897041)
    ·
      refine ⟨53620734591778809613422781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71494312789038412817897041 53620734591778809613422781)
      ·
        refine ⟨20107775471917053605033543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53620734591778809613422781 20107775471917053605033543)
        ·
          refine ⟨30161663207875580407550315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20107775471917053605033543 30161663207875580407550315)
          ·
            refine ⟨45242494811813370611325473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30161663207875580407550315 45242494811813370611325473)
            ·
              refine ⟨33931871108860027958494105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45242494811813370611325473 33931871108860027958494105)
              ·
                refine ⟨25448903331645020968870579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33931871108860027958494105 25448903331645020968870579)
                ·
                  refine ⟨38173354997467531453305869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25448903331645020968870579 38173354997467531453305869)
                  ·
                    refine ⟨14315008124050324294989701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38173354997467531453305869 14315008124050324294989701)
                    ·
                      refine ⟨2684064023259435805310569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14315008124050324294989701 2684064023259435805310569)
                      ·
                        rfl

theorem cell23_5227196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_5227196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227196 prefixEnd_5227196 := by exact prefixLift 5227196
  have htrace : WordTrace (prefixWord ++ tailWord_5227196) baseStart_5227196 baseEnd_5227196 := by
    simpa [prefixWord, tailWord_5227196, baseEnd_5227196] using wordTrace_append hprefix tailTrace_5227196
  have hstable : (prefixWord ++ tailWord_5227196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227196).length < 2 ^ (prefixWord ++ tailWord_5227196).sum := by decide
  have hdescent : baseEnd_5227196 < baseStart_5227196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227209 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 6, 1, 6]
def baseStart_5227209 : Nat := 118140960795 + 5227209 * 2 ^ 59
def prefixEnd_5227209 : Nat := 4983230072969 + 3 ^ 40 * 5227209 * 2
def baseEnd_5227209 : Nat := 2684070698507944254448009

theorem tailTrace_5227209 : CollatzResearch.WordTrace tailWord_5227209 prefixEnd_5227209 2684070698507944254448009 := by
  unfold tailWord_5227209
  simp only [CollatzResearch.WordTrace]
  refine ⟨190651974919722004067948681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127101316613148002711965787 190651974919722004067948681)
  ·
    refine ⟨142988981189791503050961511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190651974919722004067948681 142988981189791503050961511)
    ·
      refine ⟨214483471784687254576442267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142988981189791503050961511 214483471784687254576442267)
      ·
        refine ⟨321725207677030881864663401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214483471784687254576442267 321725207677030881864663401)
        ·
          refine ⟨241293905757773161398497551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321725207677030881864663401 241293905757773161398497551)
          ·
            refine ⟨361940858636659742097746327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241293905757773161398497551 361940858636659742097746327)
            ·
              refine ⟨542911287954989613146619491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361940858636659742097746327 542911287954989613146619491)
              ·
                refine ⟨814366931932484419719929237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 542911287954989613146619491 814366931932484419719929237)
                ·
                  refine ⟨38173449934335207174371683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 814366931932484419719929237 38173449934335207174371683)
                  ·
                    refine ⟨57260174901502810761557525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38173449934335207174371683 57260174901502810761557525)
                    ·
                      refine ⟨2684070698507944254448009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57260174901502810761557525 2684070698507944254448009)
                      ·
                        rfl

theorem cell23_5227209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_5227209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227209 prefixEnd_5227209 := by exact prefixLift 5227209
  have htrace : WordTrace (prefixWord ++ tailWord_5227209) baseStart_5227209 baseEnd_5227209 := by
    simpa [prefixWord, tailWord_5227209, baseEnd_5227209] using wordTrace_append hprefix tailTrace_5227209
  have hstable : (prefixWord ++ tailWord_5227209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227209).length < 2 ^ (prefixWord ++ tailWord_5227209).sum := by decide
  have hdescent : baseEnd_5227209 < baseStart_5227209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227236 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 8]
def baseStart_5227236 : Nat := 118140960795 + 5227236 * 2 ^ 59
def prefixEnd_5227236 : Nat := 4983230072969 + 3 ^ 40 * 5227236 * 2
def baseEnd_5227236 : Nat := 298231618053957294312265

theorem tailTrace_5227236 : CollatzResearch.WordTrace tailWord_5227236 prefixEnd_5227236 298231618053957294312265 := by
  unfold tailWord_5227236
  simp only [CollatzResearch.WordTrace]
  refine ⟨95326479845312093839590781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127101973127082791786121041 95326479845312093839590781)
  ·
    refine ⟨35747429941992035189846543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95326479845312093839590781 35747429941992035189846543)
    ·
      refine ⟨53621144912988052784769815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35747429941992035189846543 53621144912988052784769815)
      ·
        refine ⟨80431717369482079177154723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53621144912988052784769815 80431717369482079177154723)
        ·
          refine ⟨120647576054223118765732085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80431717369482079177154723 120647576054223118765732085)
          ·
            refine ⟨11310710255083417384287383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120647576054223118765732085 11310710255083417384287383)
            ·
              refine ⟨16966065382625126076431075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11310710255083417384287383 16966065382625126076431075)
              ·
                refine ⟨25449098073937689114646613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16966065382625126076431075 25449098073937689114646613)
                ·
                  refine ⟨298231618053957294312265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25449098073937689114646613 298231618053957294312265)
                  ·
                    rfl

theorem cell23_5227236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_5227236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227236 prefixEnd_5227236 := by exact prefixLift 5227236
  have htrace : WordTrace (prefixWord ++ tailWord_5227236) baseStart_5227236 baseEnd_5227236 := by
    simpa [prefixWord, tailWord_5227236, baseEnd_5227236] using wordTrace_append hprefix tailTrace_5227236
  have hstable : (prefixWord ++ tailWord_5227236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227236).length < 2 ^ (prefixWord ++ tailWord_5227236).sum := by decide
  have hdescent : baseEnd_5227236 < baseStart_5227236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227240 : List Nat := [2, 1, 4, 1, 4, 1, 2, 1, 3, 4]
def baseStart_5227240 : Nat := 118140960795 + 5227240 * 2 ^ 59
def prefixEnd_5227240 : Nat := 4983230072969 + 3 ^ 40 * 5227240 * 2
def baseEnd_5227240 : Nat := 894695538802744544386789

theorem tailTrace_5227240 : CollatzResearch.WordTrace tailWord_5227240 prefixEnd_5227240 894695538802744544386789 := by
  unfold tailWord_5227240
  simp only [CollatzResearch.WordTrace]
  refine ⟨95326552791304848181163587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127102070388406464241551449 95326552791304848181163587)
  ·
    refine ⟨142989829186957272271745381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95326552791304848181163587 142989829186957272271745381)
    ·
      refine ⟨26810592972554488550952259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142989829186957272271745381 26810592972554488550952259)
      ·
        refine ⟨40215889458831732826428389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26810592972554488550952259 40215889458831732826428389)
        ·
          refine ⟨7540479273530949904955323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40215889458831732826428389 7540479273530949904955323)
          ·
            refine ⟨11310718910296424857432985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7540479273530949904955323 11310718910296424857432985)
            ·
              refine ⟨8483039182722318643074739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11310718910296424857432985 8483039182722318643074739)
              ·
                refine ⟨12724558774083477964612109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8483039182722318643074739 12724558774083477964612109)
                ·
                  refine ⟨4771709540281304236729541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12724558774083477964612109 4771709540281304236729541)
                  ·
                    refine ⟨894695538802744544386789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4771709540281304236729541 894695538802744544386789)
                    ·
                      rfl

theorem cell23_5227240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_5227240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227240 prefixEnd_5227240 := by exact prefixLift 5227240
  have htrace : WordTrace (prefixWord ++ tailWord_5227240) baseStart_5227240 baseEnd_5227240 := by
    simpa [prefixWord, tailWord_5227240, baseEnd_5227240] using wordTrace_append hprefix tailTrace_5227240
  have hstable : (prefixWord ++ tailWord_5227240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227240).length < 2 ^ (prefixWord ++ tailWord_5227240).sum := by decide
  have hdescent : baseEnd_5227240 < baseStart_5227240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227273 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 1, 5, 2]
def baseStart_5227273 : Nat := 118140960795 + 5227273 * 2 ^ 59
def prefixEnd_5227273 : Nat := 4983230072969 + 3 ^ 40 * 5227273 * 2
def baseEnd_5227273 : Nat := 2684103561269832004047715

theorem tailTrace_5227273 : CollatzResearch.WordTrace tailWord_5227273 prefixEnd_5227273 2684103561269832004047715 := by
  unfold tailWord_5227273
  simp only [CollatzResearch.WordTrace]
  refine ⟨190654309191490142998278473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127102872794326761998852315 190654309191490142998278473)
  ·
    refine ⟨142990731893617607248708855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190654309191490142998278473 142990731893617607248708855)
    ·
      refine ⟨214486097840426410873063283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142990731893617607248708855 214486097840426410873063283)
      ·
        refine ⟨321729146760639616309594925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214486097840426410873063283 321729146760639616309594925)
        ·
          refine ⟨120648430035239856116098097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 321729146760639616309594925 120648430035239856116098097)
          ·
            refine ⟨90486322526429892087073573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120648430035239856116098097 90486322526429892087073573)
            ·
              refine ⟨16966185473705604766326295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90486322526429892087073573 16966185473705604766326295)
              ·
                refine ⟨25449278210558407149489443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16966185473705604766326295 25449278210558407149489443)
                ·
                  refine ⟨38173917315837610724234165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25449278210558407149489443 38173917315837610724234165)
                  ·
                    refine ⟨3578804748359776005396953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38173917315837610724234165 3578804748359776005396953)
                    ·
                      refine ⟨2684103561269832004047715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3578804748359776005396953 2684103561269832004047715)
                      ·
                        rfl

theorem cell23_5227273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 5, 2].length) (baseStart_5227273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227273 prefixEnd_5227273 := by exact prefixLift 5227273
  have htrace : WordTrace (prefixWord ++ tailWord_5227273) baseStart_5227273 baseEnd_5227273 := by
    simpa [prefixWord, tailWord_5227273, baseEnd_5227273] using wordTrace_append hprefix tailTrace_5227273
  have hstable : (prefixWord ++ tailWord_5227273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227273).length < 2 ^ (prefixWord ++ tailWord_5227273).sum := by decide
  have hdescent : baseEnd_5227273 < baseStart_5227273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227290 : List Nat := [3, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2]
def baseStart_5227290 : Nat := 118140960795 + 5227290 * 2 ^ 59
def prefixEnd_5227290 : Nat := 4983230072969 + 3 ^ 40 * 5227290 * 2
def baseEnd_5227290 : Nat := 2684112290440958437535137

theorem tailTrace_5227290 : CollatzResearch.WordTrace tailWord_5227290 prefixEnd_5227290 2684112290440958437535137 := by
  unfold tailWord_5227290
  simp only [CollatzResearch.WordTrace]
  refine ⟨47663732308107138725411831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127103286154952369934431549 47663732308107138725411831)
  ·
    refine ⟨71495598462160708088117747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47663732308107138725411831 71495598462160708088117747)
    ·
      refine ⟨107243397693241062132176621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71495598462160708088117747 107243397693241062132176621)
      ·
        refine ⟨40216274134965398299566233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107243397693241062132176621 40216274134965398299566233)
        ·
          refine ⟨30162205601224048724674675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40216274134965398299566233 30162205601224048724674675)
          ·
            refine ⟨45243308401836073087012013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30162205601224048724674675 45243308401836073087012013)
            ·
              refine ⟨16966240650688527407629505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45243308401836073087012013 16966240650688527407629505)
              ·
                refine ⟨12724680488016395555722129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16966240650688527407629505 12724680488016395555722129)
                ·
                  refine ⟨9543510366012296666791597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12724680488016395555722129 9543510366012296666791597)
                  ·
                    refine ⟨3578816387254611250046849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9543510366012296666791597 3578816387254611250046849)
                    ·
                      refine ⟨2684112290440958437535137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3578816387254611250046849 2684112290440958437535137)
                      ·
                        rfl

theorem cell23_5227290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_5227290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227290 prefixEnd_5227290 := by exact prefixLift 5227290
  have htrace : WordTrace (prefixWord ++ tailWord_5227290) baseStart_5227290 baseEnd_5227290 := by
    simpa [prefixWord, tailWord_5227290, baseEnd_5227290] using wordTrace_append hprefix tailTrace_5227290
  have hstable : (prefixWord ++ tailWord_5227290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227290).length < 2 ^ (prefixWord ++ tailWord_5227290).sum := by decide
  have hdescent : baseEnd_5227290 < baseStart_5227290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227320 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 5, 2, 2]
def baseStart_5227320 : Nat := 118140960795 + 5227320 * 2 ^ 59
def prefixEnd_5227320 : Nat := 4983230072969 + 3 ^ 40 * 5227320 * 2
def baseEnd_5227320 : Nat := 2684127694860593320159999

theorem tailTrace_5227320 : CollatzResearch.WordTrace tailWord_5227320 prefixEnd_5227320 2684127694860593320159999 := by
  unfold tailWord_5227320
  simp only [CollatzResearch.WordTrace]
  refine ⟨95328011711159935012619707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127104015614879913350159609 95328011711159935012619707)
  ·
    refine ⟨142992017566739902518929561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95328011711159935012619707 142992017566739902518929561)
    ·
      refine ⟨107244013175054926889197171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142992017566739902518929561 107244013175054926889197171)
      ·
        refine ⟨160866019762582390333795757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107244013175054926889197171 160866019762582390333795757)
        ·
          refine ⟨60324757410968396375173409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160866019762582390333795757 60324757410968396375173409)
          ·
            refine ⟨45243568058226297281380057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60324757410968396375173409 45243568058226297281380057)
            ·
              refine ⟨33932676043669722961035043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45243568058226297281380057 33932676043669722961035043)
              ·
                refine ⟨50899014065504584441552565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33932676043669722961035043 50899014065504584441552565)
                ·
                  refine ⟨4771782568641054791395553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50899014065504584441552565 4771782568641054791395553)
                  ·
                    refine ⟨3578836926480791093546665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4771782568641054791395553 3578836926480791093546665)
                    ·
                      refine ⟨2684127694860593320159999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3578836926480791093546665 2684127694860593320159999)
                      ·
                        rfl

theorem cell23_5227320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 5, 2, 2].length) (baseStart_5227320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227320 prefixEnd_5227320 := by exact prefixLift 5227320
  have htrace : WordTrace (prefixWord ++ tailWord_5227320) baseStart_5227320 baseEnd_5227320 := by
    simpa [prefixWord, tailWord_5227320, baseEnd_5227320] using wordTrace_append hprefix tailTrace_5227320
  have hstable : (prefixWord ++ tailWord_5227320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227320).length < 2 ^ (prefixWord ++ tailWord_5227320).sum := by decide
  have hdescent : baseEnd_5227320 < baseStart_5227320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227340 : List Nat := [2, 2, 1, 3, 3, 3, 1, 1, 1, 1, 5]
def baseStart_5227340 : Nat := 118140960795 + 5227340 * 2 ^ 59
def prefixEnd_5227340 : Nat := 4983230072969 + 3 ^ 40 * 5227340 * 2
def baseEnd_5227340 : Nat := 2684137964473683241909907

theorem tailTrace_5227340 : CollatzResearch.WordTrace tailWord_5227340 prefixEnd_5227340 2684137964473683241909907 := by
  unfold tailWord_5227340
  simp only [CollatzResearch.WordTrace]
  refine ⟨95328376441123706720483737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127104501921498275627311649 95328376441123706720483737)
  ·
    refine ⟨71496282330842780040362803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95328376441123706720483737 71496282330842780040362803)
    ·
      refine ⟨107244423496264170060544205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71496282330842780040362803 107244423496264170060544205)
      ·
        refine ⟨40216658811099063772704077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107244423496264170060544205 40216658811099063772704077)
        ·
          refine ⟨15081247054162148914764029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40216658811099063772704077 15081247054162148914764029)
          ·
            refine ⟨5655467645310805843036511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15081247054162148914764029 5655467645310805843036511)
            ·
              refine ⟨8483201467966208764554767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5655467645310805843036511 8483201467966208764554767)
              ·
                refine ⟨12724802201949313146832151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8483201467966208764554767 12724802201949313146832151)
                ·
                  refine ⟨19087203302923969720248227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12724802201949313146832151 19087203302923969720248227)
                  ·
                    refine ⟨28630804954385954580372341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19087203302923969720248227 28630804954385954580372341)
                    ·
                      refine ⟨2684137964473683241909907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28630804954385954580372341 2684137964473683241909907)
                      ·
                        rfl

theorem cell23_5227340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_5227340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227340 prefixEnd_5227340 := by exact prefixLift 5227340
  have htrace : WordTrace (prefixWord ++ tailWord_5227340) baseStart_5227340 baseEnd_5227340 := by
    simpa [prefixWord, tailWord_5227340, baseEnd_5227340] using wordTrace_append hprefix tailTrace_5227340
  have hstable : (prefixWord ++ tailWord_5227340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227340).length < 2 ^ (prefixWord ++ tailWord_5227340).sum := by decide
  have hdescent : baseEnd_5227340 < baseStart_5227340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227348 : List Nat := [2, 4, 1, 1, 5, 1, 2, 2, 1, 1, 3]
def baseStart_5227348 : Nat := 118140960795 + 5227348 * 2 ^ 59
def prefixEnd_5227348 : Nat := 4983230072969 + 3 ^ 40 * 5227348 * 2
def baseEnd_5227348 : Nat := 2684142072318919210609871

theorem tailTrace_5227348 : CollatzResearch.WordTrace tailWord_5227348 prefixEnd_5227348 2684142072318919210609871 := by
  unfold tailWord_5227348
  simp only [CollatzResearch.WordTrace]
  refine ⟨95328522333109215403629349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127104696444145620538172465 95328522333109215403629349)
  ·
    refine ⟨17874097937457977888180503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95328522333109215403629349 17874097937457977888180503)
    ·
      refine ⟨26811146906186966832270755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17874097937457977888180503 26811146906186966832270755)
      ·
        refine ⟨40216720359280450248406133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26811146906186966832270755 40216720359280450248406133)
        ·
          refine ⟨3770317533682542210788075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40216720359280450248406133 3770317533682542210788075)
          ·
            refine ⟨5655476300523813316182113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3770317533682542210788075 5655476300523813316182113)
            ·
              refine ⟨4241607225392859987136585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5655476300523813316182113 4241607225392859987136585)
              ·
                refine ⟨3181205419044644990352439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4241607225392859987136585 3181205419044644990352439)
                ·
                  refine ⟨4771808128566967485528659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3181205419044644990352439 4771808128566967485528659)
                  ·
                    refine ⟨7157712192850451228292989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4771808128566967485528659 7157712192850451228292989)
                    ·
                      refine ⟨2684142072318919210609871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7157712192850451228292989 2684142072318919210609871)
                      ·
                        rfl

theorem cell23_5227348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_5227348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227348 prefixEnd_5227348 := by exact prefixLift 5227348
  have htrace : WordTrace (prefixWord ++ tailWord_5227348) baseStart_5227348 baseEnd_5227348 := by
    simpa [prefixWord, tailWord_5227348, baseEnd_5227348] using wordTrace_append hprefix tailTrace_5227348
  have hstable : (prefixWord ++ tailWord_5227348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227348).length < 2 ^ (prefixWord ++ tailWord_5227348).sum := by decide
  have hdescent : baseEnd_5227348 < baseStart_5227348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227354 : List Nat := [3, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2]
def baseStart_5227354 : Nat := 118140960795 + 5227354 * 2 ^ 59
def prefixEnd_5227354 : Nat := 4983230072969 + 3 ^ 40 * 5227354 * 2
def baseEnd_5227354 : Nat := 2684145153202846187134843

theorem tailTrace_5227354 : CollatzResearch.WordTrace tailWord_5227354 prefixEnd_5227354 2684145153202846187134843 := by
  unfold tailWord_5227354
  simp only [CollatzResearch.WordTrace]
  refine ⟨47664315876049173457994279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127104842336131129221318077 47664315876049173457994279)
  ·
    refine ⟨71496473814073760186991419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47664315876049173457994279 71496473814073760186991419)
    ·
      refine ⟨107244710721110640280487129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71496473814073760186991419 107244710721110640280487129)
      ·
        refine ⟨80433533040832980210365347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107244710721110640280487129 80433533040832980210365347)
        ·
          refine ⟨120650299561249470315548021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80433533040832980210365347 120650299561249470315548021)
          ·
            refine ⟨11310965583867137842082627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120650299561249470315548021 11310965583867137842082627)
            ·
              refine ⟨16966448375800706763123941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11310965583867137842082627 16966448375800706763123941)
              ·
                refine ⟨3181209070462632518085739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16966448375800706763123941 3181209070462632518085739)
                ·
                  refine ⟨4771813605693948777128609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3181209070462632518085739 4771813605693948777128609)
                  ·
                    refine ⟨3578860204270461582846457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4771813605693948777128609 3578860204270461582846457)
                    ·
                      refine ⟨2684145153202846187134843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3578860204270461582846457 2684145153202846187134843)
                      ·
                        rfl

theorem cell23_5227354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2].length) (baseStart_5227354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227354 prefixEnd_5227354 := by exact prefixLift 5227354
  have htrace : WordTrace (prefixWord ++ tailWord_5227354) baseStart_5227354 baseEnd_5227354 := by
    simpa [prefixWord, tailWord_5227354, baseEnd_5227354] using wordTrace_append hprefix tailTrace_5227354
  have hstable : (prefixWord ++ tailWord_5227354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227354).length < 2 ^ (prefixWord ++ tailWord_5227354).sum := by decide
  have hdescent : baseEnd_5227354 < baseStart_5227354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227386 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 3, 8]
def baseStart_5227386 : Nat := 118140960795 + 5227386 * 2 ^ 59
def prefixEnd_5227386 : Nat := 4983230072969 + 3 ^ 40 * 5227386 * 2
def baseEnd_5227386 : Nat := 894720528194596687311565

theorem tailTrace_5227386 : CollatzResearch.WordTrace tailWord_5227386 prefixEnd_5227386 894720528194596687311565 := by
  unfold tailWord_5227386
  simp only [CollatzResearch.WordTrace]
  refine ⟨47664607660020190824285503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127105620426720508864761341 47664607660020190824285503)
  ·
    refine ⟨71496911490030286236428255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47664607660020190824285503 71496911490030286236428255)
    ·
      refine ⟨107245367235045429354642383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71496911490030286236428255 107245367235045429354642383)
      ·
        refine ⟨160868050852568144031963575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107245367235045429354642383 160868050852568144031963575)
        ·
          refine ⟨241302076278852216047945363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160868050852568144031963575 241302076278852216047945363)
          ·
            refine ⟨361953114418278324071918045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241302076278852216047945363 361953114418278324071918045)
            ·
              refine ⟨135732417906854371526969267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 361953114418278324071918045 135732417906854371526969267)
              ·
                refine ⟨203598626860281557290453901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135732417906854371526969267 203598626860281557290453901)
                ·
                  refine ⟨76349485072605583983920213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 203598626860281557290453901 76349485072605583983920213)
                  ·
                    refine ⟨894720528194596687311565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76349485072605583983920213 894720528194596687311565)
                    ·
                      rfl

theorem cell23_5227386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_5227386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227386 prefixEnd_5227386 := by exact prefixLift 5227386
  have htrace : WordTrace (prefixWord ++ tailWord_5227386) baseStart_5227386 baseEnd_5227386 := by
    simpa [prefixWord, tailWord_5227386, baseEnd_5227386] using wordTrace_append hprefix tailTrace_5227386
  have hstable : (prefixWord ++ tailWord_5227386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227386).length < 2 ^ (prefixWord ++ tailWord_5227386).sum := by decide
  have hdescent : baseEnd_5227386 < baseStart_5227386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227397 : List Nat := [1, 3, 1, 1, 3, 4, 1, 3, 1, 3, 2]
def baseStart_5227397 : Nat := 118140960795 + 5227397 * 2 ^ 59
def prefixEnd_5227397 : Nat := 4983230072969 + 3 ^ 40 * 5227397 * 2
def baseEnd_5227397 : Nat := 2684167232870989518897145

theorem tailTrace_5227397 : CollatzResearch.WordTrace tailWord_5227397 prefixEnd_5227397 2684167232870989518897145 := by
  unfold tailWord_5227397
  simp only [CollatzResearch.WordTrace]
  refine ⟨190658831843040912175792445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127105887895360608117194963 190658831843040912175792445)
  ·
    refine ⟨71497061941140342065922167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190658831843040912175792445 71497061941140342065922167)
    ·
      refine ⟨107245592911710513098883251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71497061941140342065922167 107245592911710513098883251)
      ·
        refine ⟨160868389367565769648324877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107245592911710513098883251 160868389367565769648324877)
        ·
          refine ⟨60325646012837163618121829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160868389367565769648324877 60325646012837163618121829)
          ·
            refine ⟨11311058627406968178397843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60325646012837163618121829 11311058627406968178397843)
            ·
              refine ⟨16966587941110452267596765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11311058627406968178397843 16966587941110452267596765)
              ·
                refine ⟨6362470477916419600348787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16966587941110452267596765 6362470477916419600348787)
                ·
                  refine ⟨9543705716874629400523181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6362470477916419600348787 9543705716874629400523181)
                  ·
                    refine ⟨3578889643827986025196193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9543705716874629400523181 3578889643827986025196193)
                    ·
                      refine ⟨2684167232870989518897145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3578889643827986025196193 2684167232870989518897145)
                      ·
                        rfl

theorem cell23_5227397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 3, 2].length) (baseStart_5227397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227397 prefixEnd_5227397 := by exact prefixLift 5227397
  have htrace : WordTrace (prefixWord ++ tailWord_5227397) baseStart_5227397 baseEnd_5227397 := by
    simpa [prefixWord, tailWord_5227397, baseEnd_5227397] using wordTrace_append hprefix tailTrace_5227397
  have hstable : (prefixWord ++ tailWord_5227397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227397).length < 2 ^ (prefixWord ++ tailWord_5227397).sum := by decide
  have hdescent : baseEnd_5227397 < baseStart_5227397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227427 : List Nat := [1, 1, 1, 4, 1, 2, 2, 5, 2, 2, 2]
def baseStart_5227427 : Nat := 118140960795 + 5227427 * 2 ^ 59
def prefixEnd_5227427 : Nat := 4983230072969 + 3 ^ 40 * 5227427 * 2
def baseEnd_5227427 : Nat := 2684182637290624401522007

theorem tailTrace_5227427 : CollatzResearch.WordTrace tailWord_5227427 prefixEnd_5227427 2684182637290624401522007 := by
  unfold tailWord_5227427
  simp only [CollatzResearch.WordTrace]
  refine ⟨190659926032932227299384535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127106617355288151532923023 190659926032932227299384535)
  ·
    refine ⟨285989889049398340949076803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190659926032932227299384535 285989889049398340949076803)
    ·
      refine ⟨428984833574097511423615205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285989889049398340949076803 428984833574097511423615205)
      ·
        refine ⟨80434656295143283391927851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 428984833574097511423615205 80434656295143283391927851)
        ·
          refine ⟨120651984442714925087891777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80434656295143283391927851 120651984442714925087891777)
          ·
            refine ⟨90488988332036193815918833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120651984442714925087891777 90488988332036193815918833)
            ·
              refine ⟨67866741249027145361939125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90488988332036193815918833 67866741249027145361939125)
              ·
                refine ⟨6362506992096294877681793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67866741249027145361939125 6362506992096294877681793)
                ·
                  refine ⟨4771880244072221158261345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6362506992096294877681793 4771880244072221158261345)
                  ·
                    refine ⟨3578910183054165868696009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4771880244072221158261345 3578910183054165868696009)
                    ·
                      refine ⟨2684182637290624401522007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3578910183054165868696009 2684182637290624401522007)
                      ·
                        rfl

theorem cell23_5227427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 2, 2].length) (baseStart_5227427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227427 prefixEnd_5227427 := by exact prefixLift 5227427
  have htrace : WordTrace (prefixWord ++ tailWord_5227427) baseStart_5227427 baseEnd_5227427 := by
    simpa [prefixWord, tailWord_5227427, baseEnd_5227427] using wordTrace_append hprefix tailTrace_5227427
  have hstable : (prefixWord ++ tailWord_5227427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227427).length < 2 ^ (prefixWord ++ tailWord_5227427).sum := by decide
  have hdescent : baseEnd_5227427 < baseStart_5227427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227443 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 3]
def baseStart_5227443 : Nat := 118140960795 + 5227443 * 2 ^ 59
def prefixEnd_5227443 : Nat := 4983230072969 + 3 ^ 40 * 5227443 * 2
def baseEnd_5227443 : Nat := 2684190852981096338921933

theorem tailTrace_5227443 : CollatzResearch.WordTrace tailWord_5227443 prefixEnd_5227443 2684190852981096338921933 := by
  unfold tailWord_5227443
  simp only [CollatzResearch.WordTrace]
  refine ⟨190660509600874262031966983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127107006400582841354644655 190660509600874262031966983)
  ·
    refine ⟨285990764401311393047950475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190660509600874262031966983 285990764401311393047950475)
    ·
      refine ⟨428986146601967089571925713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285990764401311393047950475 428986146601967089571925713)
      ·
        refine ⟨321739609951475317178944285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428986146601967089571925713 321739609951475317178944285)
        ·
          refine ⟨120652353731803243942104107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 321739609951475317178944285 120652353731803243942104107)
          ·
            refine ⟨180978530597704865913156161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120652353731803243942104107 180978530597704865913156161)
            ·
              refine ⟨135733897948278649434867121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180978530597704865913156161 135733897948278649434867121)
              ·
                refine ⟨101800423461208987076150341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135733897948278649434867121 101800423461208987076150341)
                ·
                  refine ⟨19087579398976685076778189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101800423461208987076150341 19087579398976685076778189)
                  ·
                    refine ⟨7157842274616256903791821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19087579398976685076778189 7157842274616256903791821)
                    ·
                      refine ⟨2684190852981096338921933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7157842274616256903791821 2684190852981096338921933)
                      ·
                        rfl

theorem cell23_5227443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 3].length) (baseStart_5227443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227443 prefixEnd_5227443 := by exact prefixLift 5227443
  have htrace : WordTrace (prefixWord ++ tailWord_5227443) baseStart_5227443 baseEnd_5227443 := by
    simpa [prefixWord, tailWord_5227443, baseEnd_5227443] using wordTrace_append hprefix tailTrace_5227443
  have hstable : (prefixWord ++ tailWord_5227443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227443).length < 2 ^ (prefixWord ++ tailWord_5227443).sum := by decide
  have hdescent : baseEnd_5227443 < baseStart_5227443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227463 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 4, 5]
def baseStart_5227463 : Nat := 118140960795 + 5227463 * 2 ^ 59
def prefixEnd_5227463 : Nat := 4983230072969 + 3 ^ 40 * 5227463 * 2
def baseEnd_5227463 : Nat := 894733707531395420223947

theorem tailTrace_5227463 : CollatzResearch.WordTrace tailWord_5227463 prefixEnd_5227463 894733707531395420223947 := by
  unfold tailWord_5227463
  simp only [CollatzResearch.WordTrace]
  refine ⟨190661239060801805447695043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127107492707201203631796695 190661239060801805447695043)
  ·
    refine ⟨285991858591202708171542565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190661239060801805447695043 285991858591202708171542565)
    ·
      refine ⟨53623473485850507782164231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 285991858591202708171542565 53623473485850507782164231)
      ·
        refine ⟨80435210228775761673246347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53623473485850507782164231 80435210228775761673246347)
        ·
          refine ⟨120652815343163642509869521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80435210228775761673246347 120652815343163642509869521)
          ·
            refine ⟨90489611507372731882402141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120652815343163642509869521 90489611507372731882402141)
            ·
              refine ⟨33933604315264774455900803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90489611507372731882402141 33933604315264774455900803)
              ·
                refine ⟨50900406472897161683851205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33933604315264774455900803 50900406472897161683851205)
                ·
                  refine ⟨9543826213668217815722101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50900406472897161683851205 9543826213668217815722101)
                  ·
                    refine ⟨894733707531395420223947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9543826213668217815722101 894733707531395420223947)
                    ·
                      rfl

theorem cell23_5227463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_5227463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227463 prefixEnd_5227463 := by exact prefixLift 5227463
  have htrace : WordTrace (prefixWord ++ tailWord_5227463) baseStart_5227463 baseEnd_5227463 := by
    simpa [prefixWord, tailWord_5227463, baseEnd_5227463] using wordTrace_append hprefix tailTrace_5227463
  have hstable : (prefixWord ++ tailWord_5227463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227463).length < 2 ^ (prefixWord ++ tailWord_5227463).sum := by decide
  have hdescent : baseEnd_5227463 < baseStart_5227463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227467 : List Nat := [1, 1, 1, 1, 3, 6, 3, 2, 5]
def baseStart_5227467 : Nat := 118140960795 + 5227467 * 2 ^ 59
def prefixEnd_5227467 : Nat := 4983230072969 + 3 ^ 40 * 5227467 * 2
def baseEnd_5227467 : Nat := 298244797390756027224647

theorem tailTrace_5227467 : CollatzResearch.WordTrace tailWord_5227467 prefixEnd_5227467 298244797390756027224647 := by
  unfold tailWord_5227467
  simp only [CollatzResearch.WordTrace]
  refine ⟨190661384952787314130840655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127107589968524876087227103 190661384952787314130840655)
  ·
    refine ⟨285992077429180971196260983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190661384952787314130840655 285992077429180971196260983)
    ·
      refine ⟨428988116143771456794391475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285992077429180971196260983 428988116143771456794391475)
      ·
        refine ⟨643482174215657185191587213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428988116143771456794391475 643482174215657185191587213)
        ·
          refine ⟨241305815330871444446845205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 643482174215657185191587213 241305815330871444446845205)
          ·
            refine ⟨11311210093634598958445869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 241305815330871444446845205 11311210093634598958445869)
            ·
              refine ⟨4241703785112974609417201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11311210093634598958445869 4241703785112974609417201)
              ·
                refine ⟨3181277838834730957062901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4241703785112974609417201 3181277838834730957062901)
                ·
                  refine ⟨298244797390756027224647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3181277838834730957062901 298244797390756027224647)
                  ·
                    rfl

theorem cell23_5227467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 5].length) (baseStart_5227467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227467 prefixEnd_5227467 := by exact prefixLift 5227467
  have htrace : WordTrace (prefixWord ++ tailWord_5227467) baseStart_5227467 baseEnd_5227467 := by
    simpa [prefixWord, tailWord_5227467, baseEnd_5227467] using wordTrace_append hprefix tailTrace_5227467
  have hstable : (prefixWord ++ tailWord_5227467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227467).length < 2 ^ (prefixWord ++ tailWord_5227467).sum := by decide
  have hdescent : baseEnd_5227467 < baseStart_5227467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227473 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 1, 2, 5]
def baseStart_5227473 : Nat := 118140960795 + 5227473 * 2 ^ 59
def prefixEnd_5227473 : Nat := 4983230072969 + 3 ^ 40 * 5227473 * 2
def baseEnd_5227473 : Nat := 2684206257400731221546795

theorem tailTrace_5227473 : CollatzResearch.WordTrace tailWord_5227473 prefixEnd_5227473 2684206257400731221546795 := by
  unfold tailWord_5227473
  simp only [CollatzResearch.WordTrace]
  refine ⟨190661603790765577155559073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127107735860510384770372715 190661603790765577155559073)
  ·
    refine ⟨142996202843074182866669305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190661603790765577155559073 142996202843074182866669305)
    ·
      refine ⟨107247152132305637150001979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142996202843074182866669305 107247152132305637150001979)
      ·
        refine ⟨160870728198458455725002969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107247152132305637150001979 160870728198458455725002969)
        ·
          refine ⟨120653046148843841793752227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160870728198458455725002969 120653046148843841793752227)
          ·
            refine ⟨180979569223265762690628341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120653046148843841793752227 180979569223265762690628341)
            ·
              refine ⟨16966834614681165252246407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 180979569223265762690628341 16966834614681165252246407)
              ·
                refine ⟨25450251922021747878369611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16966834614681165252246407 25450251922021747878369611)
                ·
                  refine ⟨38175377883032621817554417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25450251922021747878369611 38175377883032621817554417)
                  ·
                    refine ⟨28631533412274466363165813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38175377883032621817554417 28631533412274466363165813)
                    ·
                      refine ⟨2684206257400731221546795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28631533412274466363165813 2684206257400731221546795)
                      ·
                        rfl

theorem cell23_5227473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_5227473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227473 prefixEnd_5227473 := by exact prefixLift 5227473
  have htrace : WordTrace (prefixWord ++ tailWord_5227473) baseStart_5227473 baseEnd_5227473 := by
    simpa [prefixWord, tailWord_5227473, baseEnd_5227473] using wordTrace_append hprefix tailTrace_5227473
  have hstable : (prefixWord ++ tailWord_5227473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227473).length < 2 ^ (prefixWord ++ tailWord_5227473).sum := by decide
  have hdescent : baseEnd_5227473 < baseStart_5227473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227478 : List Nat := [5, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2]
def baseStart_5227478 : Nat := 118140960795 + 5227478 * 2 ^ 59
def prefixEnd_5227478 : Nat := 4983230072969 + 3 ^ 40 * 5227478 * 2
def baseEnd_5227478 : Nat := 2684208824804003701984273

theorem tailTrace_5227478 : CollatzResearch.WordTrace tailWord_5227478 prefixEnd_5227478 2684208824804003701984273 := by
  unfold tailWord_5227478
  simp only [CollatzResearch.WordTrace]
  refine ⟨11916361634734216438093193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127107857437164975339660725 11916361634734216438093193)
  ·
    refine ⟨8937271226050662328569895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11916361634734216438093193 8937271226050662328569895)
    ·
      refine ⟨13405906839075993492854843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8937271226050662328569895 13405906839075993492854843)
      ·
        refine ⟨20108860258613990239282265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13405906839075993492854843 20108860258613990239282265)
        ·
          refine ⟨15081645193960492679461699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20108860258613990239282265 15081645193960492679461699)
          ·
            refine ⟨22622467790940739019192549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15081645193960492679461699 22622467790940739019192549)
            ·
              refine ⟨4241712710801388566098603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22622467790940739019192549 4241712710801388566098603)
              ·
                refine ⟨6362569066202082849147905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4241712710801388566098603 6362569066202082849147905)
                ·
                  refine ⟨4771926799651562136860929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6362569066202082849147905 4771926799651562136860929)
                  ·
                    refine ⟨3578945099738671602645697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4771926799651562136860929 3578945099738671602645697)
                    ·
                      refine ⟨2684208824804003701984273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3578945099738671602645697 2684208824804003701984273)
                      ·
                        rfl

theorem cell23_5227478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_5227478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227478 prefixEnd_5227478 := by exact prefixLift 5227478
  have htrace : WordTrace (prefixWord ++ tailWord_5227478) baseStart_5227478 baseEnd_5227478 := by
    simpa [prefixWord, tailWord_5227478, baseEnd_5227478] using wordTrace_append hprefix tailTrace_5227478
  have hstable : (prefixWord ++ tailWord_5227478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227478).length < 2 ^ (prefixWord ++ tailWord_5227478).sum := by decide
  have hdescent : baseEnd_5227478 < baseStart_5227478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227500 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 6, 4, 2]
def baseStart_5227500 : Nat := 118140960795 + 5227500 * 2 ^ 59
def prefixEnd_5227500 : Nat := 4983230072969 + 3 ^ 40 * 5227500 * 2
def baseEnd_5227500 : Nat := 2684220121378402615909171

theorem tailTrace_5227500 : CollatzResearch.WordTrace tailWord_5227500 prefixEnd_5227500 2684220121378402615909171 := by
  unfold tailWord_5227500
  simp only [CollatzResearch.WordTrace]
  refine ⟨95331294280833880383395977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127108392374445173844527969 95331294280833880383395977)
  ·
    refine ⟨71498470710625410287546983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95331294280833880383395977 71498470710625410287546983)
    ·
      refine ⟨107247706065938115431320475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71498470710625410287546983 107247706065938115431320475)
      ·
        refine ⟨160871559098907173146980713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107247706065938115431320475 160871559098907173146980713)
        ·
          refine ⟨120653669324180379860235535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160871559098907173146980713 120653669324180379860235535)
          ·
            refine ⟨180980503986270569790353303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120653669324180379860235535 180980503986270569790353303)
            ·
              refine ⟨271470755979405854685529955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180980503986270569790353303 271470755979405854685529955)
              ·
                refine ⟨407206133969108782028294933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271470755979405854685529955 407206133969108782028294933)
                ·
                  refine ⟨19087787529801974157576325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 407206133969108782028294933 19087787529801974157576325)
                  ·
                    refine ⟨3578960161837870154545561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19087787529801974157576325 3578960161837870154545561)
                    ·
                      refine ⟨2684220121378402615909171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3578960161837870154545561 2684220121378402615909171)
                      ·
                        rfl

theorem cell23_5227500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 4, 2].length) (baseStart_5227500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227500 prefixEnd_5227500 := by exact prefixLift 5227500
  have htrace : WordTrace (prefixWord ++ tailWord_5227500) baseStart_5227500 baseEnd_5227500 := by
    simpa [prefixWord, tailWord_5227500, baseEnd_5227500] using wordTrace_append hprefix tailTrace_5227500
  have hstable : (prefixWord ++ tailWord_5227500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227500).length < 2 ^ (prefixWord ++ tailWord_5227500).sum := by decide
  have hdescent : baseEnd_5227500 < baseStart_5227500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227513 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 2, 1, 6]
def baseStart_5227513 : Nat := 118140960795 + 5227513 * 2 ^ 59
def prefixEnd_5227513 : Nat := 4983230072969 + 3 ^ 40 * 5227513 * 2
def baseEnd_5227513 : Nat := 2684226796626911065046611

theorem tailTrace_5227513 : CollatzResearch.WordTrace tailWord_5227513 prefixEnd_5227513 2684226796626911065046611 := by
  unfold tailWord_5227513
  simp only [CollatzResearch.WordTrace]
  refine ⟨190663062710620663987015193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127108708473747109324676795 190663062710620663987015193)
  ·
    refine ⟨142997297032965497990261395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190663062710620663987015193 142997297032965497990261395)
    ·
      refine ⟨214495945549448246985392093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142997297032965497990261395 214495945549448246985392093)
      ·
        refine ⟨80435979581043092619522035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214495945549448246985392093 80435979581043092619522035)
        ·
          refine ⟨120653969371564638929283053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80435979581043092619522035 120653969371564638929283053)
          ·
            refine ⟨45245238514336739598481145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120653969371564638929283053 45245238514336739598481145)
            ·
              refine ⟨33933928885752554698860859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45245238514336739598481145 33933928885752554698860859)
              ·
                refine ⟨50900893328628832048291289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33933928885752554698860859 50900893328628832048291289)
                ·
                  refine ⟨38175669996471624036218467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50900893328628832048291289 38175669996471624036218467)
                  ·
                    refine ⟨57263504994707436054327701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38175669996471624036218467 57263504994707436054327701)
                    ·
                      refine ⟨2684226796626911065046611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57263504994707436054327701 2684226796626911065046611)
                      ·
                        rfl

theorem cell23_5227513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_5227513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227513 prefixEnd_5227513 := by exact prefixLift 5227513
  have htrace : WordTrace (prefixWord ++ tailWord_5227513) baseStart_5227513 baseEnd_5227513 := by
    simpa [prefixWord, tailWord_5227513, baseEnd_5227513] using wordTrace_append hprefix tailTrace_5227513
  have hstable : (prefixWord ++ tailWord_5227513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227513).length < 2 ^ (prefixWord ++ tailWord_5227513).sum := by decide
  have hdescent : baseEnd_5227513 < baseStart_5227513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227518 : List Nat := [4, 2, 2, 2, 3, 1, 2, 2, 5]
def baseStart_5227518 : Nat := 118140960795 + 5227518 * 2 ^ 59
def prefixEnd_5227518 : Nat := 4983230072969 + 3 ^ 40 * 5227518 * 2
def baseEnd_5227518 : Nat := 298247707114464838387121

theorem tailTrace_5227518 : CollatzResearch.WordTrace tailWord_5227518 prefixEnd_5227518 298247707114464838387121 := by
  unfold tailWord_5227518
  simp only [CollatzResearch.WordTrace]
  refine ⟨23832905634450318730118401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127108830050401699893964805 23832905634450318730118401)
  ·
    refine ⟨17874679225837739047588801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23832905634450318730118401 17874679225837739047588801)
    ·
      refine ⟨13406009419378304285691601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17874679225837739047588801 13406009419378304285691601)
      ·
        refine ⟨10054507064533728214268701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13406009419378304285691601 10054507064533728214268701)
        ·
          refine ⟨3770440149200148080350763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10054507064533728214268701 3770440149200148080350763)
          ·
            refine ⟨5655660223800222120526145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3770440149200148080350763 5655660223800222120526145)
            ·
              refine ⟨4241745167850166590394609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5655660223800222120526145 4241745167850166590394609)
              ·
                refine ⟨3181308875887624942795957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4241745167850166590394609 3181308875887624942795957)
                ·
                  refine ⟨298247707114464838387121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3181308875887624942795957 298247707114464838387121)
                  ·
                    rfl

theorem cell23_5227518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_5227518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227518 prefixEnd_5227518 := by exact prefixLift 5227518
  have htrace : WordTrace (prefixWord ++ tailWord_5227518) baseStart_5227518 baseEnd_5227518 := by
    simpa [prefixWord, tailWord_5227518, baseEnd_5227518] using wordTrace_append hprefix tailTrace_5227518
  have hstable : (prefixWord ++ tailWord_5227518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227518).length < 2 ^ (prefixWord ++ tailWord_5227518).sum := by decide
  have hdescent : baseEnd_5227518 < baseStart_5227518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227554 : List Nat := [3, 3, 1, 1, 1, 5, 1, 1, 2, 2, 3]
def baseStart_5227554 : Nat := 118140960795 + 5227554 * 2 ^ 59
def prefixEnd_5227554 : Nat := 4983230072969 + 3 ^ 40 * 5227554 * 2
def baseEnd_5227554 : Nat := 2684247849333745404633923

theorem tailTrace_5227554 : CollatzResearch.WordTrace tailWord_5227554 prefixEnd_5227554 2684247849333745404633923 := by
  unfold tailWord_5227554
  simp only [CollatzResearch.WordTrace]
  refine ⟨47666139525868031997314429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127109705402314751992838477 47666139525868031997314429)
  ·
    refine ⟨17874802322200511998992911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47666139525868031997314429 17874802322200511998992911)
    ·
      refine ⟨26812203483300767998489367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17874802322200511998992911 26812203483300767998489367)
      ·
        refine ⟨40218305224951151997734051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26812203483300767998489367 40218305224951151997734051)
        ·
          refine ⟨60327457837426727996601077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40218305224951151997734051 60327457837426727996601077)
          ·
            refine ⟨5655699172258755749681351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60327457837426727996601077 5655699172258755749681351)
            ·
              refine ⟨8483548758388133624522027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5655699172258755749681351 8483548758388133624522027)
              ·
                refine ⟨12725323137582200436783041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8483548758388133624522027 12725323137582200436783041)
                ·
                  refine ⟨9543992353186650327587281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12725323137582200436783041 9543992353186650327587281)
                  ·
                    refine ⟨7157994264889987745690461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9543992353186650327587281 7157994264889987745690461)
                    ·
                      refine ⟨2684247849333745404633923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7157994264889987745690461 2684247849333745404633923)
                      ·
                        rfl

theorem cell23_5227554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_5227554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227554 prefixEnd_5227554 := by exact prefixLift 5227554
  have htrace : WordTrace (prefixWord ++ tailWord_5227554) baseStart_5227554 baseEnd_5227554 := by
    simpa [prefixWord, tailWord_5227554, baseEnd_5227554] using wordTrace_append hprefix tailTrace_5227554
  have hstable : (prefixWord ++ tailWord_5227554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227554).length < 2 ^ (prefixWord ++ tailWord_5227554).sum := by decide
  have hdescent : baseEnd_5227554 < baseStart_5227554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227574 : List Nat := [5, 1, 2, 1, 1, 4, 1, 2, 6]
def baseStart_5227574 : Nat := 118140960795 + 5227574 * 2 ^ 59
def prefixEnd_5227574 : Nat := 4983230072969 + 3 ^ 40 * 5227574 * 2
def baseEnd_5227574 : Nat := 298250902105203925153759

theorem tailTrace_5227574 : CollatzResearch.WordTrace tailWord_5227574 prefixEnd_5227574 298250902105203925153759 := by
  unfold tailWord_5227574
  simp only [CollatzResearch.WordTrace]
  refine ⟨11916580472712479462811611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127110191708933114269990517 11916580472712479462811611)
  ·
    refine ⟨17874870709068719194217417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11916580472712479462811611 17874870709068719194217417)
    ·
      refine ⟨13406153031801539395663063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17874870709068719194217417 13406153031801539395663063)
      ·
        refine ⟨20109229547702309093494595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13406153031801539395663063 20109229547702309093494595)
        ·
          refine ⟨30163844321553463640241893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20109229547702309093494595 30163844321553463640241893)
          ·
            refine ⟨5655720810291274432545355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30163844321553463640241893 5655720810291274432545355)
            ·
              refine ⟨8483581215436911648818033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5655720810291274432545355 8483581215436911648818033)
              ·
                refine ⟨6362685911577683736613525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8483581215436911648818033 6362685911577683736613525)
                ·
                  refine ⟨298250902105203925153759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6362685911577683736613525 298250902105203925153759)
                  ·
                    rfl

theorem cell23_5227574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_5227574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227574 prefixEnd_5227574 := by exact prefixLift 5227574
  have htrace : WordTrace (prefixWord ++ tailWord_5227574) baseStart_5227574 baseEnd_5227574 := by
    simpa [prefixWord, tailWord_5227574, baseEnd_5227574] using wordTrace_append hprefix tailTrace_5227574
  have hstable : (prefixWord ++ tailWord_5227574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227574).length < 2 ^ (prefixWord ++ tailWord_5227574).sum := by decide
  have hdescent : baseEnd_5227574 < baseStart_5227574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227584 : List Nat := [2, 1, 1, 2, 2, 3, 1, 6, 1, 1, 3]
def baseStart_5227584 : Nat := 118140960795 + 5227584 * 2 ^ 59
def prefixEnd_5227584 : Nat := 4983230072969 + 3 ^ 40 * 5227584 * 2
def baseEnd_5227584 : Nat := 2684263253753380287258785

theorem tailTrace_5227584 : CollatzResearch.WordTrace tailWord_5227584 prefixEnd_5227584 2684263253753380287258785 := by
  unfold tailWord_5227584
  simp only [CollatzResearch.WordTrace]
  refine ⟨95332826146681721556424903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127110434862242295408566537 95332826146681721556424903)
  ·
    refine ⟨142999239220022582334637355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95332826146681721556424903 142999239220022582334637355)
    ·
      refine ⟨214498858830033873501956033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142999239220022582334637355 214498858830033873501956033)
      ·
        refine ⟨160874144122525405126467025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214498858830033873501956033 160874144122525405126467025)
        ·
          refine ⟨120655608091894053844850269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160874144122525405126467025 120655608091894053844850269)
          ·
            refine ⟨45245853034460270191818851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120655608091894053844850269 45245853034460270191818851)
            ·
              refine ⟨67868779551690405287728277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45245853034460270191818851 67868779551690405287728277)
              ·
                refine ⟨3181349041485487747862263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67868779551690405287728277 3181349041485487747862263)
                ·
                  refine ⟨4772023562228231621793395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3181349041485487747862263 4772023562228231621793395)
                  ·
                    refine ⟨7158035343342347432690093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4772023562228231621793395 7158035343342347432690093)
                    ·
                      refine ⟨2684263253753380287258785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7158035343342347432690093 2684263253753380287258785)
                      ·
                        rfl

theorem cell23_5227584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 1, 1, 3].length) (baseStart_5227584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227584 prefixEnd_5227584 := by exact prefixLift 5227584
  have htrace : WordTrace (prefixWord ++ tailWord_5227584) baseStart_5227584 baseEnd_5227584 := by
    simpa [prefixWord, tailWord_5227584, baseEnd_5227584] using wordTrace_append hprefix tailTrace_5227584
  have hstable : (prefixWord ++ tailWord_5227584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227584).length < 2 ^ (prefixWord ++ tailWord_5227584).sum := by decide
  have hdescent : baseEnd_5227584 < baseStart_5227584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227618 : List Nat := [3, 3, 2, 2, 1, 1, 3, 3, 1, 1, 3]
def baseStart_5227618 : Nat := 118140960795 + 5227618 * 2 ^ 59
def prefixEnd_5227618 : Nat := 4983230072969 + 3 ^ 40 * 5227618 * 2
def baseEnd_5227618 : Nat := 2684280712095633154233629

theorem tailTrace_5227618 : CollatzResearch.WordTrace tailWord_5227618 prefixEnd_5227618 2684280712095633154233629 := by
  unfold tailWord_5227618
  simp only [CollatzResearch.WordTrace]
  refine ⟨47666723093810066729896877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127111261583493511279725005 47666723093810066729896877)
  ·
    refine ⟨17875021160178775023711329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47666723093810066729896877 17875021160178775023711329)
    ·
      refine ⟨13406265870134081267783497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17875021160178775023711329 13406265870134081267783497)
      ·
        refine ⟨10054699402600560950837623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13406265870134081267783497 10054699402600560950837623)
        ·
          refine ⟨15082049103900841426256435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10054699402600560950837623 15082049103900841426256435)
          ·
            refine ⟨22623073655851262139384653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15082049103900841426256435 22623073655851262139384653)
            ·
              refine ⟨8483652620944223302269245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22623073655851262139384653 8483652620944223302269245)
              ·
                refine ⟨3181369732854083738350967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8483652620944223302269245 3181369732854083738350967)
                ·
                  refine ⟨4772054599281125607526451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3181369732854083738350967 4772054599281125607526451)
                  ·
                    refine ⟨7158081898921688411289677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4772054599281125607526451 7158081898921688411289677)
                    ·
                      refine ⟨2684280712095633154233629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7158081898921688411289677 2684280712095633154233629)
                      ·
                        rfl

theorem cell23_5227618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_5227618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227618 prefixEnd_5227618 := by exact prefixLift 5227618
  have htrace : WordTrace (prefixWord ++ tailWord_5227618) baseStart_5227618 baseEnd_5227618 := by
    simpa [prefixWord, tailWord_5227618, baseEnd_5227618] using wordTrace_append hprefix tailTrace_5227618
  have hstable : (prefixWord ++ tailWord_5227618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227618).length < 2 ^ (prefixWord ++ tailWord_5227618).sum := by decide
  have hdescent : baseEnd_5227618 < baseStart_5227618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227620 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 3, 2, 4]
def baseStart_5227620 : Nat := 118140960795 + 5227620 * 2 ^ 59
def prefixEnd_5227620 : Nat := 4983230072969 + 3 ^ 40 * 5227620 * 2
def baseEnd_5227620 : Nat := 2684281739056942146408619

theorem tailTrace_5227620 : CollatzResearch.WordTrace tailWord_5227620 prefixEnd_5227620 2684281739056942146408619 := by
  unfold tailWord_5227620
  simp only [CollatzResearch.WordTrace]
  refine ⟨95333482660616510630580157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127111310214155347507440209 95333482660616510630580157)
  ·
    refine ⟨35750055997731191486467559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95333482660616510630580157 35750055997731191486467559)
    ·
      refine ⟨53625083996596787229701339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35750055997731191486467559 53625083996596787229701339)
      ·
        refine ⟨80437625994895180844552009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53625083996596787229701339 80437625994895180844552009)
        ·
          refine ⟨60328219496171385633414007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80437625994895180844552009 60328219496171385633414007)
          ·
            refine ⟨90492329244257078450121011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60328219496171385633414007 90492329244257078450121011)
            ·
              refine ⟨135738493866385617675181517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90492329244257078450121011 135738493866385617675181517)
              ·
                refine ⟨50901935199894606628193069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135738493866385617675181517 50901935199894606628193069)
                ·
                  refine ⟨19088225699960477485572401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50901935199894606628193069 19088225699960477485572401)
                  ·
                    refine ⟨14316169274970358114179301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19088225699960477485572401 14316169274970358114179301)
                    ·
                      refine ⟨2684281739056942146408619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14316169274970358114179301 2684281739056942146408619)
                      ·
                        rfl

theorem cell23_5227620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_5227620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227620 prefixEnd_5227620 := by exact prefixLift 5227620
  have htrace : WordTrace (prefixWord ++ tailWord_5227620) baseStart_5227620 baseEnd_5227620 := by
    simpa [prefixWord, tailWord_5227620, baseEnd_5227620] using wordTrace_append hprefix tailTrace_5227620
  have hstable : (prefixWord ++ tailWord_5227620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227620).length < 2 ^ (prefixWord ++ tailWord_5227620).sum := by decide
  have hdescent : baseEnd_5227620 < baseStart_5227620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227630 : List Nat := [4, 1, 2, 2, 1, 2, 11]
def baseStart_5227630 : Nat := 118140960795 + 5227630 * 2 ^ 59
def prefixEnd_5227630 : Nat := 4983230072969 + 3 ^ 40 * 5227630 * 2
def baseEnd_5227630 : Nat := 33139344121771445768933

theorem tailTrace_5227630 : CollatzResearch.WordTrace tailWord_5227630 prefixEnd_5227630 33139344121771445768933 := by
  unfold tailWord_5227630
  simp only [CollatzResearch.WordTrace]
  refine ⟨23833416256399599121128043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127111553367464528646016229 23833416256399599121128043)
  ·
    refine ⟨35750124384599398681692065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23833416256399599121128043 35750124384599398681692065)
    ·
      refine ⟨26812593288449549011269049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35750124384599398681692065 26812593288449549011269049)
      ·
        refine ⟨20109444966337161758451787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26812593288449549011269049 20109444966337161758451787)
        ·
          refine ⟨30164167449505742637677681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20109444966337161758451787 30164167449505742637677681)
          ·
            refine ⟨22623125587129306978258261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30164167449505742637677681 22623125587129306978258261)
            ·
              refine ⟨33139344121771445768933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 22623125587129306978258261 33139344121771445768933)
              ·
                rfl

theorem cell23_5227630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 11].length) (baseStart_5227630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227630 prefixEnd_5227630 := by exact prefixLift 5227630
  have htrace : WordTrace (prefixWord ++ tailWord_5227630) baseStart_5227630 baseEnd_5227630 := by
    simpa [prefixWord, tailWord_5227630, baseEnd_5227630] using wordTrace_append hprefix tailTrace_5227630
  have hstable : (prefixWord ++ tailWord_5227630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227630).length < 2 ^ (prefixWord ++ tailWord_5227630).sum := by decide
  have hdescent : baseEnd_5227630 < baseStart_5227630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227674 : List Nat := [3, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3]
def baseStart_5227674 : Nat := 118140960795 + 5227674 * 2 ^ 59
def prefixEnd_5227674 : Nat := 4983230072969 + 3 ^ 40 * 5227674 * 2
def baseEnd_5227674 : Nat := 2684309467012284935133371

theorem tailTrace_5227674 : CollatzResearch.WordTrace tailWord_5227674 prefixEnd_5227674 2684309467012284935133371 := by
  unfold tailWord_5227674
  simp only [CollatzResearch.WordTrace]
  refine ⟨47667233715759347120906519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127112623242024925655750717 47667233715759347120906519)
  ·
    refine ⟨71500850573639020681359779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47667233715759347120906519 71500850573639020681359779)
    ·
      refine ⟨107251275860458531022039669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71500850573639020681359779 107251275860458531022039669)
      ·
        refine ⟨10054807111917987283316219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107251275860458531022039669 10054807111917987283316219)
        ·
          refine ⟨15082210667876980924974329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10054807111917987283316219 15082210667876980924974329)
          ·
            refine ⟨11311658000907735693730747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15082210667876980924974329 11311658000907735693730747)
            ·
              refine ⟨16967487001361603540596121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11311658000907735693730747 16967487001361603540596121)
              ·
                refine ⟨12725615251021202655447091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16967487001361603540596121 12725615251021202655447091)
                ·
                  refine ⟨19088422876531803983170637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12725615251021202655447091 19088422876531803983170637)
                  ·
                    refine ⟨7158158578699426493688989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19088422876531803983170637 7158158578699426493688989)
                    ·
                      refine ⟨2684309467012284935133371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7158158578699426493688989 2684309467012284935133371)
                      ·
                        rfl

theorem cell23_5227674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_5227674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227674 prefixEnd_5227674 := by exact prefixLift 5227674
  have htrace : WordTrace (prefixWord ++ tailWord_5227674) baseStart_5227674 baseEnd_5227674 := by
    simpa [prefixWord, tailWord_5227674, baseEnd_5227674] using wordTrace_append hprefix tailTrace_5227674
  have hstable : (prefixWord ++ tailWord_5227674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227674).length < 2 ^ (prefixWord ++ tailWord_5227674).sum := by decide
  have hdescent : baseEnd_5227674 < baseStart_5227674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227678 : List Nat := [4, 3, 1, 1, 2, 2, 3, 1, 1, 2, 3]
def baseStart_5227678 : Nat := 118140960795 + 5227678 * 2 ^ 59
def prefixEnd_5227678 : Nat := 4983230072969 + 3 ^ 40 * 5227678 * 2
def baseEnd_5227678 : Nat := 2684311520934902919483353

theorem tailTrace_5227678 : CollatzResearch.WordTrace tailWord_5227678 prefixEnd_5227678 2684311520934902919483353 := by
  unfold tailWord_5227678
  simp only [CollatzResearch.WordTrace]
  refine ⟨23833635094377862145846461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127112720503348598111181125 23833635094377862145846461)
  ·
    refine ⟨8937613160391698304692423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23833635094377862145846461 8937613160391698304692423)
    ·
      refine ⟨13406419740587547457038635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8937613160391698304692423 13406419740587547457038635)
      ·
        refine ⟨20109629610881321185557953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13406419740587547457038635 20109629610881321185557953)
        ·
          refine ⟨15082222208160990889168465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20109629610881321185557953 15082222208160990889168465)
          ·
            refine ⟨11311666656120743166876349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15082222208160990889168465 11311666656120743166876349)
            ·
              refine ⟨4241874996045278687578631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11311666656120743166876349 4241874996045278687578631)
              ·
                refine ⟨6362812494067918031367947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4241874996045278687578631 6362812494067918031367947)
                ·
                  refine ⟨9544218741101877047051921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6362812494067918031367947 9544218741101877047051921)
                  ·
                    refine ⟨7158164055826407785288941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9544218741101877047051921 7158164055826407785288941)
                    ·
                      refine ⟨2684311520934902919483353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7158164055826407785288941 2684311520934902919483353)
                      ·
                        rfl

theorem cell23_5227678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_5227678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227678 prefixEnd_5227678 := by exact prefixLift 5227678
  have htrace : WordTrace (prefixWord ++ tailWord_5227678) baseStart_5227678 baseEnd_5227678 := by
    simpa [prefixWord, tailWord_5227678, baseEnd_5227678] using wordTrace_append hprefix tailTrace_5227678
  have hstable : (prefixWord ++ tailWord_5227678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227678).length < 2 ^ (prefixWord ++ tailWord_5227678).sum := by decide
  have hdescent : baseEnd_5227678 < baseStart_5227678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227697 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 2, 3, 4]
def baseStart_5227697 : Nat := 118140960795 + 5227697 * 2 ^ 59
def prefixEnd_5227697 : Nat := 4983230072969 + 3 ^ 40 * 5227697 * 2
def baseEnd_5227697 : Nat := 2684321277067338345145765

theorem tailTrace_5227697 : CollatzResearch.WordTrace tailWord_5227697 prefixEnd_5227697 2684321277067338345145765 := by
  unfold tailWord_5227697
  simp only [CollatzResearch.WordTrace]
  refine ⟨190669773741954063411713345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127113182494636042274475563 190669773741954063411713345)
  ·
    refine ⟨143002330306465547558785009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190669773741954063411713345 143002330306465547558785009)
    ·
      refine ⟨107251747729849160669088757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143002330306465547558785009 107251747729849160669088757)
      ·
        refine ⟨10054851349673358812727071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107251747729849160669088757 10054851349673358812727071)
        ·
          refine ⟨15082277024510038219090607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10054851349673358812727071 15082277024510038219090607)
          ·
            refine ⟨22623415536765057328635911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15082277024510038219090607 22623415536765057328635911)
            ·
              refine ⟨33935123305147585992953867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22623415536765057328635911 33935123305147585992953867)
              ·
                refine ⟨50902684957721378989430801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33935123305147585992953867 50902684957721378989430801)
                ·
                  refine ⟨38177013718291034242073101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50902684957721378989430801 38177013718291034242073101)
                  ·
                    refine ⟨14316380144359137840777413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38177013718291034242073101 14316380144359137840777413)
                    ·
                      refine ⟨2684321277067338345145765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14316380144359137840777413 2684321277067338345145765)
                      ·
                        rfl

theorem cell23_5227697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_5227697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227697 prefixEnd_5227697 := by exact prefixLift 5227697
  have htrace : WordTrace (prefixWord ++ tailWord_5227697) baseStart_5227697 baseEnd_5227697 := by
    simpa [prefixWord, tailWord_5227697, baseEnd_5227697] using wordTrace_append hprefix tailTrace_5227697
  have hstable : (prefixWord ++ tailWord_5227697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227697).length < 2 ^ (prefixWord ++ tailWord_5227697).sum := by decide
  have hdescent : baseEnd_5227697 < baseStart_5227697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227720 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 9]
def baseStart_5227720 : Nat := 118140960795 + 5227720 * 2 ^ 59
def prefixEnd_5227720 : Nat := 4983230072969 + 3 ^ 40 * 5227720 * 2
def baseEnd_5227720 : Nat := 298259231902487972795351

theorem tailTrace_5227720 : CollatzResearch.WordTrace tailWord_5227720 prefixEnd_5227720 298259231902487972795351 := by
  unfold tailWord_5227720
  simp only [CollatzResearch.WordTrace]
  refine ⟨95335306310435369169900307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127113741747247158893200409 95335306310435369169900307)
  ·
    refine ⟨143002959465653053754850461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95335306310435369169900307 143002959465653053754850461)
    ·
      refine ⟨53626109799619895158068923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143002959465653053754850461 53626109799619895158068923)
      ·
        refine ⟨80439164699429842737103385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53626109799619895158068923 80439164699429842737103385)
        ·
          refine ⟨60329373524572382052827539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80439164699429842737103385 60329373524572382052827539)
          ·
            refine ⟨90494060286858573079241309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60329373524572382052827539 90494060286858573079241309)
            ·
              refine ⟨33935272607571964904715491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90494060286858573079241309 33935272607571964904715491)
              ·
                refine ⟨50902908911357947357073237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33935272607571964904715491 50902908911357947357073237)
                ·
                  refine ⟨298259231902487972795351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50902908911357947357073237 298259231902487972795351)
                  ·
                    rfl

theorem cell23_5227720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 9].length) (baseStart_5227720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227720 prefixEnd_5227720 := by exact prefixLift 5227720
  have htrace : WordTrace (prefixWord ++ tailWord_5227720) baseStart_5227720 baseEnd_5227720 := by
    simpa [prefixWord, tailWord_5227720, baseEnd_5227720] using wordTrace_append hprefix tailTrace_5227720
  have hstable : (prefixWord ++ tailWord_5227720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227720).length < 2 ^ (prefixWord ++ tailWord_5227720).sum := by decide
  have hdescent : baseEnd_5227720 < baseStart_5227720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227754 : List Nat := [3, 1, 3, 1, 1, 3, 2, 4, 5]
def baseStart_5227754 : Nat := 118140960795 + 5227754 * 2 ^ 59
def prefixEnd_5227754 : Nat := 4983230072969 + 3 ^ 40 * 5227754 * 2
def baseEnd_5227754 : Nat := 298261171718293846903667

theorem tailTrace_5227754 : CollatzResearch.WordTrace tailWord_5227754 prefixEnd_5227754 298261171718293846903667 := by
  unfold tailWord_5227754
  simp only [CollatzResearch.WordTrace]
  refine ⟨47667963175686890536634579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127114568468498374764358877 47667963175686890536634579)
  ·
    refine ⟨71501944763530335804951869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47667963175686890536634579 71501944763530335804951869)
    ·
      refine ⟨26813229286323875926856951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71501944763530335804951869 26813229286323875926856951)
      ·
        refine ⟨40219843929485813890285427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26813229286323875926856951 40219843929485813890285427)
        ·
          refine ⟨60329765894228720835428141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40219843929485813890285427 60329765894228720835428141)
          ·
            refine ⟨22623662210335770313285553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60329765894228720835428141 22623662210335770313285553)
            ·
              refine ⟨16967746657751827734964165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22623662210335770313285553 16967746657751827734964165)
              ·
                refine ⟨3181452498328467700305781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16967746657751827734964165 3181452498328467700305781)
                ·
                  refine ⟨298261171718293846903667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3181452498328467700305781 298261171718293846903667)
                  ·
                    rfl

theorem cell23_5227754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 5].length) (baseStart_5227754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227754 prefixEnd_5227754 := by exact prefixLift 5227754
  have htrace : WordTrace (prefixWord ++ tailWord_5227754) baseStart_5227754 baseEnd_5227754 := by
    simpa [prefixWord, tailWord_5227754, baseEnd_5227754] using wordTrace_append hprefix tailTrace_5227754
  have hstable : (prefixWord ++ tailWord_5227754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227754).length < 2 ^ (prefixWord ++ tailWord_5227754).sum := by decide
  have hdescent : baseEnd_5227754 < baseStart_5227754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227787 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 4]
def baseStart_5227787 : Nat := 118140960795 + 5227787 * 2 ^ 59
def prefixEnd_5227787 : Nat := 4983230072969 + 3 ^ 40 * 5227787 * 2
def baseEnd_5227787 : Nat := 2684367490326242993020351

theorem tailTrace_5227787 : CollatzResearch.WordTrace tailWord_5227787 prefixEnd_5227787 2684367490326242993020351 := by
  unfold tailWord_5227787
  simp only [CollatzResearch.WordTrace]
  refine ⟨190673056311628008782489615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127115370874418672521659743 190673056311628008782489615)
  ·
    refine ⟨286009584467442013173734423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190673056311628008782489615 286009584467442013173734423)
    ·
      refine ⟨429014376701163019760601635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286009584467442013173734423 429014376701163019760601635)
      ·
        refine ⟨643521565051744529640902453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429014376701163019760601635 643521565051744529640902453)
        ·
          refine ⟨60330146723601049653834605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 643521565051744529640902453 60330146723601049653834605)
          ·
            refine ⟨22623805021350393620187977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60330146723601049653834605 22623805021350393620187977)
            ·
              refine ⟨16967853766012795215140983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22623805021350393620187977 16967853766012795215140983)
              ·
                refine ⟨25451780649019192822711475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16967853766012795215140983 25451780649019192822711475)
                ·
                  refine ⟨38177670973528789234067213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25451780649019192822711475 38177670973528789234067213)
                  ·
                    refine ⟨14316626615073295962775205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38177670973528789234067213 14316626615073295962775205)
                    ·
                      refine ⟨2684367490326242993020351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14316626615073295962775205 2684367490326242993020351)
                      ·
                        rfl

theorem cell23_5227787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 4].length) (baseStart_5227787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227787 prefixEnd_5227787 := by exact prefixLift 5227787
  have htrace : WordTrace (prefixWord ++ tailWord_5227787) baseStart_5227787 baseEnd_5227787 := by
    simpa [prefixWord, tailWord_5227787, baseEnd_5227787] using wordTrace_append hprefix tailTrace_5227787
  have hstable : (prefixWord ++ tailWord_5227787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227787).length < 2 ^ (prefixWord ++ tailWord_5227787).sum := by decide
  have hdescent : baseEnd_5227787 < baseStart_5227787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227804 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 4, 4, 2]
def baseStart_5227804 : Nat := 118140960795 + 5227804 * 2 ^ 59
def prefixEnd_5227804 : Nat := 4983230072969 + 3 ^ 40 * 5227804 * 2
def baseEnd_5227804 : Nat := 2684376219497369426507773

theorem tailTrace_5227804 : CollatzResearch.WordTrace tailWord_5227804 prefixEnd_5227804 2684376219497369426507773 := by
  unfold tailWord_5227804
  simp only [CollatzResearch.WordTrace]
  refine ⟨95336838176283210342929233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127115784235044280457238977 95336838176283210342929233)
  ·
    refine ⟨71502628632212407757196925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95336838176283210342929233 71502628632212407757196925)
    ·
      refine ⟨26813485737079652908948847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71502628632212407757196925 26813485737079652908948847)
      ·
        refine ⟨40220228605619479363423271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26813485737079652908948847 40220228605619479363423271)
        ·
          refine ⟨60330342908429219045134907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40220228605619479363423271 60330342908429219045134907)
          ·
            refine ⟨90495514362643828567702361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60330342908429219045134907 90495514362643828567702361)
            ·
              refine ⟨67871635771982871425776771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90495514362643828567702361 67871635771982871425776771)
              ·
                refine ⟨101807453657974307138665157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67871635771982871425776771 101807453657974307138665157)
                ·
                  refine ⟨19088897560870182588499717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101807453657974307138665157 19088897560870182588499717)
                  ·
                    refine ⟨3579168292663159235343697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19088897560870182588499717 3579168292663159235343697)
                    ·
                      refine ⟨2684376219497369426507773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3579168292663159235343697 2684376219497369426507773)
                      ·
                        rfl

theorem cell23_5227804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_5227804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227804 prefixEnd_5227804 := by exact prefixLift 5227804
  have htrace : WordTrace (prefixWord ++ tailWord_5227804) baseStart_5227804 baseEnd_5227804 := by
    simpa [prefixWord, tailWord_5227804, baseEnd_5227804] using wordTrace_append hprefix tailTrace_5227804
  have hstable : (prefixWord ++ tailWord_5227804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227804).length < 2 ^ (prefixWord ++ tailWord_5227804).sum := by decide
  have hdescent : baseEnd_5227804 < baseStart_5227804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227841 : List Nat := [1, 2, 5, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_5227841 : Nat := 118140960795 + 5227841 * 2 ^ 59
def prefixEnd_5227841 : Nat := 4983230072969 + 3 ^ 40 * 5227841 * 2
def baseEnd_5227841 : Nat := 2684395218281585781745103

theorem tailTrace_5227841 : CollatzResearch.WordTrace tailWord_5227841 prefixEnd_5227841 2684395218281585781745103 := by
  unfold tailWord_5227841
  simp only [CollatzResearch.WordTrace]
  refine ⟨190675025853432376004955377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127116683902288250669970251 190675025853432376004955377)
  ·
    refine ⟨143006269390074282003716533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190675025853432376004955377 143006269390074282003716533)
    ·
      refine ⟨13406837755319463937848425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143006269390074282003716533 13406837755319463937848425)
      ·
        refine ⟨10055128316489597953386319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13406837755319463937848425 10055128316489597953386319)
        ·
          refine ⟨15082692474734396930079479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10055128316489597953386319 15082692474734396930079479)
          ·
            refine ⟨22624038712101595395119219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15082692474734396930079479 22624038712101595395119219)
            ·
              refine ⟨33936058068152393092678829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22624038712101595395119219 33936058068152393092678829)
              ·
                refine ⟨12726021775557147409754561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33936058068152393092678829 12726021775557147409754561)
                ·
                  refine ⟨9544516331667860557315921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12726021775557147409754561 9544516331667860557315921)
                  ·
                    refine ⟨7158387248750895417986941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9544516331667860557315921 7158387248750895417986941)
                    ·
                      refine ⟨2684395218281585781745103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7158387248750895417986941 2684395218281585781745103)
                      ·
                        rfl

theorem cell23_5227841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_5227841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227841 prefixEnd_5227841 := by exact prefixLift 5227841
  have htrace : WordTrace (prefixWord ++ tailWord_5227841) baseStart_5227841 baseEnd_5227841 := by
    simpa [prefixWord, tailWord_5227841, baseEnd_5227841] using wordTrace_append hprefix tailTrace_5227841
  have hstable : (prefixWord ++ tailWord_5227841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227841).length < 2 ^ (prefixWord ++ tailWord_5227841).sum := by decide
  have hdescent : baseEnd_5227841 < baseStart_5227841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227874 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 5, 5]
def baseStart_5227874 : Nat := 118140960795 + 5227874 * 2 ^ 59
def prefixEnd_5227874 : Nat := 4983230072969 + 3 ^ 40 * 5227874 * 2
def baseEnd_5227874 : Nat := 894804054381061384210817

theorem tailTrace_5227874 : CollatzResearch.WordTrace tailWord_5227874 prefixEnd_5227874 894804054381061384210817 := by
  unfold tailWord_5227874
  simp only [CollatzResearch.WordTrace]
  refine ⟨47669057365578205660226669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127117486308208548427271117 47669057365578205660226669)
  ·
    refine ⟨17875896512091827122585001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47669057365578205660226669 17875896512091827122585001)
    ·
      refine ⟨13406922384068870341938751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17875896512091827122585001 13406922384068870341938751)
      ·
        refine ⟨20110383576103305512908127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13406922384068870341938751 20110383576103305512908127)
        ·
          refine ⟨30165575364154958269362191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20110383576103305512908127 30165575364154958269362191)
          ·
            refine ⟨45248363046232437404043287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30165575364154958269362191 45248363046232437404043287)
            ·
              refine ⟨67872544569348656106064931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45248363046232437404043287 67872544569348656106064931)
              ·
                refine ⟨101808816854022984159097397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67872544569348656106064931 101808816854022984159097397)
                ·
                  refine ⟨9544576580064654764915381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 101808816854022984159097397 9544576580064654764915381)
                  ·
                    refine ⟨894804054381061384210817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9544576580064654764915381 894804054381061384210817)
                    ·
                      rfl

theorem cell23_5227874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_5227874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227874 prefixEnd_5227874 := by exact prefixLift 5227874
  have htrace : WordTrace (prefixWord ++ tailWord_5227874) baseStart_5227874 baseEnd_5227874 := by
    simpa [prefixWord, tailWord_5227874, baseEnd_5227874] using wordTrace_append hprefix tailTrace_5227874
  have hstable : (prefixWord ++ tailWord_5227874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227874).length < 2 ^ (prefixWord ++ tailWord_5227874).sum := by decide
  have hdescent : baseEnd_5227874 < baseStart_5227874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227908 : List Nat := [2, 3, 2, 1, 1, 5, 2, 1, 1, 5]
def baseStart_5227908 : Nat := 118140960795 + 5227908 * 2 ^ 59
def prefixEnd_5227908 : Nat := 4983230072969 + 3 ^ 40 * 5227908 * 2
def baseEnd_5227908 : Nat := 894809873828479006535765

theorem tailTrace_5227908 : CollatzResearch.WordTrace tailWord_5227908 prefixEnd_5227908 894809873828479006535765 := by
  unfold tailWord_5227908
  simp only [CollatzResearch.WordTrace]
  refine ⟨95338734772094823223822189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127118313029459764298429585 95338734772094823223822189)
  ·
    refine ⟨35752025539535558708933321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95338734772094823223822189 35752025539535558708933321)
    ·
      refine ⟨26814019154651669031699991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35752025539535558708933321 26814019154651669031699991)
      ·
        refine ⟨40221028731977503547549987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26814019154651669031699991 40221028731977503547549987)
        ·
          refine ⟨60331543097966255321324981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40221028731977503547549987 60331543097966255321324981)
          ·
            refine ⟨5656082165434336436374217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60331543097966255321324981 5656082165434336436374217)
            ·
              refine ⟨4242061624075752327280663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5656082165434336436374217 4242061624075752327280663)
              ·
                refine ⟨6363092436113628490920995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4242061624075752327280663 6363092436113628490920995)
                ·
                  refine ⟨9544638654170442736381493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6363092436113628490920995 9544638654170442736381493)
                  ·
                    refine ⟨894809873828479006535765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9544638654170442736381493 894809873828479006535765)
                    ·
                      rfl

theorem cell23_5227908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_5227908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227908 prefixEnd_5227908 := by exact prefixLift 5227908
  have htrace : WordTrace (prefixWord ++ tailWord_5227908) baseStart_5227908 baseEnd_5227908 := by
    simpa [prefixWord, tailWord_5227908, baseEnd_5227908] using wordTrace_append hprefix tailTrace_5227908
  have hstable : (prefixWord ++ tailWord_5227908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227908).length < 2 ^ (prefixWord ++ tailWord_5227908).sum := by decide
  have hdescent : baseEnd_5227908 < baseStart_5227908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227911 : List Nat := [1, 1, 4, 2, 2, 3, 1, 3, 1, 1, 4]
def baseStart_5227911 : Nat := 118140960795 + 5227911 * 2 ^ 59
def prefixEnd_5227911 : Nat := 4983230072969 + 3 ^ 40 * 5227911 * 2
def baseEnd_5227911 : Nat := 2684431161927400507869781

theorem tailTrace_5227911 : CollatzResearch.WordTrace tailWord_5227911 prefixEnd_5227911 2684431161927400507869781 := by
  unfold tailWord_5227911
  simp only [CollatzResearch.WordTrace]
  refine ⟨190677578963178777960003587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127118385975452518640002391 190677578963178777960003587)
  ·
    refine ⟨286016368444768166940005381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190677578963178777960003587 286016368444768166940005381)
    ·
      refine ⟨53628069083394031301251009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 286016368444768166940005381 53628069083394031301251009)
      ·
        refine ⟨40221051812545523475938257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53628069083394031301251009 40221051812545523475938257)
        ·
          refine ⟨30165788859409142606953693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40221051812545523475938257 30165788859409142606953693)
          ·
            refine ⟨11312170822278428477607635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30165788859409142606953693 11312170822278428477607635)
            ·
              refine ⟨16968256233417642716411453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11312170822278428477607635 16968256233417642716411453)
              ·
                refine ⟨6363096087531616018654295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16968256233417642716411453 6363096087531616018654295)
                ·
                  refine ⟨9544644131297424027981443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6363096087531616018654295 9544644131297424027981443)
                  ·
                    refine ⟨14316966196946136041972165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9544644131297424027981443 14316966196946136041972165)
                    ·
                      refine ⟨2684431161927400507869781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14316966196946136041972165 2684431161927400507869781)
                      ·
                        rfl

theorem cell23_5227911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_5227911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227911 prefixEnd_5227911 := by exact prefixLift 5227911
  have htrace : WordTrace (prefixWord ++ tailWord_5227911) baseStart_5227911 baseEnd_5227911 := by
    simpa [prefixWord, tailWord_5227911, baseEnd_5227911] using wordTrace_append hprefix tailTrace_5227911
  have hstable : (prefixWord ++ tailWord_5227911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227911).length < 2 ^ (prefixWord ++ tailWord_5227911).sum := by decide
  have hdescent : baseEnd_5227911 < baseStart_5227911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227927 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 7]
def baseStart_5227927 : Nat := 118140960795 + 5227927 * 2 ^ 59
def prefixEnd_5227927 : Nat := 4983230072969 + 3 ^ 40 * 5227927 * 2
def baseEnd_5227927 : Nat := 2684439377617872445269707

theorem tailTrace_5227927 : CollatzResearch.WordTrace tailWord_5227927 prefixEnd_5227927 2684439377617872445269707 := by
  unfold tailWord_5227927
  simp only [CollatzResearch.WordTrace]
  refine ⟨190678162531120812692586035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127118775020747208461724023 190678162531120812692586035)
  ·
    refine ⟨286017243796681219038879053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190678162531120812692586035 286017243796681219038879053)
    ·
      refine ⟨107256466423755457139579645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 286017243796681219038879053 107256466423755457139579645)
      ·
        refine ⟨40221174908908296427342367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107256466423755457139579645 40221174908908296427342367)
        ·
          refine ⟨60331762363362444641013551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40221174908908296427342367 60331762363362444641013551)
          ·
            refine ⟨90497643545043666961520327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60331762363362444641013551 90497643545043666961520327)
            ·
              refine ⟨135746465317565500442280491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90497643545043666961520327 135746465317565500442280491)
              ·
                refine ⟨203619697976348250663420737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135746465317565500442280491 203619697976348250663420737)
                ·
                  refine ⟨152714773482261187997565553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203619697976348250663420737 152714773482261187997565553)
                  ·
                    refine ⟨114536080111695890998174165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 152714773482261187997565553 114536080111695890998174165)
                    ·
                      refine ⟨2684439377617872445269707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114536080111695890998174165 2684439377617872445269707)
                      ·
                        rfl

theorem cell23_5227927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_5227927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227927 prefixEnd_5227927 := by exact prefixLift 5227927
  have htrace : WordTrace (prefixWord ++ tailWord_5227927) baseStart_5227927 baseEnd_5227927 := by
    simpa [prefixWord, tailWord_5227927, baseEnd_5227927] using wordTrace_append hprefix tailTrace_5227927
  have hstable : (prefixWord ++ tailWord_5227927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227927).length < 2 ^ (prefixWord ++ tailWord_5227927).sum := by decide
  have hdescent : baseEnd_5227927 < baseStart_5227927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5227967 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 8]
def baseStart_5227967 : Nat := 118140960795 + 5227967 * 2 ^ 59
def prefixEnd_5227967 : Nat := 4983230072969 + 3 ^ 40 * 5227967 * 2
def baseEnd_5227967 : Nat := 2684459916844052288769523

theorem tailTrace_5227967 : CollatzResearch.WordTrace tailWord_5227967 prefixEnd_5227967 2684459916844052288769523 := by
  unfold tailWord_5227967
  simp only [CollatzResearch.WordTrace]
  refine ⟨190679621450975899524042155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127119747633983933016028103 190679621450975899524042155)
  ·
    refine ⟨286019432176463849286063233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190679621450975899524042155 286019432176463849286063233)
    ·
      refine ⟨214514574132347886964547425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286019432176463849286063233 214514574132347886964547425)
      ·
        refine ⟨160885930599260915223410569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214514574132347886964547425 160885930599260915223410569)
        ·
          refine ⟨120664447949445686417557927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160885930599260915223410569 120664447949445686417557927)
          ·
            refine ⟨180996671924168529626336891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120664447949445686417557927 180996671924168529626336891)
            ·
              refine ⟨271495007886252794439505337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180996671924168529626336891 271495007886252794439505337)
              ·
                refine ⟨203621255914689595829629003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271495007886252794439505337 203621255914689595829629003)
                ·
                  refine ⟨305431883872034393744443505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203621255914689595829629003 305431883872034393744443505)
                  ·
                    refine ⟨229073912904025795308332629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 305431883872034393744443505 229073912904025795308332629)
                    ·
                      refine ⟨2684459916844052288769523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 229073912904025795308332629 2684459916844052288769523)
                      ·
                        rfl

theorem cell23_5227967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_5227967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5227967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5227967 prefixEnd_5227967 := by exact prefixLift 5227967
  have htrace : WordTrace (prefixWord ++ tailWord_5227967) baseStart_5227967 baseEnd_5227967 := by
    simpa [prefixWord, tailWord_5227967, baseEnd_5227967] using wordTrace_append hprefix tailTrace_5227967
  have hstable : (prefixWord ++ tailWord_5227967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5227967).length < 2 ^ (prefixWord ++ tailWord_5227967).sum := by decide
  have hdescent : baseEnd_5227967 < baseStart_5227967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5227967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228005 : List Nat := [1, 3, 1, 5, 1, 1, 3, 2, 1, 3, 2]
def baseStart_5228005 : Nat := 118140960795 + 5228005 * 2 ^ 59
def prefixEnd_5228005 : Nat := 4983230072969 + 3 ^ 40 * 5228005 * 2
def baseEnd_5228005 : Nat := 2684479429108923140094349

theorem tailTrace_5228005 : CollatzResearch.WordTrace tailWord_5228005 prefixEnd_5228005 2684479429108923140094349 := by
  unfold tailWord_5228005
  simp only [CollatzResearch.WordTrace]
  refine ⟨190681007424838232013925469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127120671616558821342616979 190681007424838232013925469)
  ·
    refine ⟨71505377784314337005222051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190681007424838232013925469 71505377784314337005222051)
    ·
      refine ⟨107258066676471505507833077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71505377784314337005222051 107258066676471505507833077)
      ·
        refine ⟨10055443750919203641359351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107258066676471505507833077 10055443750919203641359351)
        ·
          refine ⟨15083165626378805462039027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10055443750919203641359351 15083165626378805462039027)
          ·
            refine ⟨22624748439568208193058541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15083165626378805462039027 22624748439568208193058541)
            ·
              refine ⟨8484280664838078072396953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22624748439568208193058541 8484280664838078072396953)
              ·
                refine ⟨6363210498628558554297715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8484280664838078072396953 6363210498628558554297715)
                ·
                  refine ⟨9544815747942837831446573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6363210498628558554297715 9544815747942837831446573)
                  ·
                    refine ⟨3579305905478564186792465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9544815747942837831446573 3579305905478564186792465)
                    ·
                      refine ⟨2684479429108923140094349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3579305905478564186792465 2684479429108923140094349)
                      ·
                        rfl

theorem cell23_5228005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_5228005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228005 prefixEnd_5228005 := by exact prefixLift 5228005
  have htrace : WordTrace (prefixWord ++ tailWord_5228005) baseStart_5228005 baseEnd_5228005 := by
    simpa [prefixWord, tailWord_5228005, baseEnd_5228005] using wordTrace_append hprefix tailTrace_5228005
  have hstable : (prefixWord ++ tailWord_5228005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228005).length < 2 ^ (prefixWord ++ tailWord_5228005).sum := by decide
  have hdescent : baseEnd_5228005 < baseStart_5228005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228018 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 3, 4, 2]
def baseStart_5228018 : Nat := 118140960795 + 5228018 * 2 ^ 59
def prefixEnd_5228018 : Nat := 4983230072969 + 3 ^ 40 * 5228018 * 2
def baseEnd_5228018 : Nat := 2684486104357431589231789

theorem tailTrace_5228018 : CollatzResearch.WordTrace tailWord_5228018 prefixEnd_5228018 2684486104357431589231789 := by
  unfold tailWord_5228018
  simp only [CollatzResearch.WordTrace]
  refine ⟨47670370393447783808537177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127120987715860756822765805 47670370393447783808537177)
  ·
    refine ⟨35752777795085837856402883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47670370393447783808537177 35752777795085837856402883)
    ·
      refine ⟨53629166692628756784604325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35752777795085837856402883 53629166692628756784604325)
      ·
        refine ⟨10055468754867891897113311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53629166692628756784604325 10055468754867891897113311)
        ·
          refine ⟨15083203132301837845669967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10055468754867891897113311 15083203132301837845669967)
          ·
            refine ⟨22624804698452756768504951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15083203132301837845669967 22624804698452756768504951)
            ·
              refine ⟨33937207047679135152757427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22624804698452756768504951 33937207047679135152757427)
              ·
                refine ⟨50905810571518702729136141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33937207047679135152757427 50905810571518702729136141)
                ·
                  refine ⟨19089678964319513523426053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50905810571518702729136141 19089678964319513523426053)
                  ·
                    refine ⟨3579314805809908785642385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19089678964319513523426053 3579314805809908785642385)
                    ·
                      refine ⟨2684486104357431589231789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3579314805809908785642385 2684486104357431589231789)
                      ·
                        rfl

theorem cell23_5228018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_5228018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228018 prefixEnd_5228018 := by exact prefixLift 5228018
  have htrace : WordTrace (prefixWord ++ tailWord_5228018) baseStart_5228018 baseEnd_5228018 := by
    simpa [prefixWord, tailWord_5228018, baseEnd_5228018] using wordTrace_append hprefix tailTrace_5228018
  have hstable : (prefixWord ++ tailWord_5228018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228018).length < 2 ^ (prefixWord ++ tailWord_5228018).sum := by decide
  have hdescent : baseEnd_5228018 < baseStart_5228018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228022 : List Nat := [5, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2]
def baseStart_5228022 : Nat := 118140960795 + 5228022 * 2 ^ 59
def prefixEnd_5228022 : Nat := 4983230072969 + 3 ^ 40 * 5228022 * 2
def baseEnd_5228022 : Nat := 2684488158280049573581771

theorem tailTrace_5228022 : CollatzResearch.WordTrace tailWord_5228022 prefixEnd_5228022 2684488158280049573581771 := by
  unfold tailWord_5228022
  simp only [CollatzResearch.WordTrace]
  refine ⟨11917601716611040244830895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127121084977184429278196213 11917601716611040244830895)
  ·
    refine ⟨17876402574916560367246343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11917601716611040244830895 17876402574916560367246343)
    ·
      refine ⟨26814603862374840550869515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17876402574916560367246343 26814603862374840550869515)
      ·
        refine ⟨40221905793562260826304273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26814603862374840550869515 40221905793562260826304273)
        ·
          refine ⟨30166429345171695619728205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40221905793562260826304273 30166429345171695619728205)
          ·
            refine ⟨11312411004439385857398077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30166429345171695619728205 11312411004439385857398077)
            ·
              refine ⟨4242154126664769696524279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11312411004439385857398077 4242154126664769696524279)
              ·
                refine ⟨6363231189997154544786419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4242154126664769696524279 6363231189997154544786419)
                ·
                  refine ⟨9544846784995731817179629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6363231189997154544786419 9544846784995731817179629)
                  ·
                    refine ⟨3579317544373399431442361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9544846784995731817179629 3579317544373399431442361)
                    ·
                      refine ⟨2684488158280049573581771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3579317544373399431442361 2684488158280049573581771)
                      ·
                        rfl

theorem cell23_5228022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_5228022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228022 prefixEnd_5228022 := by exact prefixLift 5228022
  have htrace : WordTrace (prefixWord ++ tailWord_5228022) baseStart_5228022 baseEnd_5228022 := by
    simpa [prefixWord, tailWord_5228022, baseEnd_5228022] using wordTrace_append hprefix tailTrace_5228022
  have hstable : (prefixWord ++ tailWord_5228022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228022).length < 2 ^ (prefixWord ++ tailWord_5228022).sum := by decide
  have hdescent : baseEnd_5228022 < baseStart_5228022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228041 : List Nat := [1, 2, 1, 1, 3, 1, 5, 4, 5]
def baseStart_5228041 : Nat := 118140960795 + 5228041 * 2 ^ 59
def prefixEnd_5228041 : Nat := 4983230072969 + 3 ^ 40 * 5228041 * 2
def baseEnd_5228041 : Nat := 298277546045831666582687

theorem tailTrace_5228041 : CollatzResearch.WordTrace tailWord_5228041 prefixEnd_5228041 298277546045831666582687 := by
  unfold tailWord_5228041
  simp only [CollatzResearch.WordTrace]
  refine ⟨190682320452707810162235977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127121546968471873441490651 190682320452707810162235977)
  ·
    refine ⟨143011740339530857621676983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190682320452707810162235977 143011740339530857621676983)
    ·
      refine ⟨214517610509296286432515475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143011740339530857621676983 214517610509296286432515475)
      ·
        refine ⟨321776415763944429648773213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214517610509296286432515475 321776415763944429648773213)
        ·
          refine ⟨120666155911479161118289955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 321776415763944429648773213 120666155911479161118289955)
          ·
            refine ⟨180999233867218741677434933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120666155911479161118289955 180999233867218741677434933)
            ·
              refine ⟨16968678175051757032259525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 180999233867218741677434933 16968678175051757032259525)
              ·
                refine ⟨3181627157822204443548661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16968678175051757032259525 3181627157822204443548661)
                ·
                  refine ⟨298277546045831666582687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3181627157822204443548661 298277546045831666582687)
                  ·
                    rfl

theorem cell23_5228041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 5].length) (baseStart_5228041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228041 prefixEnd_5228041 := by exact prefixLift 5228041
  have htrace : WordTrace (prefixWord ++ tailWord_5228041) baseStart_5228041 baseEnd_5228041 := by
    simpa [prefixWord, tailWord_5228041, baseEnd_5228041] using wordTrace_append hprefix tailTrace_5228041
  have hstable : (prefixWord ++ tailWord_5228041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228041).length < 2 ^ (prefixWord ++ tailWord_5228041).sum := by decide
  have hdescent : baseEnd_5228041 < baseStart_5228041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228045 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_5228045 : Nat := 118140960795 + 5228045 * 2 ^ 59
def prefixEnd_5228045 : Nat := 4983230072969 + 3 ^ 40 * 5228045 * 2
def baseEnd_5228045 : Nat := 894833322778367661198055

theorem tailTrace_5228045 : CollatzResearch.WordTrace tailWord_5228045 prefixEnd_5228045 894833322778367661198055 := by
  unfold tailWord_5228045
  simp only [CollatzResearch.WordTrace]
  refine ⟨190682466344693318845381589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127121644229795545896921059 190682466344693318845381589)
  ·
    refine ⟨4469120304953749660438631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 190682466344693318845381589 4469120304953749660438631)
    ·
      refine ⟨6703680457430624490657947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4469120304953749660438631 6703680457430624490657947)
      ·
        refine ⟨10055520686145936735986921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6703680457430624490657947 10055520686145936735986921)
        ·
          refine ⟨7541640514609452551990191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10055520686145936735986921 7541640514609452551990191)
          ·
            refine ⟨11312460771914178827985287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7541640514609452551990191 11312460771914178827985287)
            ·
              refine ⟨16968691157871268241977931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11312460771914178827985287 16968691157871268241977931)
              ·
                refine ⟨25453036736806902362966897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16968691157871268241977931 25453036736806902362966897)
                ·
                  refine ⟨19089777552605176772225173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25453036736806902362966897 19089777552605176772225173)
                  ·
                    refine ⟨894833322778367661198055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19089777552605176772225173 894833322778367661198055)
                    ·
                      rfl

theorem cell23_5228045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_5228045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228045 prefixEnd_5228045 := by exact prefixLift 5228045
  have htrace : WordTrace (prefixWord ++ tailWord_5228045) baseStart_5228045 baseEnd_5228045 := by
    simpa [prefixWord, tailWord_5228045, baseEnd_5228045] using wordTrace_append hprefix tailTrace_5228045
  have hstable : (prefixWord ++ tailWord_5228045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228045).length < 2 ^ (prefixWord ++ tailWord_5228045).sum := by decide
  have hdescent : baseEnd_5228045 < baseStart_5228045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228051 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 3]
def baseStart_5228051 : Nat := 118140960795 + 5228051 * 2 ^ 59
def prefixEnd_5228051 : Nat := 4983230072969 + 3 ^ 40 * 5228051 * 2
def baseEnd_5228051 : Nat := 2684503049219029960119137

theorem tailTrace_5228051 : CollatzResearch.WordTrace tailWord_5228051 prefixEnd_5228051 2684503049219029960119137 := by
  unfold tailWord_5228051
  simp only [CollatzResearch.WordTrace]
  refine ⟨190682685182671581870100007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127121790121781054580066671 190682685182671581870100007)
  ·
    refine ⟨286024027774007372805150011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190682685182671581870100007 286024027774007372805150011)
    ·
      refine ⟨429036041661011059207725017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286024027774007372805150011 429036041661011059207725017)
      ·
        refine ⟨321777031245758294405793763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429036041661011059207725017 321777031245758294405793763)
        ·
          refine ⟨482665546868637441608690645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321777031245758294405793763 482665546868637441608690645)
          ·
            refine ⟨11312473754733690037703687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 482665546868637441608690645 11312473754733690037703687)
            ·
              refine ⟨16968710632100535056555531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11312473754733690037703687 16968710632100535056555531)
              ·
                refine ⟨25453065948150802584833297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16968710632100535056555531 25453065948150802584833297)
                ·
                  refine ⟨19089799461113101938624973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25453065948150802584833297 19089799461113101938624973)
                  ·
                    refine ⟨7158674797917413226984365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19089799461113101938624973 7158674797917413226984365)
                    ·
                      refine ⟨2684503049219029960119137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7158674797917413226984365 2684503049219029960119137)
                      ·
                        rfl

theorem cell23_5228051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 3].length) (baseStart_5228051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228051 prefixEnd_5228051 := by exact prefixLift 5228051
  have htrace : WordTrace (prefixWord ++ tailWord_5228051) baseStart_5228051 baseEnd_5228051 := by
    simpa [prefixWord, tailWord_5228051, baseEnd_5228051] using wordTrace_append hprefix tailTrace_5228051
  have hstable : (prefixWord ++ tailWord_5228051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228051).length < 2 ^ (prefixWord ++ tailWord_5228051).sum := by decide
  have hdescent : baseEnd_5228051 < baseStart_5228051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228052 : List Nat := [2, 4, 3, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_5228052 : Nat := 118140960795 + 5228052 * 2 ^ 59
def prefixEnd_5228052 : Nat := 4983230072969 + 3 ^ 40 * 5228052 * 2
def baseEnd_5228052 : Nat := 2684503562699684456206633

theorem tailTrace_5228052 : CollatzResearch.WordTrace tailWord_5228052 prefixEnd_5228052 2684503562699684456206633 := by
  unfold tailWord_5228052
  simp only [CollatzResearch.WordTrace]
  refine ⟨95341360827833979520443205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127121814437111972693924273 95341360827833979520443205)
  ·
    refine ⟨17876505155218871160083101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95341360827833979520443205 17876505155218871160083101)
    ·
      refine ⟨6703689433207076685031163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17876505155218871160083101 6703689433207076685031163)
      ·
        refine ⟨10055534149810615027546745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6703689433207076685031163 10055534149810615027546745)
        ·
          refine ⟨7541650612357961270660059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10055534149810615027546745 7541650612357961270660059)
          ·
            refine ⟨11312475918536941905990089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7541650612357961270660059 11312475918536941905990089)
            ·
              refine ⟨8484356938902706429492567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11312475918536941905990089 8484356938902706429492567)
              ·
                refine ⟨12726535408354059644238851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8484356938902706429492567 12726535408354059644238851)
                ·
                  refine ⟨19089803112531089466358277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12726535408354059644238851 19089803112531089466358277)
                  ·
                    refine ⟨3579338083599579274942177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19089803112531089466358277 3579338083599579274942177)
                    ·
                      refine ⟨2684503562699684456206633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3579338083599579274942177 2684503562699684456206633)
                      ·
                        rfl

theorem cell23_5228052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_5228052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228052 prefixEnd_5228052 := by exact prefixLift 5228052
  have htrace : WordTrace (prefixWord ++ tailWord_5228052) baseStart_5228052 baseEnd_5228052 := by
    simpa [prefixWord, tailWord_5228052, baseEnd_5228052] using wordTrace_append hprefix tailTrace_5228052
  have hstable : (prefixWord ++ tailWord_5228052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228052).length < 2 ^ (prefixWord ++ tailWord_5228052).sum := by decide
  have hdescent : baseEnd_5228052 < baseStart_5228052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228086 : List Nat := [5, 1, 2, 1, 4, 1, 1, 2, 2, 2, 2]
def baseStart_5228086 : Nat := 118140960795 + 5228086 * 2 ^ 59
def prefixEnd_5228086 : Nat := 4983230072969 + 3 ^ 40 * 5228086 * 2
def baseEnd_5228086 : Nat := 2684521021041937323181477

theorem tailTrace_5228086 : CollatzResearch.WordTrace tailWord_5228086 prefixEnd_5228086 2684521021041937323181477 := by
  unfold tailWord_5228086
  simp only [CollatzResearch.WordTrace]
  refine ⟨11917747608596548927976507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127122641158363188565082741 11917747608596548927976507)
  ·
    refine ⟨17876621412894823391964761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11917747608596548927976507 17876621412894823391964761)
    ·
      refine ⟨13407466059671117543973571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17876621412894823391964761 13407466059671117543973571)
      ·
        refine ⟨20111199089506676315960357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13407466059671117543973571 20111199089506676315960357)
        ·
          refine ⟨3770849829282501809242567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20111199089506676315960357 3770849829282501809242567)
          ·
            refine ⟨5656274743923752713863851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3770849829282501809242567 5656274743923752713863851)
            ·
              refine ⟨8484412115885629070795777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5656274743923752713863851 8484412115885629070795777)
              ·
                refine ⟨6363309086914221803096833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8484412115885629070795777 6363309086914221803096833)
                ·
                  refine ⟨4772481815185666352322625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6363309086914221803096833 4772481815185666352322625)
                  ·
                    refine ⟨3579361361389249764241969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4772481815185666352322625 3579361361389249764241969)
                    ·
                      refine ⟨2684521021041937323181477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3579361361389249764241969 2684521021041937323181477)
                      ·
                        rfl

theorem cell23_5228086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_5228086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228086 prefixEnd_5228086 := by exact prefixLift 5228086
  have htrace : WordTrace (prefixWord ++ tailWord_5228086) baseStart_5228086 baseEnd_5228086 := by
    simpa [prefixWord, tailWord_5228086, baseEnd_5228086] using wordTrace_append hprefix tailTrace_5228086
  have hstable : (prefixWord ++ tailWord_5228086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228086).length < 2 ^ (prefixWord ++ tailWord_5228086).sum := by decide
  have hdescent : baseEnd_5228086 < baseStart_5228086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228108 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 2, 4, 2]
def baseStart_5228108 : Nat := 118140960795 + 5228108 * 2 ^ 59
def prefixEnd_5228108 : Nat := 4983230072969 + 3 ^ 40 * 5228108 * 2
def baseEnd_5228108 : Nat := 2684532317616336237106375

theorem tailTrace_5228108 : CollatzResearch.WordTrace tailWord_5228108 prefixEnd_5228108 2684532317616336237106375 := by
  unfold tailWord_5228108
  simp only [CollatzResearch.WordTrace]
  refine ⟨95342382071732540302462489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127123176095643387069949985 95342382071732540302462489)
  ·
    refine ⟨71506786553799405226846867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95342382071732540302462489 71506786553799405226846867)
    ·
      refine ⟨107260179830699107840270301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71506786553799405226846867 107260179830699107840270301)
      ·
        refine ⟨40222567436512165440101363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107260179830699107840270301 40222567436512165440101363)
        ·
          refine ⟨60333851154768248160152045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40222567436512165440101363 60333851154768248160152045)
          ·
            refine ⟨22625194183038093060057017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60333851154768248160152045 22625194183038093060057017)
            ·
              refine ⟨16968895637278569795042763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22625194183038093060057017 16968895637278569795042763)
              ·
                refine ⟨25453343455917854692564145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16968895637278569795042763 25453343455917854692564145)
                ·
                  refine ⟨19090007591938391019423109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25453343455917854692564145 19090007591938391019423109)
                  ·
                    refine ⟨3579376423488448316141833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19090007591938391019423109 3579376423488448316141833)
                    ·
                      refine ⟨2684532317616336237106375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3579376423488448316141833 2684532317616336237106375)
                      ·
                        rfl

theorem cell23_5228108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_5228108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228108 prefixEnd_5228108 := by exact prefixLift 5228108
  have htrace : WordTrace (prefixWord ++ tailWord_5228108) baseStart_5228108 baseEnd_5228108 := by
    simpa [prefixWord, tailWord_5228108, baseEnd_5228108] using wordTrace_append hprefix tailTrace_5228108
  have hstable : (prefixWord ++ tailWord_5228108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228108).length < 2 ^ (prefixWord ++ tailWord_5228108).sum := by decide
  have hdescent : baseEnd_5228108 < baseStart_5228108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228135 : List Nat := [1, 1, 5, 1, 1, 1, 5, 3, 1, 4]
def baseStart_5228135 : Nat := 118140960795 + 5228135 * 2 ^ 59
def prefixEnd_5228135 : Nat := 4983230072969 + 3 ^ 40 * 5228135 * 2
def baseEnd_5228135 : Nat := 894848727198002543822917

theorem tailTrace_5228135 : CollatzResearch.WordTrace tailWord_5228135 prefixEnd_5228135 894848727198002543822917 := by
  unfold tailWord_5228135
  simp only [CollatzResearch.WordTrace]
  refine ⟨190685748914367264216157859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127123832609578176144105239 190685748914367264216157859)
  ·
    refine ⟨286028623371550896324236789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190685748914367264216157859 286028623371550896324236789)
    ·
      refine ⟨26815183441082896530397199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 286028623371550896324236789 26815183441082896530397199)
      ·
        refine ⟨40222775161624344795595799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26815183441082896530397199 40222775161624344795595799)
        ·
          refine ⟨60334162742436517193393699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40222775161624344795595799 60334162742436517193393699)
          ·
            refine ⟨90501244113654775790090549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60334162742436517193393699 90501244113654775790090549)
            ·
              refine ⟨8484491635655135230320989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90501244113654775790090549 8484491635655135230320989)
              ·
                refine ⟨3181684363370675711370371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8484491635655135230320989 3181684363370675711370371)
                ·
                  refine ⟨4772526545056013567055557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3181684363370675711370371 4772526545056013567055557)
                  ·
                    refine ⟨894848727198002543822917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4772526545056013567055557 894848727198002543822917)
                    ·
                      rfl

theorem cell23_5228135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_5228135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228135 prefixEnd_5228135 := by exact prefixLift 5228135
  have htrace : WordTrace (prefixWord ++ tailWord_5228135) baseStart_5228135 baseEnd_5228135 := by
    simpa [prefixWord, tailWord_5228135, baseEnd_5228135] using wordTrace_append hprefix tailTrace_5228135
  have hstable : (prefixWord ++ tailWord_5228135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228135).length < 2 ^ (prefixWord ++ tailWord_5228135).sum := by decide
  have hdescent : baseEnd_5228135 < baseStart_5228135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228208 : List Nat := [2, 1, 1, 1, 2, 1, 5, 4, 2, 4]
def baseStart_5228208 : Nat := 118140960795 + 5228208 * 2 ^ 59
def prefixEnd_5228208 : Nat := 4983230072969 + 3 ^ 40 * 5228208 * 2
def baseEnd_5228208 : Nat := 894861221893928615285305

theorem tailTrace_5228208 : CollatzResearch.WordTrace tailWord_5228208 prefixEnd_5228208 894861221893928615285305 := by
  unfold tailWord_5228208
  simp only [CollatzResearch.WordTrace]
  refine ⟨95344205721551398841782639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127125607628735198455710185 95344205721551398841782639)
  ·
    refine ⟨143016308582327098262673959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95344205721551398841782639 143016308582327098262673959)
    ·
      refine ⟨214524462873490647394010939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143016308582327098262673959 214524462873490647394010939)
      ·
        refine ⟨321786694310235971091016409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214524462873490647394010939 321786694310235971091016409)
        ·
          refine ⟨241340020732676978318262307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321786694310235971091016409 241340020732676978318262307)
          ·
            refine ⟨362010031099015467477393461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241340020732676978318262307 362010031099015467477393461)
            ·
              refine ⟨33938440415532700076005637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 362010031099015467477393461 33938440415532700076005637)
              ·
                refine ⟨6363457577912381264251057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33938440415532700076005637 6363457577912381264251057)
                ·
                  refine ⟨4772593183434285948188293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6363457577912381264251057 4772593183434285948188293)
                  ·
                    refine ⟨894861221893928615285305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4772593183434285948188293 894861221893928615285305)
                    ·
                      rfl

theorem cell23_5228208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 2, 4].length) (baseStart_5228208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228208 prefixEnd_5228208 := by exact prefixLift 5228208
  have htrace : WordTrace (prefixWord ++ tailWord_5228208) baseStart_5228208 baseEnd_5228208 := by
    simpa [prefixWord, tailWord_5228208, baseEnd_5228208] using wordTrace_append hprefix tailTrace_5228208
  have hstable : (prefixWord ++ tailWord_5228208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228208).length < 2 ^ (prefixWord ++ tailWord_5228208).sum := by decide
  have hdescent : baseEnd_5228208 < baseStart_5228208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228211 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 4]
def baseStart_5228211 : Nat := 118140960795 + 5228211 * 2 ^ 59
def prefixEnd_5228211 : Nat := 4983230072969 + 3 ^ 40 * 5228211 * 2
def baseEnd_5228211 : Nat := 2684585206123749334118401

theorem tailTrace_5228211 : CollatzResearch.WordTrace tailWord_5228211 prefixEnd_5228211 2684585206123749334118401 := by
  unfold tailWord_5228211
  simp only [CollatzResearch.WordTrace]
  refine ⟨190688520862091929195924487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127125680574727952797282991 190688520862091929195924487)
  ·
    refine ⟨286032781293137893793886731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190688520862091929195924487 286032781293137893793886731)
    ·
      refine ⟨429049171939706840690830097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286032781293137893793886731 429049171939706840690830097)
      ·
        refine ⟨321786878954780130518122573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429049171939706840690830097 321786878954780130518122573)
        ·
          refine ⟨120670079608042548944295965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 321786878954780130518122573 120670079608042548944295965)
          ·
            refine ⟨45251279853015955854110987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120670079608042548944295965 45251279853015955854110987)
            ·
              refine ⟨67876919779523933781166481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45251279853015955854110987 67876919779523933781166481)
              ·
                refine ⟨50907689834642950335874861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67876919779523933781166481 50907689834642950335874861)
                ·
                  refine ⟨19090383687991106375953073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50907689834642950335874861 19090383687991106375953073)
                  ·
                    refine ⟨14317787765993329781964805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19090383687991106375953073 14317787765993329781964805)
                    ·
                      refine ⟨2684585206123749334118401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14317787765993329781964805 2684585206123749334118401)
                      ·
                        rfl

theorem cell23_5228211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 4].length) (baseStart_5228211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228211 prefixEnd_5228211 := by exact prefixLift 5228211
  have htrace : WordTrace (prefixWord ++ tailWord_5228211) baseStart_5228211 baseEnd_5228211 := by
    simpa [prefixWord, tailWord_5228211, baseEnd_5228211] using wordTrace_append hprefix tailTrace_5228211
  have hstable : (prefixWord ++ tailWord_5228211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228211).length < 2 ^ (prefixWord ++ tailWord_5228211).sum := by decide
  have hdescent : baseEnd_5228211 < baseStart_5228211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228218 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3]
def baseStart_5228218 : Nat := 118140960795 + 5228218 * 2 ^ 59
def prefixEnd_5228218 : Nat := 4983230072969 + 3 ^ 40 * 5228218 * 2
def baseEnd_5228218 : Nat := 2684588800488330806730869

theorem tailTrace_5228218 : CollatzResearch.WordTrace tailWord_5228218 prefixEnd_5228218 2684588800488330806730869 := by
  unfold tailWord_5228218
  simp only [CollatzResearch.WordTrace]
  refine ⟨47672194043266642347857327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127125850782044379594286205 47672194043266642347857327)
  ·
    refine ⟨71508291064899963521785991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47672194043266642347857327 71508291064899963521785991)
    ·
      refine ⟨107262436597349945282678987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71508291064899963521785991 107262436597349945282678987)
      ·
        refine ⟨160893654896024917924018481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107262436597349945282678987 160893654896024917924018481)
        ·
          refine ⟨120670241172018688443013861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160893654896024917924018481 120670241172018688443013861)
          ·
            refine ⟨22625670219753504083065099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120670241172018688443013861 22625670219753504083065099)
            ·
              refine ⟨33938505329630256124597649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22625670219753504083065099 33938505329630256124597649)
              ·
                refine ⟨25453878997222692093448237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33938505329630256124597649 25453878997222692093448237)
                ·
                  refine ⟨9545204623958509535043089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25453878997222692093448237 9545204623958509535043089)
                  ·
                    refine ⟨7158903467968882151282317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9545204623958509535043089 7158903467968882151282317)
                    ·
                      refine ⟨2684588800488330806730869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7158903467968882151282317 2684588800488330806730869)
                      ·
                        rfl

theorem cell23_5228218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3].length) (baseStart_5228218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228218 prefixEnd_5228218 := by exact prefixLift 5228218
  have htrace : WordTrace (prefixWord ++ tailWord_5228218) baseStart_5228218 baseEnd_5228218 := by
    simpa [prefixWord, tailWord_5228218, baseEnd_5228218] using wordTrace_append hprefix tailTrace_5228218
  have hstable : (prefixWord ++ tailWord_5228218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228218).length < 2 ^ (prefixWord ++ tailWord_5228218).sum := by decide
  have hdescent : baseEnd_5228218 < baseStart_5228218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228226 : List Nat := [3, 5, 1, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_5228226 : Nat := 118140960795 + 5228226 * 2 ^ 59
def prefixEnd_5228226 : Nat := 4983230072969 + 3 ^ 40 * 5228226 * 2
def baseEnd_5228226 : Nat := 2684592908333566775430833

theorem tailTrace_5228226 : CollatzResearch.WordTrace tailWord_5228226 prefixEnd_5228226 2684592908333566775430833 := by
  unfold tailWord_5228226
  simp only [CollatzResearch.WordTrace]
  refine ⟨47672266989259396689430133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127126045304691724505147021 47672266989259396689430133)
  ·
    refine ⟨4469275030243068439634075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47672266989259396689430133 4469275030243068439634075)
    ·
      refine ⟨6703912545364602659451113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4469275030243068439634075 6703912545364602659451113)
      ·
        refine ⟨5027934409023451994588335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6703912545364602659451113 5027934409023451994588335)
        ·
          refine ⟨7541901613535177991882503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5027934409023451994588335 7541901613535177991882503)
          ·
            refine ⟨11312852420302766987823755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7541901613535177991882503 11312852420302766987823755)
            ·
              refine ⟨16969278630454150481735633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11312852420302766987823755 16969278630454150481735633)
              ·
                refine ⟨12726958972840612861301725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16969278630454150481735633 12726958972840612861301725)
                ·
                  refine ⟨4772609614815229822988147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12726958972840612861301725 4772609614815229822988147)
                  ·
                    refine ⟨7158914422222844734482221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4772609614815229822988147 7158914422222844734482221)
                    ·
                      refine ⟨2684592908333566775430833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7158914422222844734482221 2684592908333566775430833)
                      ·
                        rfl

theorem cell23_5228226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_5228226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228226 prefixEnd_5228226 := by exact prefixLift 5228226
  have htrace : WordTrace (prefixWord ++ tailWord_5228226) baseStart_5228226 baseEnd_5228226 := by
    simpa [prefixWord, tailWord_5228226, baseEnd_5228226] using wordTrace_append hprefix tailTrace_5228226
  have hstable : (prefixWord ++ tailWord_5228226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228226).length < 2 ^ (prefixWord ++ tailWord_5228226).sum := by decide
  have hdescent : baseEnd_5228226 < baseStart_5228226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228238 : List Nat := [4, 1, 1, 1, 3, 1, 5, 7]
def baseStart_5228238 : Nat := 118140960795 + 5228238 * 2 ^ 59
def prefixEnd_5228238 : Nat := 4983230072969 + 3 ^ 40 * 5228238 * 2
def baseEnd_5228238 : Nat := 99429595188941508462251

theorem tailTrace_5228238 : CollatzResearch.WordTrace tailWord_5228238 prefixEnd_5228238 99429595188941508462251 := by
  unfold tailWord_5228238
  simp only [CollatzResearch.WordTrace]
  refine ⟨23836188204124264100894671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127126337088662741871438245 23836188204124264100894671)
  ·
    refine ⟨35754282306186396151342007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23836188204124264100894671 35754282306186396151342007)
    ·
      refine ⟨53631423459279594227013011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35754282306186396151342007 53631423459279594227013011)
      ·
        refine ⟨80447135188919391340519517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53631423459279594227013011 80447135188919391340519517)
        ·
          refine ⟨30167675695844771752694819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80447135188919391340519517 30167675695844771752694819)
          ·
            refine ⟨45251513543767157629042229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30167675695844771752694819 45251513543767157629042229)
            ·
              refine ⟨4242329394728171027722709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45251513543767157629042229 4242329394728171027722709)
              ·
                refine ⟨99429595188941508462251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4242329394728171027722709 99429595188941508462251)
                ·
                  rfl

theorem cell23_5228238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 7].length) (baseStart_5228238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228238 prefixEnd_5228238 := by exact prefixLift 5228238
  have htrace : WordTrace (prefixWord ++ tailWord_5228238) baseStart_5228238 baseEnd_5228238 := by
    simpa [prefixWord, tailWord_5228238, baseEnd_5228238] using wordTrace_append hprefix tailTrace_5228238
  have hstable : (prefixWord ++ tailWord_5228238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228238).length < 2 ^ (prefixWord ++ tailWord_5228238).sum := by decide
  have hdescent : baseEnd_5228238 < baseStart_5228238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228246 : List Nat := [5, 2, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_5228246 : Nat := 118140960795 + 5228246 * 2 ^ 59
def prefixEnd_5228246 : Nat := 4983230072969 + 3 ^ 40 * 5228246 * 2
def baseEnd_5228246 : Nat := 894867725982218899060247

theorem tailTrace_5228246 : CollatzResearch.WordTrace tailWord_5228246 prefixEnd_5228246 894867725982218899060247 := by
  unfold tailWord_5228246
  simp only [CollatzResearch.WordTrace]
  refine ⟨11918112338560320635840537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127126531611310086782299061 11918112338560320635840537)
  ·
    refine ⟨8938584253920240476880403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11918112338560320635840537 8938584253920240476880403)
    ·
      refine ⟨13407876380880360715320605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8938584253920240476880403 13407876380880360715320605)
      ·
        refine ⟨5027953642830135268245227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13407876380880360715320605 5027953642830135268245227)
        ·
          refine ⟨7541930464245202902367841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5027953642830135268245227 7541930464245202902367841)
          ·
            refine ⟨5656447848183902176775881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7541930464245202902367841 5656447848183902176775881)
            ·
              refine ⟨4242335886137926632581911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5656447848183902176775881 4242335886137926632581911)
              ·
                refine ⟨6363503829206889948872867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4242335886137926632581911 6363503829206889948872867)
                ·
                  refine ⟨9545255743810334923309301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6363503829206889948872867 9545255743810334923309301)
                  ·
                    refine ⟨894867725982218899060247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9545255743810334923309301 894867725982218899060247)
                    ·
                      rfl

theorem cell23_5228246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_5228246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228246 prefixEnd_5228246 := by exact prefixLift 5228246
  have htrace : WordTrace (prefixWord ++ tailWord_5228246) baseStart_5228246 baseEnd_5228246 := by
    simpa [prefixWord, tailWord_5228246, baseEnd_5228246] using wordTrace_append hprefix tailTrace_5228246
  have hstable : (prefixWord ++ tailWord_5228246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228246).length < 2 ^ (prefixWord ++ tailWord_5228246).sum := by decide
  have hdescent : baseEnd_5228246 < baseStart_5228246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228248 : List Nat := [2, 1, 2, 2, 3, 1, 1, 4, 1, 3, 3]
def baseStart_5228248 : Nat := 118140960795 + 5228248 * 2 ^ 59
def prefixEnd_5228248 : Nat := 4983230072969 + 3 ^ 40 * 5228248 * 2
def baseEnd_5228248 : Nat := 2684604204907965689355731

theorem tailTrace_5228248 : CollatzResearch.WordTrace tailWord_5228248 prefixEnd_5228248 2684604204907965689355731 := by
  unfold tailWord_5228248
  simp only [CollatzResearch.WordTrace]
  refine ⟨95344935181478942257510699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127126580241971923010014265 95344935181478942257510699)
  ·
    refine ⟨143017402772218413386266049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95344935181478942257510699 143017402772218413386266049)
    ·
      refine ⟨107263052079163810039699537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143017402772218413386266049 107263052079163810039699537)
      ·
        refine ⟨80447289059372857529774653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107263052079163810039699537 80447289059372857529774653)
        ·
          refine ⟨30167733397264821573665495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80447289059372857529774653 30167733397264821573665495)
          ·
            refine ⟨45251600095897232360498243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30167733397264821573665495 45251600095897232360498243)
            ·
              refine ⟨67877400143845848540747365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45251600095897232360498243 67877400143845848540747365)
              ·
                refine ⟨12727012526971096601390131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67877400143845848540747365 12727012526971096601390131)
                ·
                  refine ⟨19090518790456644902085197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12727012526971096601390131 19090518790456644902085197)
                  ·
                    refine ⟨7158944546421241838281949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19090518790456644902085197 7158944546421241838281949)
                    ·
                      refine ⟨2684604204907965689355731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7158944546421241838281949 2684604204907965689355731)
                      ·
                        rfl

theorem cell23_5228248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_5228248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228248 prefixEnd_5228248 := by exact prefixLift 5228248
  have htrace : WordTrace (prefixWord ++ tailWord_5228248) baseStart_5228248 baseEnd_5228248 := by
    simpa [prefixWord, tailWord_5228248, baseEnd_5228248] using wordTrace_append hprefix tailTrace_5228248
  have hstable : (prefixWord ++ tailWord_5228248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228248).length < 2 ^ (prefixWord ++ tailWord_5228248).sum := by decide
  have hdescent : baseEnd_5228248 < baseStart_5228248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228249 : List Nat := [1, 2, 1, 2, 3, 4, 2, 3, 1, 2, 2]
def baseStart_5228249 : Nat := 118140960795 + 5228249 * 2 ^ 59
def prefixEnd_5228249 : Nat := 4983230072969 + 3 ^ 40 * 5228249 * 2
def baseEnd_5228249 : Nat := 2684604718388620185443227

theorem tailTrace_5228249 : CollatzResearch.WordTrace tailWord_5228249 prefixEnd_5228249 2684604718388620185443227 := by
  unfold tailWord_5228249
  simp only [CollatzResearch.WordTrace]
  refine ⟨190689906835954261685807801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127126604557302841123871867 190689906835954261685807801)
  ·
    refine ⟨143017430126965696264355851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190689906835954261685807801 143017430126965696264355851)
    ·
      refine ⟨214526145190448544396533777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143017430126965696264355851 214526145190448544396533777)
      ·
        refine ⟨160894608892836408297400333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214526145190448544396533777 160894608892836408297400333)
        ·
          refine ⟨60335478334813653111525125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160894608892836408297400333 60335478334813653111525125)
          ·
            refine ⟨11312902187777559958410961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60335478334813653111525125 11312902187777559958410961)
            ·
              refine ⟨8484676640833169968808221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11312902187777559958410961 8484676640833169968808221)
              ·
                refine ⟨3181753740312438738303083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8484676640833169968808221 3181753740312438738303083)
                ·
                  refine ⟨4772630610468658107454625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3181753740312438738303083 4772630610468658107454625)
                  ·
                    refine ⟨3579472957851493580590969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4772630610468658107454625 3579472957851493580590969)
                    ·
                      refine ⟨2684604718388620185443227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3579472957851493580590969 2684604718388620185443227)
                      ·
                        rfl

theorem cell23_5228249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 1, 2, 2].length) (baseStart_5228249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228249 prefixEnd_5228249 := by exact prefixLift 5228249
  have htrace : WordTrace (prefixWord ++ tailWord_5228249) baseStart_5228249 baseEnd_5228249 := by
    simpa [prefixWord, tailWord_5228249, baseEnd_5228249] using wordTrace_append hprefix tailTrace_5228249
  have hstable : (prefixWord ++ tailWord_5228249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228249).length < 2 ^ (prefixWord ++ tailWord_5228249).sum := by decide
  have hdescent : baseEnd_5228249 < baseStart_5228249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228259 : List Nat := [1, 1, 1, 7, 3, 1, 1, 2, 2, 4]
def baseStart_5228259 : Nat := 118140960795 + 5228259 * 2 ^ 59
def prefixEnd_5228259 : Nat := 4983230072969 + 3 ^ 40 * 5228259 * 2
def baseEnd_5228259 : Nat := 894869951065055048772727

theorem tailTrace_5228259 : CollatzResearch.WordTrace tailWord_5228259 prefixEnd_5228259 894869951065055048772727 := by
  unfold tailWord_5228259
  simp only [CollatzResearch.WordTrace]
  refine ⟨190690271565918033393671831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127126847710612022262447887 190690271565918033393671831)
  ·
    refine ⟨286035407348877050090507747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190690271565918033393671831 286035407348877050090507747)
    ·
      refine ⟨429053111023315575135761621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286035407348877050090507747 429053111023315575135761621)
      ·
        refine ⟨10055932289608958792244413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 429053111023315575135761621 10055932289608958792244413)
        ·
          refine ⟨3770974608603359547091655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10055932289608958792244413 3770974608603359547091655)
          ·
            refine ⟨5656461912905039320637483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3770974608603359547091655 5656461912905039320637483)
            ·
              refine ⟨8484692869357558980956225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5656461912905039320637483 8484692869357558980956225)
              ·
                refine ⟨6363519652018169235717169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8484692869357558980956225 6363519652018169235717169)
                ·
                  refine ⟨4772639739013626926787877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6363519652018169235717169 4772639739013626926787877)
                  ·
                    refine ⟨894869951065055048772727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4772639739013626926787877 894869951065055048772727)
                    ·
                      rfl

theorem cell23_5228259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 2, 4].length) (baseStart_5228259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228259 prefixEnd_5228259 := by exact prefixLift 5228259
  have htrace : WordTrace (prefixWord ++ tailWord_5228259) baseStart_5228259 baseEnd_5228259 := by
    simpa [prefixWord, tailWord_5228259, baseEnd_5228259] using wordTrace_append hprefix tailTrace_5228259
  have hstable : (prefixWord ++ tailWord_5228259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228259).length < 2 ^ (prefixWord ++ tailWord_5228259).sum := by decide
  have hdescent : baseEnd_5228259 < baseStart_5228259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228276 : List Nat := [2, 6, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_5228276 : Nat := 118140960795 + 5228276 * 2 ^ 59
def prefixEnd_5228276 : Nat := 4983230072969 + 3 ^ 40 * 5228276 * 2
def baseEnd_5228276 : Nat := 894872860788763859935201

theorem tailTrace_5228276 : CollatzResearch.WordTrace tailWord_5228276 prefixEnd_5228276 894872860788763859935201 := by
  unfold tailWord_5228276
  simp only [CollatzResearch.WordTrace]
  refine ⟨95345445803428222648520341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127127261071237630198027121 95345445803428222648520341)
  ·
    refine ⟨4469317772035697936649391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 95345445803428222648520341 4469317772035697936649391)
    ·
      refine ⟨6703976658053546904974087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4469317772035697936649391 6703976658053546904974087)
      ·
        refine ⟨10055964987080320357461131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6703976658053546904974087 10055964987080320357461131)
        ·
          refine ⟨15083947480620480536191697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10055964987080320357461131 15083947480620480536191697)
          ·
            refine ⟨11312960610465360402143773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15083947480620480536191697 11312960610465360402143773)
            ·
              refine ⟨4242360228924510150803915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11312960610465360402143773 4242360228924510150803915)
              ·
                refine ⟨6363540343386765226205873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4242360228924510150803915 6363540343386765226205873)
                ·
                  refine ⟨4772655257540073919654405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6363540343386765226205873 4772655257540073919654405)
                  ·
                    refine ⟨894872860788763859935201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4772655257540073919654405 894872860788763859935201)
                    ·
                      rfl

theorem cell23_5228276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_5228276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228276 prefixEnd_5228276 := by exact prefixLift 5228276
  have htrace : WordTrace (prefixWord ++ tailWord_5228276) baseStart_5228276 baseEnd_5228276 := by
    simpa [prefixWord, tailWord_5228276, baseEnd_5228276] using wordTrace_append hprefix tailTrace_5228276
  have hstable : (prefixWord ++ tailWord_5228276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228276).length < 2 ^ (prefixWord ++ tailWord_5228276).sum := by decide
  have hdescent : baseEnd_5228276 < baseStart_5228276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228292 : List Nat := [2, 3, 2, 2, 1, 2, 1, 4, 1, 3, 2]
def baseStart_5228292 : Nat := 118140960795 + 5228292 * 2 ^ 59
def prefixEnd_5228292 : Nat := 4983230072969 + 3 ^ 40 * 5228292 * 2
def baseEnd_5228292 : Nat := 2684626798056763517205529

theorem tailTrace_5228292 : CollatzResearch.WordTrace tailWord_5228292 prefixEnd_5228292 2684626798056763517205529 := by
  unfold tailWord_5228292
  simp only [CollatzResearch.WordTrace]
  refine ⟨95345737587399240014811565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127127650116532320019748753 95345737587399240014811565)
  ·
    refine ⟨35754651595274715005554337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95345737587399240014811565 35754651595274715005554337)
    ·
      refine ⟨26815988696456036254165753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35754651595274715005554337 26815988696456036254165753)
      ·
        refine ⟨20111991522342027190624315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26815988696456036254165753 20111991522342027190624315)
        ·
          refine ⟨30167987283513040785936473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20111991522342027190624315 30167987283513040785936473)
          ·
            refine ⟨22625990462634780589452355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30167987283513040785936473 22625990462634780589452355)
            ·
              refine ⟨33938985693952170884178533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22625990462634780589452355 33938985693952170884178533)
              ·
                refine ⟨6363559817616032040783475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33938985693952170884178533 6363559817616032040783475)
                ·
                  refine ⟨9545339726424048061175213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6363559817616032040783475 9545339726424048061175213)
                  ·
                    refine ⟨3579502397409018022940705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9545339726424048061175213 3579502397409018022940705)
                    ·
                      refine ⟨2684626798056763517205529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3579502397409018022940705 2684626798056763517205529)
                      ·
                        rfl

theorem cell23_5228292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_5228292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228292 prefixEnd_5228292 := by exact prefixLift 5228292
  have htrace : WordTrace (prefixWord ++ tailWord_5228292) baseStart_5228292 baseEnd_5228292 := by
    simpa [prefixWord, tailWord_5228292, baseEnd_5228292] using wordTrace_append hprefix tailTrace_5228292
  have hstable : (prefixWord ++ tailWord_5228292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228292).length < 2 ^ (prefixWord ++ tailWord_5228292).sum := by decide
  have hdescent : baseEnd_5228292 < baseStart_5228292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228294 : List Nat := [6, 2, 2, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_5228294 : Nat := 118140960795 + 5228294 * 2 ^ 59
def prefixEnd_5228294 : Nat := 4983230072969 + 3 ^ 40 * 5228294 * 2
def baseEnd_5228294 : Nat := 2684627825018072509380521

theorem tailTrace_5228294 : CollatzResearch.WordTrace tailWord_5228294 prefixEnd_5228294 2684627825018072509380521 := by
  unfold tailWord_5228294
  simp only [CollatzResearch.WordTrace]
  refine ⟨5959110878774726074099873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 127127698747194156247463957 5959110878774726074099873)
  ·
    refine ⟨4469333159081044555574905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5959110878774726074099873 4469333159081044555574905)
    ·
      refine ⟨3351999869310783416681179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4469333159081044555574905 3351999869310783416681179)
      ·
        refine ⟨5027999803966175125021769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3351999869310783416681179 5027999803966175125021769)
        ·
          refine ⟨3770999852974631343766327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5027999803966175125021769 3770999852974631343766327)
          ·
            refine ⟨5656499779461947015649491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3770999852974631343766327 5656499779461947015649491)
            ·
              refine ⟨8484749669192920523474237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5656499779461947015649491 8484749669192920523474237)
              ·
                refine ⟨3181781125947345196302839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8484749669192920523474237 3181781125947345196302839)
                ·
                  refine ⟨4772671688921017794454259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3181781125947345196302839 4772671688921017794454259)
                  ·
                    refine ⟨7159007533381526691681389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4772671688921017794454259 7159007533381526691681389)
                    ·
                      refine ⟨2684627825018072509380521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7159007533381526691681389 2684627825018072509380521)
                      ·
                        rfl

theorem cell23_5228294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_5228294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228294 prefixEnd_5228294 := by exact prefixLift 5228294
  have htrace : WordTrace (prefixWord ++ tailWord_5228294) baseStart_5228294 baseEnd_5228294 := by
    simpa [prefixWord, tailWord_5228294, baseEnd_5228294] using wordTrace_append hprefix tailTrace_5228294
  have hstable : (prefixWord ++ tailWord_5228294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228294).length < 2 ^ (prefixWord ++ tailWord_5228294).sum := by decide
  have hdescent : baseEnd_5228294 < baseStart_5228294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228322 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 4, 2, 2]
def baseStart_5228322 : Nat := 118140960795 + 5228322 * 2 ^ 59
def prefixEnd_5228322 : Nat := 4983230072969 + 3 ^ 40 * 5228322 * 2
def baseEnd_5228322 : Nat := 2684642202476398399830391

theorem tailTrace_5228322 : CollatzResearch.WordTrace tailWord_5228322 prefixEnd_5228322 2684642202476398399830391 := by
  unfold tailWord_5228322
  simp only [CollatzResearch.WordTrace]
  refine ⟨47673142341172448788303805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127128379576459863435476813 47673142341172448788303805)
  ·
    refine ⟨17877428377939668295613927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47673142341172448788303805 17877428377939668295613927)
    ·
      refine ⟨26816142566909502443420891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17877428377939668295613927 26816142566909502443420891)
      ·
        refine ⟨40224213850364253665131337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26816142566909502443420891 40224213850364253665131337)
        ·
          refine ⟨30168160387773190248848503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40224213850364253665131337 30168160387773190248848503)
          ·
            refine ⟨45252240581659785373272755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30168160387773190248848503 45252240581659785373272755)
            ·
              refine ⟨67878360872489678059909133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45252240581659785373272755 67878360872489678059909133)
              ·
                refine ⟨25454385327183629272465925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67878360872489678059909133 25454385327183629272465925)
                ·
                  refine ⟨4772697248846930488587361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25454385327183629272465925 4772697248846930488587361)
                  ·
                    refine ⟨3579522936635197866440521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4772697248846930488587361 3579522936635197866440521)
                    ·
                      refine ⟨2684642202476398399830391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3579522936635197866440521 2684642202476398399830391)
                      ·
                        rfl

theorem cell23_5228322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_5228322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228322 prefixEnd_5228322 := by exact prefixLift 5228322
  have htrace : WordTrace (prefixWord ++ tailWord_5228322) baseStart_5228322 baseEnd_5228322 := by
    simpa [prefixWord, tailWord_5228322, baseEnd_5228322] using wordTrace_append hprefix tailTrace_5228322
  have hstable : (prefixWord ++ tailWord_5228322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228322).length < 2 ^ (prefixWord ++ tailWord_5228322).sum := by decide
  have hdescent : baseEnd_5228322 < baseStart_5228322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228339 : List Nat := [1, 1, 1, 2, 7, 1, 1, 3, 2, 2, 2]
def baseStart_5228339 : Nat := 118140960795 + 5228339 * 2 ^ 59
def prefixEnd_5228339 : Nat := 4983230072969 + 3 ^ 40 * 5228339 * 2
def baseEnd_5228339 : Nat := 2684650931647524833317813

theorem tailTrace_5228339 : CollatzResearch.WordTrace tailWord_5228339 prefixEnd_5228339 2684650931647524833317813 := by
  unfold tailWord_5228339
  simp only [CollatzResearch.WordTrace]
  refine ⟨190693189405628207056584071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127128792937085471371056047 190693189405628207056584071)
  ·
    refine ⟨286039784108442310584876107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190693189405628207056584071 286039784108442310584876107)
    ·
      refine ⟨429059676162663465877314161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286039784108442310584876107 429059676162663465877314161)
      ·
        refine ⟨321794757121997599407985621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429059676162663465877314161 321794757121997599407985621)
        ·
          refine ⟨7542064620046818736124663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 321794757121997599407985621 7542064620046818736124663)
          ·
            refine ⟨11313096930070228104186995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7542064620046818736124663 11313096930070228104186995)
            ·
              refine ⟨16969645395105342156280493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11313096930070228104186995 16969645395105342156280493)
              ·
                refine ⟨6363617023164503308605185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16969645395105342156280493 6363617023164503308605185)
                ·
                  refine ⟨4772712767373377481453889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6363617023164503308605185 4772712767373377481453889)
                  ·
                    refine ⟨3579534575530033111090417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4772712767373377481453889 3579534575530033111090417)
                    ·
                      refine ⟨2684650931647524833317813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3579534575530033111090417 2684650931647524833317813)
                      ·
                        rfl

theorem cell23_5228339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 2, 2].length) (baseStart_5228339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228339 prefixEnd_5228339 := by exact prefixLift 5228339
  have htrace : WordTrace (prefixWord ++ tailWord_5228339) baseStart_5228339 baseEnd_5228339 := by
    simpa [prefixWord, tailWord_5228339, baseEnd_5228339] using wordTrace_append hprefix tailTrace_5228339
  have hstable : (prefixWord ++ tailWord_5228339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228339).length < 2 ^ (prefixWord ++ tailWord_5228339).sum := by decide
  have hdescent : baseEnd_5228339 < baseStart_5228339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228452 : List Nat := [2, 3, 1, 2, 1, 4, 3, 1, 6]
def baseStart_5228452 : Nat := 118140960795 + 5228452 * 2 ^ 59
def prefixEnd_5228452 : Nat := 4983230072969 + 3 ^ 40 * 5228452 * 2
def baseEnd_5228452 : Nat := 298300994995720321244977

theorem tailTrace_5228452 : CollatzResearch.WordTrace tailWord_5228452 prefixEnd_5228452 298300994995720321244977 := by
  unfold tailWord_5228452
  simp only [CollatzResearch.WordTrace]
  refine ⟨95348655427109413677723805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127131540569479218236965073 95348655427109413677723805)
  ·
    refine ⟨35755745785166030129146427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95348655427109413677723805 35755745785166030129146427)
    ·
      refine ⟨53633618677749045193719641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35755745785166030129146427 53633618677749045193719641)
      ·
        refine ⟨40225214008311783895289731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53633618677749045193719641 40225214008311783895289731)
        ·
          refine ⟨60337821012467675842934597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40225214008311783895289731 60337821012467675842934597)
          ·
            refine ⟨11313341439837689220550237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60337821012467675842934597 11313341439837689220550237)
            ·
              refine ⟨4242503039939133457706339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11313341439837689220550237 4242503039939133457706339)
              ·
                refine ⟨6363754559908700186559509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4242503039939133457706339 6363754559908700186559509)
                ·
                  refine ⟨298300994995720321244977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6363754559908700186559509 298300994995720321244977)
                  ·
                    rfl

theorem cell23_5228452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_5228452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228452 prefixEnd_5228452 := by exact prefixLift 5228452
  have htrace : WordTrace (prefixWord ++ tailWord_5228452) baseStart_5228452 baseEnd_5228452 := by
    simpa [prefixWord, tailWord_5228452, baseEnd_5228452] using wordTrace_append hprefix tailTrace_5228452
  have hstable : (prefixWord ++ tailWord_5228452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228452).length < 2 ^ (prefixWord ++ tailWord_5228452).sum := by decide
  have hdescent : baseEnd_5228452 < baseStart_5228452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228472 : List Nat := [2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2]
def baseStart_5228472 : Nat := 118140960795 + 5228472 * 2 ^ 59
def prefixEnd_5228472 : Nat := 4983230072969 + 3 ^ 40 * 5228472 * 2
def baseEnd_5228472 : Nat := 2684719224574572812954701

theorem tailTrace_5228472 : CollatzResearch.WordTrace tailWord_5228472 prefixEnd_5228472 2684719224574572812954701 := by
  unfold tailWord_5228472
  simp only [CollatzResearch.WordTrace]
  refine ⟨95349020157073185385587835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127132026876097580514117113 95349020157073185385587835)
  ·
    refine ⟨143023530235609778078381753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95349020157073185385587835 143023530235609778078381753)
    ·
      refine ⟨107267647676707333558786315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143023530235609778078381753 107267647676707333558786315)
      ·
        refine ⟨160901471515061000338179473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107267647676707333558786315 160901471515061000338179473)
        ·
          refine ⟨120676103636295750253634605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160901471515061000338179473 120676103636295750253634605)
          ·
            refine ⟨45253538863610906345112977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120676103636295750253634605 45253538863610906345112977)
            ·
              refine ⟨33940154147708179758834733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45253538863610906345112977 33940154147708179758834733)
              ·
                refine ⟨12727557805390567409563025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33940154147708179758834733 12727557805390567409563025)
                ·
                  refine ⟨9545668354042925557172269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12727557805390567409563025 9545668354042925557172269)
                  ·
                    refine ⟨3579625632766097083939601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9545668354042925557172269 3579625632766097083939601)
                    ·
                      refine ⟨2684719224574572812954701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3579625632766097083939601 2684719224574572812954701)
                      ·
                        rfl

theorem cell23_5228472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2].length) (baseStart_5228472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228472 prefixEnd_5228472 := by exact prefixLift 5228472
  have htrace : WordTrace (prefixWord ++ tailWord_5228472) baseStart_5228472 baseEnd_5228472 := by
    simpa [prefixWord, tailWord_5228472, baseEnd_5228472] using wordTrace_append hprefix tailTrace_5228472
  have hstable : (prefixWord ++ tailWord_5228472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228472).length < 2 ^ (prefixWord ++ tailWord_5228472).sum := by decide
  have hdescent : baseEnd_5228472 < baseStart_5228472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228495 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 4, 4]
def baseStart_5228495 : Nat := 118140960795 + 5228495 * 2 ^ 59
def prefixEnd_5228495 : Nat := 4983230072969 + 3 ^ 40 * 5228495 * 2
def baseEnd_5228495 : Nat := 894910344876542074322365

theorem tailTrace_5228495 : CollatzResearch.WordTrace tailWord_5228495 prefixEnd_5228495 894910344876542074322365 := by
  unfold tailWord_5228495
  simp only [CollatzResearch.WordTrace]
  refine ⟨190698879193063045699262939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127132586128708697132841959 190698879193063045699262939)
  ·
    refine ⟨286048318789594568548894409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190698879193063045699262939 286048318789594568548894409)
    ·
      refine ⟨214536239092195926411670807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286048318789594568548894409 214536239092195926411670807)
      ·
        refine ⟨321804358638293889617506211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214536239092195926411670807 321804358638293889617506211)
        ·
          refine ⟨482706537957440834426259317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321804358638293889617506211 482706537957440834426259317)
          ·
            refine ⟨45253737933510078227461811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 482706537957440834426259317 45253737933510078227461811)
            ·
              refine ⟨67880606900265117341192717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45253737933510078227461811 67880606900265117341192717)
              ·
                refine ⟨25455227587599419002947269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67880606900265117341192717 25455227587599419002947269)
                ·
                  refine ⟨4772855172674891063052613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25455227587599419002947269 4772855172674891063052613)
                  ·
                    refine ⟨894910344876542074322365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4772855172674891063052613 894910344876542074322365)
                    ·
                      rfl

theorem cell23_5228495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 4].length) (baseStart_5228495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228495 prefixEnd_5228495 := by exact prefixLift 5228495
  have htrace : WordTrace (prefixWord ++ tailWord_5228495) baseStart_5228495 baseEnd_5228495 := by
    simpa [prefixWord, tailWord_5228495, baseEnd_5228495] using wordTrace_append hprefix tailTrace_5228495
  have hstable : (prefixWord ++ tailWord_5228495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228495).length < 2 ^ (prefixWord ++ tailWord_5228495).sum := by decide
  have hdescent : baseEnd_5228495 < baseStart_5228495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228515 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 6]
def baseStart_5228515 : Nat := 118140960795 + 5228515 * 2 ^ 59
def prefixEnd_5228515 : Nat := 4983230072969 + 3 ^ 40 * 5228515 * 2
def baseEnd_5228515 : Nat := 2684741304242716144717003

theorem tailTrace_5228515 : CollatzResearch.WordTrace tailWord_5228515 prefixEnd_5228515 2684741304242716144717003 := by
  unfold tailWord_5228515
  simp only [CollatzResearch.WordTrace]
  refine ⟨190699608652990589114990999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127133072435327059409993999 190699608652990589114990999)
  ·
    refine ⟨286049412979485883672486499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190699608652990589114990999 286049412979485883672486499)
    ·
      refine ⟨429074119469228825508729749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286049412979485883672486499 429074119469228825508729749)
      ·
        refine ⟨20112849350120101195721707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 429074119469228825508729749 20112849350120101195721707)
        ·
          refine ⟨30169274025180151793582561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20112849350120101195721707 30169274025180151793582561)
          ·
            refine ⟨22626955518885113845186921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30169274025180151793582561 22626955518885113845186921)
            ·
              refine ⟨16970216639163835383890191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22626955518885113845186921 16970216639163835383890191)
              ·
                refine ⟨25455324958745753075835287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16970216639163835383890191 25455324958745753075835287)
                ·
                  refine ⟨38182987438118629613752931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25455324958745753075835287 38182987438118629613752931)
                  ·
                    refine ⟨57274481157177944420629397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38182987438118629613752931 57274481157177944420629397)
                    ·
                      refine ⟨2684741304242716144717003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57274481157177944420629397 2684741304242716144717003)
                      ·
                        rfl

theorem cell23_5228515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_5228515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228515 prefixEnd_5228515 := by exact prefixLift 5228515
  have htrace : WordTrace (prefixWord ++ tailWord_5228515) baseStart_5228515 baseEnd_5228515 := by
    simpa [prefixWord, tailWord_5228515, baseEnd_5228515] using wordTrace_append hprefix tailTrace_5228515
  have hstable : (prefixWord ++ tailWord_5228515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228515).length < 2 ^ (prefixWord ++ tailWord_5228515).sum := by decide
  have hdescent : baseEnd_5228515 < baseStart_5228515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228522 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 3, 2, 3]
def baseStart_5228522 : Nat := 118140960795 + 5228522 * 2 ^ 59
def prefixEnd_5228522 : Nat := 4983230072969 + 3 ^ 40 * 5228522 * 2
def baseEnd_5228522 : Nat := 2684744898607297617329471

theorem tailTrace_5228522 : CollatzResearch.WordTrace tailWord_5228522 prefixEnd_5228522 2684744898607297617329471 := by
  unfold tailWord_5228522
  simp only [CollatzResearch.WordTrace]
  refine ⟨47674965990991307327623955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127133242642643486206997213 47674965990991307327623955)
  ·
    refine ⟨71512448986486960991435933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47674965990991307327623955 71512448986486960991435933)
    ·
      refine ⟨26817168369932610371788475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71512448986486960991435933 26817168369932610371788475)
      ·
        refine ⟨40225752554898915557682713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26817168369932610371788475 40225752554898915557682713)
        ·
          refine ⟨30169314416174186668262035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40225752554898915557682713 30169314416174186668262035)
          ·
            refine ⟨45253971624261280002393053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30169314416174186668262035 45253971624261280002393053)
            ·
              refine ⟨16970239359097980000897395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45253971624261280002393053 16970239359097980000897395)
              ·
                refine ⟨25455359038646970001346093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16970239359097980000897395 25455359038646970001346093)
                ·
                  refine ⟨9545759639492613750504785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25455359038646970001346093 9545759639492613750504785)
                  ·
                    refine ⟨7159319729619460312878589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9545759639492613750504785 7159319729619460312878589)
                    ·
                      refine ⟨2684744898607297617329471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7159319729619460312878589 2684744898607297617329471)
                      ·
                        rfl

theorem cell23_5228522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_5228522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228522 prefixEnd_5228522 := by exact prefixLift 5228522
  have htrace : WordTrace (prefixWord ++ tailWord_5228522) baseStart_5228522 baseEnd_5228522 := by
    simpa [prefixWord, tailWord_5228522, baseEnd_5228522] using wordTrace_append hprefix tailTrace_5228522
  have hstable : (prefixWord ++ tailWord_5228522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228522).length < 2 ^ (prefixWord ++ tailWord_5228522).sum := by decide
  have hdescent : baseEnd_5228522 < baseStart_5228522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228575 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 4]
def baseStart_5228575 : Nat := 118140960795 + 5228575 * 2 ^ 59
def prefixEnd_5228575 : Nat := 4983230072969 + 3 ^ 40 * 5228575 * 2
def baseEnd_5228575 : Nat := 2684772113081985909966727

theorem tailTrace_5228575 : CollatzResearch.WordTrace tailWord_5228575 prefixEnd_5228575 2684772113081985909966727 := by
  unfold tailWord_5228575
  simp only [CollatzResearch.WordTrace]
  refine ⟨190701797032773219362175179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127134531355182146241450119 190701797032773219362175179)
  ·
    refine ⟨286052695549159829043262769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190701797032773219362175179 286052695549159829043262769)
    ·
      refine ⟨214539521661869871782447077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286052695549159829043262769 214539521661869871782447077)
      ·
        refine ⟨40226160311600600959208827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 214539521661869871782447077 40226160311600600959208827)
        ·
          refine ⟨60339240467400901438813241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40226160311600600959208827 60339240467400901438813241)
          ·
            refine ⟨45254430350550676079109931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60339240467400901438813241 45254430350550676079109931)
            ·
              refine ⟨67881645525826014118664897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45254430350550676079109931 67881645525826014118664897)
              ·
                refine ⟨50911234144369510588998673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67881645525826014118664897 50911234144369510588998673)
                ·
                  refine ⟨38183425608277132941749005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50911234144369510588998673 38183425608277132941749005)
                  ·
                    refine ⟨14318784603103924853155877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38183425608277132941749005 14318784603103924853155877)
                    ·
                      refine ⟨2684772113081985909966727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14318784603103924853155877 2684772113081985909966727)
                      ·
                        rfl

theorem cell23_5228575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_5228575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228575 prefixEnd_5228575 := by exact prefixLift 5228575
  have htrace : WordTrace (prefixWord ++ tailWord_5228575) baseStart_5228575 baseEnd_5228575 := by
    simpa [prefixWord, tailWord_5228575, baseEnd_5228575] using wordTrace_append hprefix tailTrace_5228575
  have hstable : (prefixWord ++ tailWord_5228575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228575).length < 2 ^ (prefixWord ++ tailWord_5228575).sum := by decide
  have hdescent : baseEnd_5228575 < baseStart_5228575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228579 : List Nat := [1, 1, 1, 4, 3, 1, 2, 4, 1, 3, 2]
def baseStart_5228579 : Nat := 118140960795 + 5228579 * 2 ^ 59
def prefixEnd_5228579 : Nat := 4983230072969 + 3 ^ 40 * 5228579 * 2
def baseEnd_5228579 : Nat := 2684774167004603894316709

theorem tailTrace_5228579 : CollatzResearch.WordTrace tailWord_5228579 prefixEnd_5228579 2684774167004603894316709 := by
  unfold tailWord_5228579
  simp only [CollatzResearch.WordTrace]
  refine ⟨190701942924758728045320791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127134628616505818696880527 190701942924758728045320791)
  ·
    refine ⟨286052914387138092067981187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190701942924758728045320791 286052914387138092067981187)
    ·
      refine ⟨429079371580707138101971781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286052914387138092067981187 429079371580707138101971781)
      ·
        refine ⟨80452382171382588394119709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 429079371580707138101971781 80452382171382588394119709)
        ·
          refine ⟨30169643314268470647794891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80452382171382588394119709 30169643314268470647794891)
          ·
            refine ⟨45254464971402705971692337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30169643314268470647794891 45254464971402705971692337)
            ·
              refine ⟨33940848728552029478769253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45254464971402705971692337 33940848728552029478769253)
              ·
                refine ⟨6363909136603505527269235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33940848728552029478769253 6363909136603505527269235)
                ·
                  refine ⟨9545863704905258290903853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6363909136603505527269235 9545863704905258290903853)
                  ·
                    refine ⟨3579698889339471859088945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9545863704905258290903853 3579698889339471859088945)
                    ·
                      refine ⟨2684774167004603894316709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3579698889339471859088945 2684774167004603894316709)
                      ·
                        rfl

theorem cell23_5228579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 3, 2].length) (baseStart_5228579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228579 prefixEnd_5228579 := by exact prefixLift 5228579
  have htrace : WordTrace (prefixWord ++ tailWord_5228579) baseStart_5228579 baseEnd_5228579 := by
    simpa [prefixWord, tailWord_5228579, baseEnd_5228579] using wordTrace_append hprefix tailTrace_5228579
  have hstable : (prefixWord ++ tailWord_5228579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228579).length < 2 ^ (prefixWord ++ tailWord_5228579).sum := by decide
  have hdescent : baseEnd_5228579 < baseStart_5228579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228595 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 5]
def baseStart_5228595 : Nat := 118140960795 + 5228595 * 2 ^ 59
def prefixEnd_5228595 : Nat := 4983230072969 + 3 ^ 40 * 5228595 * 2
def baseEnd_5228595 : Nat := 2684782382695075831716635

theorem tailTrace_5228595 : CollatzResearch.WordTrace tailWord_5228595 prefixEnd_5228595 2684782382695075831716635 := by
  unfold tailWord_5228595
  simp only [CollatzResearch.WordTrace]
  refine ⟨190702526492700762777903239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127135017661800508518602159 190702526492700762777903239)
  ·
    refine ⟨286053789739051144166854859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190702526492700762777903239 286053789739051144166854859)
    ·
      refine ⟨429080684608576716250282289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286053789739051144166854859 429080684608576716250282289)
      ·
        refine ⟨321810513456432537187711717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429080684608576716250282289 321810513456432537187711717)
        ·
          refine ⟨60339471273081100722695947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 321810513456432537187711717 60339471273081100722695947)
          ·
            refine ⟨90509206909621651084043921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60339471273081100722695947 90509206909621651084043921)
            ·
              refine ⟨67881905182216238313032941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90509206909621651084043921 67881905182216238313032941)
              ·
                refine ⟨25455714443331089367387353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67881905182216238313032941 25455714443331089367387353)
                ·
                  refine ⟨19091785832498317025540515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25455714443331089367387353 19091785832498317025540515)
                  ·
                    refine ⟨28637678748747475538310773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19091785832498317025540515 28637678748747475538310773)
                    ·
                      refine ⟨2684782382695075831716635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28637678748747475538310773 2684782382695075831716635)
                      ·
                        rfl

theorem cell23_5228595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 5].length) (baseStart_5228595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228595 prefixEnd_5228595 := by exact prefixLift 5228595
  have htrace : WordTrace (prefixWord ++ tailWord_5228595) baseStart_5228595 baseEnd_5228595 := by
    simpa [prefixWord, tailWord_5228595, baseEnd_5228595] using wordTrace_append hprefix tailTrace_5228595
  have hstable : (prefixWord ++ tailWord_5228595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228595).length < 2 ^ (prefixWord ++ tailWord_5228595).sum := by decide
  have hdescent : baseEnd_5228595 < baseStart_5228595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228622 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4]
def baseStart_5228622 : Nat := 118140960795 + 5228622 * 2 ^ 59
def prefixEnd_5228622 : Nat := 4983230072969 + 3 ^ 40 * 5228622 * 2
def baseEnd_5228622 : Nat := 2684796246672747226079011

theorem tailTrace_5228622 : CollatzResearch.WordTrace tailWord_5228622 prefixEnd_5228622 2684796246672747226079011 := by
  unfold tailWord_5228622
  simp only [CollatzResearch.WordTrace]
  refine ⟨23837938907950368298642015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127135674175735297592757413 23837938907950368298642015)
  ·
    refine ⟨35756908361925552447963023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23837938907950368298642015 35756908361925552447963023)
    ·
      refine ⟨53635362542888328671944535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35756908361925552447963023 53635362542888328671944535)
      ·
        refine ⟨80453043814332493007916803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53635362542888328671944535 80453043814332493007916803)
        ·
          refine ⟨120679565721498739511875205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80453043814332493007916803 120679565721498739511875205)
          ·
            refine ⟨22627418572781013658476601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120679565721498739511875205 22627418572781013658476601)
            ·
              refine ⟨16970563929585760243857451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22627418572781013658476601 16970563929585760243857451)
              ·
                refine ⟨25455845894378640365786177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16970563929585760243857451 25455845894378640365786177)
                ·
                  refine ⟨19091884420783980274339633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25455845894378640365786177 19091884420783980274339633)
                  ·
                    refine ⟨14318913315587985205754725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19091884420783980274339633 14318913315587985205754725)
                    ·
                      refine ⟨2684796246672747226079011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14318913315587985205754725 2684796246672747226079011)
                      ·
                        rfl

theorem cell23_5228622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_5228622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228622 prefixEnd_5228622 := by exact prefixLift 5228622
  have htrace : WordTrace (prefixWord ++ tailWord_5228622) baseStart_5228622 baseEnd_5228622 := by
    simpa [prefixWord, tailWord_5228622, baseEnd_5228622] using wordTrace_append hprefix tailTrace_5228622
  have hstable : (prefixWord ++ tailWord_5228622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228622).length < 2 ^ (prefixWord ++ tailWord_5228622).sum := by decide
  have hdescent : baseEnd_5228622 < baseStart_5228622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228630 : List Nat := [5, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_5228630 : Nat := 118140960795 + 5228630 * 2 ^ 59
def prefixEnd_5228630 : Nat := 4983230072969 + 3 ^ 40 * 5228630 * 2
def baseEnd_5228630 : Nat := 2684800354517983194778975

theorem tailTrace_5228630 : CollatzResearch.WordTrace tailWord_5228630 prefixEnd_5228630 2684800354517983194778975 := by
  unfold tailWord_5228630
  simp only [CollatzResearch.WordTrace]
  refine ⟨11918987690473372734714209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127135868698382642503618229 11918987690473372734714209)
  ·
    refine ⟨8939240767855029551035657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11918987690473372734714209 8939240767855029551035657)
    ·
      refine ⟨6704430575891272163276743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8939240767855029551035657 6704430575891272163276743)
      ·
        refine ⟨10056645863836908244915115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6704430575891272163276743 10056645863836908244915115)
        ·
          refine ⟨15084968795755362367372673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10056645863836908244915115 15084968795755362367372673)
          ·
            refine ⟨11313726596816521775529505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15084968795755362367372673 11313726596816521775529505)
            ·
              refine ⟨8485294947612391331647129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11313726596816521775529505 8485294947612391331647129)
              ·
                refine ⟨6363971210709293498735347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8485294947612391331647129 6363971210709293498735347)
                ·
                  refine ⟨9545956816063940248103021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6363971210709293498735347 9545956816063940248103021)
                  ·
                    refine ⟨3579733806023977593038633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9545956816063940248103021 3579733806023977593038633)
                    ·
                      refine ⟨2684800354517983194778975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3579733806023977593038633 2684800354517983194778975)
                      ·
                        rfl

theorem cell23_5228630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_5228630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228630 prefixEnd_5228630 := by exact prefixLift 5228630
  have htrace : WordTrace (prefixWord ++ tailWord_5228630) baseStart_5228630 baseEnd_5228630 := by
    simpa [prefixWord, tailWord_5228630, baseEnd_5228630] using wordTrace_append hprefix tailTrace_5228630
  have hstable : (prefixWord ++ tailWord_5228630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228630).length < 2 ^ (prefixWord ++ tailWord_5228630).sum := by decide
  have hdescent : baseEnd_5228630 < baseStart_5228630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228769 : List Nat := [1, 2, 3, 1, 3, 1, 3, 3, 1, 5]
def baseStart_5228769 : Nat := 118140960795 + 5228769 * 2 ^ 59
def prefixEnd_5228769 : Nat := 4983230072969 + 3 ^ 40 * 5228769 * 2
def baseEnd_5228769 : Nat := 894957242776319383646945

theorem tailTrace_5228769 : CollatzResearch.WordTrace tailWord_5228769 prefixEnd_5228769 894957242776319383646945 := by
  unfold tailWord_5228769
  simp only [CollatzResearch.WordTrace]
  refine ⟨190708872794070390494737361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127139248529380260329824907 190708872794070390494737361)
  ·
    refine ⟨143031654595552792871053021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190708872794070390494737361 143031654595552792871053021)
    ·
      refine ⟨53636870473332297326644883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143031654595552792871053021 53636870473332297326644883)
      ·
        refine ⟨80455305709998445989967325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53636870473332297326644883 80455305709998445989967325)
        ·
          refine ⟨30170739641249417246237747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80455305709998445989967325 30170739641249417246237747)
          ·
            refine ⟨45256109461874125869356621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30170739641249417246237747 45256109461874125869356621)
            ·
              refine ⟨16971041048202797201008733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45256109461874125869356621 16971041048202797201008733)
              ·
                refine ⟨6364140393076048950378275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16971041048202797201008733 6364140393076048950378275)
                ·
                  refine ⟨9546210589614073425567413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6364140393076048950378275 9546210589614073425567413)
                  ·
                    refine ⟨894957242776319383646945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9546210589614073425567413 894957242776319383646945)
                    ·
                      rfl

theorem cell23_5228769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_5228769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228769 prefixEnd_5228769 := by exact prefixLift 5228769
  have htrace : WordTrace (prefixWord ++ tailWord_5228769) baseStart_5228769 baseEnd_5228769 := by
    simpa [prefixWord, tailWord_5228769, baseEnd_5228769] using wordTrace_append hprefix tailTrace_5228769
  have hstable : (prefixWord ++ tailWord_5228769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228769).length < 2 ^ (prefixWord ++ tailWord_5228769).sum := by decide
  have hdescent : baseEnd_5228769 < baseStart_5228769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228783 : List Nat := [1, 1, 2, 1, 6, 1, 2, 4, 1, 1, 3]
def baseStart_5228783 : Nat := 118140960795 + 5228783 * 2 ^ 59
def prefixEnd_5228783 : Nat := 4983230072969 + 3 ^ 40 * 5228783 * 2
def baseEnd_5228783 : Nat := 2684878917058121096165771

theorem tailTrace_5228783 : CollatzResearch.WordTrace tailWord_5228783 prefixEnd_5228783 2684878917058121096165771 := by
  unfold tailWord_5228783
  simp only [CollatzResearch.WordTrace]
  refine ⟨190709383416019670885747003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127139588944013113923831335 190709383416019670885747003)
  ·
    refine ⟨286064075124029506328620505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190709383416019670885747003 286064075124029506328620505)
    ·
      refine ⟨214548056343022129746465379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286064075124029506328620505 214548056343022129746465379)
      ·
        refine ⟨321822084514533194619698069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214548056343022129746465379 321822084514533194619698069)
        ·
          refine ⟨15085410211618743497798347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 321822084514533194619698069 15085410211618743497798347)
          ·
            refine ⟨22628115317428115246697521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15085410211618743497798347 22628115317428115246697521)
            ·
              refine ⟨16971086488071086435023141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22628115317428115246697521 16971086488071086435023141)
              ·
                refine ⟨3182078716513328706566839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16971086488071086435023141 3182078716513328706566839)
                ·
                  refine ⟨4773118074769993059850259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3182078716513328706566839 4773118074769993059850259)
                  ·
                    refine ⟨7159677112154989589775389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4773118074769993059850259 7159677112154989589775389)
                    ·
                      refine ⟨2684878917058121096165771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7159677112154989589775389 2684878917058121096165771)
                      ·
                        rfl

theorem cell23_5228783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 1, 1, 3].length) (baseStart_5228783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228783 prefixEnd_5228783 := by exact prefixLift 5228783
  have htrace : WordTrace (prefixWord ++ tailWord_5228783) baseStart_5228783 baseEnd_5228783 := by
    simpa [prefixWord, tailWord_5228783, baseEnd_5228783] using wordTrace_append hprefix tailTrace_5228783
  have hstable : (prefixWord ++ tailWord_5228783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228783).length < 2 ^ (prefixWord ++ tailWord_5228783).sum := by decide
  have hdescent : baseEnd_5228783 < baseStart_5228783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228812 : List Nat := [2, 2, 1, 2, 2, 2, 3, 9]
def baseStart_5228812 : Nat := 118140960795 + 5228812 * 2 ^ 59
def prefixEnd_5228812 : Nat := 4983230072969 + 3 ^ 40 * 5228812 * 2
def baseEnd_5228812 : Nat := 99440511407300054914931

theorem tailTrace_5228812 : CollatzResearch.WordTrace tailWord_5228812 prefixEnd_5228812 99440511407300054914931 := by
  unfold tailWord_5228812
  simp only [CollatzResearch.WordTrace]
  refine ⟨95355220566457304419276345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127140294088609739225701793 95355220566457304419276345)
  ·
    refine ⟨71516415424842978314457259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95355220566457304419276345 71516415424842978314457259)
    ·
      refine ⟨107274623137264467471685889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71516415424842978314457259 107274623137264467471685889)
      ·
        refine ⟨80455967352948350603764417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107274623137264467471685889 80455967352948350603764417)
        ·
          refine ⟨60341975514711262952823313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80455967352948350603764417 60341975514711262952823313)
          ·
            refine ⟨45256481636033447214617485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60341975514711262952823313 45256481636033447214617485)
            ·
              refine ⟨16971180613512542705481557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45256481636033447214617485 16971180613512542705481557)
              ·
                refine ⟨99440511407300054914931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16971180613512542705481557 99440511407300054914931)
                ·
                  rfl

theorem cell23_5228812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 9].length) (baseStart_5228812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228812 prefixEnd_5228812 := by exact prefixLift 5228812
  have htrace : WordTrace (prefixWord ++ tailWord_5228812) baseStart_5228812 baseEnd_5228812 := by
    simpa [prefixWord, tailWord_5228812, baseEnd_5228812] using wordTrace_append hprefix tailTrace_5228812
  have hstable : (prefixWord ++ tailWord_5228812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228812).length < 2 ^ (prefixWord ++ tailWord_5228812).sum := by decide
  have hdescent : baseEnd_5228812 < baseStart_5228812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228826 : List Nat := [3, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5]
def baseStart_5228826 : Nat := 118140960795 + 5228826 * 2 ^ 59
def prefixEnd_5228826 : Nat := 4983230072969 + 3 ^ 40 * 5228826 * 2
def baseEnd_5228826 : Nat := 2684900996726264427928073

theorem tailTrace_5228826 : CollatzResearch.WordTrace tailWord_5228826 prefixEnd_5228826 2684900996726264427928073 := by
  unfold tailWord_5228826
  simp only [CollatzResearch.WordTrace]
  refine ⟨47677737938715972307390583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127140634503242592819708221 47677737938715972307390583)
  ·
    refine ⟨71516606908073958461085875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47677737938715972307390583 71516606908073958461085875)
    ·
      refine ⟨107274910362110937691628813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71516606908073958461085875 107274910362110937691628813)
      ·
        refine ⟨40228091385791601634360805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107274910362110937691628813 40228091385791601634360805)
        ·
          refine ⟨7542767134835925306442651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40228091385791601634360805 7542767134835925306442651)
          ·
            refine ⟨11314150702253887959663977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7542767134835925306442651 11314150702253887959663977)
            ·
              refine ⟨8485613026690415969747983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11314150702253887959663977 8485613026690415969747983)
              ·
                refine ⟨12728419540035623954621975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8485613026690415969747983 12728419540035623954621975)
                ·
                  refine ⟨19092629310053435931932963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12728419540035623954621975 19092629310053435931932963)
                  ·
                    refine ⟨28638943965080153897899445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19092629310053435931932963 28638943965080153897899445)
                    ·
                      refine ⟨2684900996726264427928073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28638943965080153897899445 2684900996726264427928073)
                      ·
                        rfl

theorem cell23_5228826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_5228826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228826 prefixEnd_5228826 := by exact prefixLift 5228826
  have htrace : WordTrace (prefixWord ++ tailWord_5228826) baseStart_5228826 baseEnd_5228826 := by
    simpa [prefixWord, tailWord_5228826, baseEnd_5228826] using wordTrace_append hprefix tailTrace_5228826
  have hstable : (prefixWord ++ tailWord_5228826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228826).length < 2 ^ (prefixWord ++ tailWord_5228826).sum := by decide
  have hdescent : baseEnd_5228826 < baseStart_5228826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228850 : List Nat := [3, 2, 1, 1, 5, 2, 2, 1, 2, 4]
def baseStart_5228850 : Nat := 118140960795 + 5228850 * 2 ^ 59
def prefixEnd_5228850 : Nat := 4983230072969 + 3 ^ 40 * 5228850 * 2
def baseEnd_5228850 : Nat := 894971106753990778009321

theorem tailTrace_5228850 : CollatzResearch.WordTrace tailWord_5228850 prefixEnd_5228850 894971106753990778009321 := by
  unfold tailWord_5228850
  simp only [CollatzResearch.WordTrace]
  refine ⟨47677956776694235332109001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127141218071184627552290669 47677956776694235332109001)
  ·
    refine ⟨35758467582520676499081751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47677956776694235332109001 35758467582520676499081751)
    ·
      refine ⟨53637701373781014748622627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35758467582520676499081751 53637701373781014748622627)
      ·
        refine ⟨80456552060671522122933941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53637701373781014748622627 80456552060671522122933941)
        ·
          refine ⟨7542801755687955199025057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80456552060671522122933941 7542801755687955199025057)
          ·
            refine ⟨5657101316765966399268793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7542801755687955199025057 5657101316765966399268793)
            ·
              refine ⟨4242825987574474799451595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5657101316765966399268793 4242825987574474799451595)
              ·
                refine ⟨6364238981361712199177393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4242825987574474799451595 6364238981361712199177393)
                ·
                  refine ⟨4773179236021284149383045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6364238981361712199177393 4773179236021284149383045)
                  ·
                    refine ⟨894971106753990778009321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4773179236021284149383045 894971106753990778009321)
                    ·
                      rfl

theorem cell23_5228850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_5228850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228850 prefixEnd_5228850 := by exact prefixLift 5228850
  have htrace : WordTrace (prefixWord ++ tailWord_5228850) baseStart_5228850 baseEnd_5228850 := by
    simpa [prefixWord, tailWord_5228850, baseEnd_5228850] using wordTrace_append hprefix tailTrace_5228850
  have hstable : (prefixWord ++ tailWord_5228850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228850).length < 2 ^ (prefixWord ++ tailWord_5228850).sum := by decide
  have hdescent : baseEnd_5228850 < baseStart_5228850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228899 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 3]
def baseStart_5228899 : Nat := 118140960795 + 5228899 * 2 ^ 59
def prefixEnd_5228899 : Nat := 4983230072969 + 3 ^ 40 * 5228899 * 2
def baseEnd_5228899 : Nat := 2684938480814042642315237

theorem tailTrace_5228899 : CollatzResearch.WordTrace tailWord_5228899 prefixEnd_5228899 2684938480814042642315237 := by
  unfold tailWord_5228899
  simp only [CollatzResearch.WordTrace]
  refine ⟨190713614283599422696969751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127142409522399615131313167 190713614283599422696969751)
  ·
    refine ⟨286070421425399134045454627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190713614283599422696969751 286070421425399134045454627)
    ·
      refine ⟨429105632138098701068181941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286070421425399134045454627 429105632138098701068181941)
      ·
        refine ⟨40228653012946753225142057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 429105632138098701068181941 40228653012946753225142057)
        ·
          refine ⟨30171489759710064918856543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40228653012946753225142057 30171489759710064918856543)
          ·
            refine ⟨45257234639565097378284815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30171489759710064918856543 45257234639565097378284815)
            ·
              refine ⟨67885851959347646067427223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45257234639565097378284815 67885851959347646067427223)
              ·
                refine ⟨101828777939021469101140835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67885851959347646067427223 101828777939021469101140835)
                ·
                  refine ⟨152743166908532203651711253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101828777939021469101140835 152743166908532203651711253)
                  ·
                    refine ⟨7159835948837447046173965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 152743166908532203651711253 7159835948837447046173965)
                    ·
                      refine ⟨2684938480814042642315237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7159835948837447046173965 2684938480814042642315237)
                      ·
                        rfl

theorem cell23_5228899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_5228899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228899 prefixEnd_5228899 := by exact prefixLift 5228899
  have htrace : WordTrace (prefixWord ++ tailWord_5228899) baseStart_5228899 baseEnd_5228899 := by
    simpa [prefixWord, tailWord_5228899, baseEnd_5228899] using wordTrace_append hprefix tailTrace_5228899
  have hstable : (prefixWord ++ tailWord_5228899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228899).length < 2 ^ (prefixWord ++ tailWord_5228899).sum := by decide
  have hdescent : baseEnd_5228899 < baseStart_5228899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228906 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 2, 6]
def baseStart_5228906 : Nat := 118140960795 + 5228906 * 2 ^ 59
def prefixEnd_5228906 : Nat := 4983230072969 + 3 ^ 40 * 5228906 * 2
def baseEnd_5228906 : Nat := 894980691726208038309235

theorem tailTrace_5228906 : CollatzResearch.WordTrace tailWord_5228906 prefixEnd_5228906 894980691726208038309235 := by
  unfold tailWord_5228906
  simp only [CollatzResearch.WordTrace]
  refine ⟨47678467398643515723118643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127142579729716041928316381 47678467398643515723118643)
  ·
    refine ⟨71517701097965273584677965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47678467398643515723118643 71517701097965273584677965)
    ·
      refine ⟨26819137911736977594254237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71517701097965273584677965 26819137911736977594254237)
      ·
        refine ⟨10057176716901366597845339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26819137911736977594254237 10057176716901366597845339)
        ·
          refine ⟨15085765075352049896768009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10057176716901366597845339 15085765075352049896768009)
          ·
            refine ⟨11314323806514037422576007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15085765075352049896768009 11314323806514037422576007)
            ·
              refine ⟨16971485709771056133864011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11314323806514037422576007 16971485709771056133864011)
              ·
                refine ⟨25457228564656584200796017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16971485709771056133864011 25457228564656584200796017)
                ·
                  refine ⟨19092921423492438150597013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25457228564656584200796017 19092921423492438150597013)
                  ·
                    refine ⟨894980691726208038309235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19092921423492438150597013 894980691726208038309235)
                    ·
                      rfl

theorem cell23_5228906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_5228906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228906 prefixEnd_5228906 := by exact prefixLift 5228906
  have htrace : WordTrace (prefixWord ++ tailWord_5228906) baseStart_5228906 baseEnd_5228906 := by
    simpa [prefixWord, tailWord_5228906, baseEnd_5228906] using wordTrace_append hprefix tailTrace_5228906
  have hstable : (prefixWord ++ tailWord_5228906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228906).length < 2 ^ (prefixWord ++ tailWord_5228906).sum := by decide
  have hdescent : baseEnd_5228906 < baseStart_5228906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228949 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 4, 5]
def baseStart_5228949 : Nat := 118140960795 + 5228949 * 2 ^ 59
def prefixEnd_5228949 : Nat := 4983230072969 + 3 ^ 40 * 5228949 * 2
def baseEnd_5228949 : Nat := 894988051615589148896669

theorem tailTrace_5228949 : CollatzResearch.WordTrace tailWord_5228949 prefixEnd_5228949 894988051615589148896669 := by
  unfold tailWord_5228949
  simp only [CollatzResearch.WordTrace]
  refine ⟨190715437933418281236289901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127143625288945520824193267 190715437933418281236289901)
  ·
    refine ⟨71518289225031855463608713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190715437933418281236289901 71518289225031855463608713)
    ·
      refine ⟨53638716918773891597706535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71518289225031855463608713 53638716918773891597706535)
      ·
        refine ⟨80458075378160837396559803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53638716918773891597706535 80458075378160837396559803)
        ·
          refine ⟨120687113067241256094839705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80458075378160837396559803 120687113067241256094839705)
          ·
            refine ⟨90515334800430942071129779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120687113067241256094839705 90515334800430942071129779)
            ·
              refine ⟨135773002200646413106694669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90515334800430942071129779 135773002200646413106694669)
              ·
                refine ⟨50914875825242404915010501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135773002200646413106694669 50914875825242404915010501)
                ·
                  refine ⟨9546539217232950921564469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50914875825242404915010501 9546539217232950921564469)
                  ·
                    refine ⟨894988051615589148896669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9546539217232950921564469 894988051615589148896669)
                    ·
                      rfl

theorem cell23_5228949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_5228949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228949 prefixEnd_5228949 := by exact prefixLift 5228949
  have htrace : WordTrace (prefixWord ++ tailWord_5228949) baseStart_5228949 baseEnd_5228949 := by
    simpa [prefixWord, tailWord_5228949, baseEnd_5228949] using wordTrace_append hprefix tailTrace_5228949
  have hstable : (prefixWord ++ tailWord_5228949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228949).length < 2 ^ (prefixWord ++ tailWord_5228949).sum := by decide
  have hdescent : baseEnd_5228949 < baseStart_5228949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228959 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 7]
def baseStart_5228959 : Nat := 118140960795 + 5228959 * 2 ^ 59
def prefixEnd_5228959 : Nat := 4983230072969 + 3 ^ 40 * 5228959 * 2
def baseEnd_5228959 : Nat := 2684969289653312407564961

theorem tailTrace_5228959 : CollatzResearch.WordTrace tailWord_5228959 prefixEnd_5228959 2684969289653312407564961 := by
  unfold tailWord_5228959
  simp only [CollatzResearch.WordTrace]
  refine ⟨190715802663382052944153931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127143868442254701962769287 190715802663382052944153931)
  ·
    refine ⟨286073703995073079416230897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190715802663382052944153931 286073703995073079416230897)
    ·
      refine ⟨214555277996304809562173173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286073703995073079416230897 214555277996304809562173173)
      ·
        refine ⟨20114557312153575896453735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 214555277996304809562173173 20114557312153575896453735)
        ·
          refine ⟨30171835968230363844680603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20114557312153575896453735 30171835968230363844680603)
          ·
            refine ⟨45257753952345545767020905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30171835968230363844680603 45257753952345545767020905)
            ·
              refine ⟨33943315464259159325265679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45257753952345545767020905 33943315464259159325265679)
              ·
                refine ⟨50914973196388738987898519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33943315464259159325265679 50914973196388738987898519)
                ·
                  refine ⟨76372459794583108481847779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50914973196388738987898519 76372459794583108481847779)
                  ·
                    refine ⟨114558689691874662722771669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76372459794583108481847779 114558689691874662722771669)
                    ·
                      refine ⟨2684969289653312407564961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114558689691874662722771669 2684969289653312407564961)
                      ·
                        rfl

theorem cell23_5228959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_5228959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228959 prefixEnd_5228959 := by exact prefixLift 5228959
  have htrace : WordTrace (prefixWord ++ tailWord_5228959) baseStart_5228959 baseEnd_5228959 := by
    simpa [prefixWord, tailWord_5228959, baseEnd_5228959] using wordTrace_append hprefix tailTrace_5228959
  have hstable : (prefixWord ++ tailWord_5228959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228959).length < 2 ^ (prefixWord ++ tailWord_5228959).sum := by decide
  have hdescent : baseEnd_5228959 < baseStart_5228959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5228986 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2]
def baseStart_5228986 : Nat := 118140960795 + 5228986 * 2 ^ 59
def prefixEnd_5228986 : Nat := 4983230072969 + 3 ^ 40 * 5228986 * 2
def baseEnd_5228986 : Nat := 2684983153630983801927337

theorem tailTrace_5228986 : CollatzResearch.WordTrace tailWord_5228986 prefixEnd_5228986 2684983153630983801927337 := by
  unfold tailWord_5228986
  simp only [CollatzResearch.WordTrace]
  refine ⟨47679196858571059138846703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127144524956189491036924541 47679196858571059138846703)
  ·
    refine ⟨71518795287856588708270055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47679196858571059138846703 71518795287856588708270055)
    ·
      refine ⟨107278192931784883062405083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71518795287856588708270055 107278192931784883062405083)
      ·
        refine ⟨160917289397677324593607625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107278192931784883062405083 160917289397677324593607625)
        ·
          refine ⟨120687967048257993445205719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160917289397677324593607625 120687967048257993445205719)
          ·
            refine ⟨181031950572386990167808579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120687967048257993445205719 181031950572386990167808579)
            ·
              refine ⟨271547925858580485251712869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181031950572386990167808579 271547925858580485251712869)
              ·
                refine ⟨50915236098483840984696163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 271547925858580485251712869 50915236098483840984696163)
                ·
                  refine ⟨76372854147725761477044245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50915236098483840984696163 76372854147725761477044245)
                  ·
                    refine ⟨3579977538174645069236449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76372854147725761477044245 3579977538174645069236449)
                    ·
                      refine ⟨2684983153630983801927337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3579977538174645069236449 2684983153630983801927337)
                      ·
                        rfl

theorem cell23_5228986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2].length) (baseStart_5228986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5228986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5228986 prefixEnd_5228986 := by exact prefixLift 5228986
  have htrace : WordTrace (prefixWord ++ tailWord_5228986) baseStart_5228986 baseEnd_5228986 := by
    simpa [prefixWord, tailWord_5228986, baseEnd_5228986] using wordTrace_append hprefix tailTrace_5228986
  have hstable : (prefixWord ++ tailWord_5228986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5228986).length < 2 ^ (prefixWord ++ tailWord_5228986).sum := by decide
  have hdescent : baseEnd_5228986 < baseStart_5228986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5228986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229013 : List Nat := [1, 3, 2, 3, 1, 2, 3, 1, 3, 4]
def baseStart_5229013 : Nat := 118140960795 + 5229013 * 2 ^ 59
def prefixEnd_5229013 : Nat := 4983230072969 + 3 ^ 40 * 5229013 * 2
def baseEnd_5229013 : Nat := 894999005869551732096571

theorem tailTrace_5229013 : CollatzResearch.WordTrace tailWord_5229013 prefixEnd_5229013 894999005869551732096571 := by
  unfold tailWord_5229013
  simp only [CollatzResearch.WordTrace]
  refine ⟨190717772205186420166619693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127145181470124280111079795 190717772205186420166619693)
  ·
    refine ⟨71519164576944907562482385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190717772205186420166619693 71519164576944907562482385)
    ·
      refine ⟨53639373432708680671861789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71519164576944907562482385 53639373432708680671861789)
      ·
        refine ⟨20114765037265755251948171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53639373432708680671861789 20114765037265755251948171)
        ·
          refine ⟨30172147555898632877922257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20114765037265755251948171 30172147555898632877922257)
          ·
            refine ⟨22629110666923974658441693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30172147555898632877922257 22629110666923974658441693)
            ·
              refine ⟨8485916500096490496915635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22629110666923974658441693 8485916500096490496915635)
              ·
                refine ⟨12728874750144735745373453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8485916500096490496915635 12728874750144735745373453)
                ·
                  refine ⟨4773328031304275904515045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12728874750144735745373453 4773328031304275904515045)
                  ·
                    refine ⟨894999005869551732096571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4773328031304275904515045 894999005869551732096571)
                    ·
                      rfl

theorem cell23_5229013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_5229013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229013 prefixEnd_5229013 := by exact prefixLift 5229013
  have htrace : WordTrace (prefixWord ++ tailWord_5229013) baseStart_5229013 baseEnd_5229013 := by
    simpa [prefixWord, tailWord_5229013, baseEnd_5229013] using wordTrace_append hprefix tailTrace_5229013
  have hstable : (prefixWord ++ tailWord_5229013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229013).length < 2 ^ (prefixWord ++ tailWord_5229013).sum := by decide
  have hdescent : baseEnd_5229013 < baseStart_5229013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229099 : List Nat := [1, 1, 1, 1, 2, 1, 3, 13]
def baseStart_5229099 : Nat := 118140960795 + 5229099 * 2 ^ 59
def prefixEnd_5229099 : Nat := 4983230072969 + 3 ^ 40 * 5229099 * 2
def baseEnd_5229099 : Nat := 99445969516479328141271

theorem tailTrace_5229099 : CollatzResearch.WordTrace tailWord_5229099 prefixEnd_5229099 99445969516479328141271 := by
  unfold tailWord_5229099
  simp only [CollatzResearch.WordTrace]
  refine ⟨190720908882874856854250351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127147272588583237902833567 190720908882874856854250351)
  ·
    refine ⟨286081363324312285281375527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190720908882874856854250351 286081363324312285281375527)
    ·
      refine ⟨429122044986468427922063291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286081363324312285281375527 429122044986468427922063291)
      ·
        refine ⟨643683067479702641883094937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429122044986468427922063291 643683067479702641883094937)
        ·
          refine ⟨482762300609776981412321203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 643683067479702641883094937 482762300609776981412321203)
          ·
            refine ⟨724143450914665472118481805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482762300609776981412321203 724143450914665472118481805)
            ·
              refine ⟨271553794092999552044430677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 724143450914665472118481805 271553794092999552044430677)
              ·
                refine ⟨99445969516479328141271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 271553794092999552044430677 99445969516479328141271)
                ·
                  rfl

theorem cell23_5229099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 13].length) (baseStart_5229099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229099 prefixEnd_5229099 := by exact prefixLift 5229099
  have htrace : WordTrace (prefixWord ++ tailWord_5229099) baseStart_5229099 baseEnd_5229099 := by
    simpa [prefixWord, tailWord_5229099, baseEnd_5229099] using wordTrace_append hprefix tailTrace_5229099
  have hstable : (prefixWord ++ tailWord_5229099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229099).length < 2 ^ (prefixWord ++ tailWord_5229099).sum := by decide
  have hdescent : baseEnd_5229099 < baseStart_5229099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229116 : List Nat := [2, 2, 2, 2, 3, 2, 10]
def baseStart_5229116 : Nat := 118140960795 + 5229116 * 2 ^ 59
def prefixEnd_5229116 : Nat := 4983230072969 + 3 ^ 40 * 5229116 * 2
def baseEnd_5229116 : Nat := 33148764273037880164219

theorem tailTrace_5229116 : CollatzResearch.WordTrace tailWord_5229116 prefixEnd_5229116 33148764273037880164219 := by
  unfold tailWord_5229116
  simp only [CollatzResearch.WordTrace]
  refine ⟨95360764461906634378809601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127147685949208845838412801 95360764461906634378809601)
  ·
    refine ⟨71520573346429975784107201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95360764461906634378809601 71520573346429975784107201)
    ·
      refine ⟨53640430009822481838080401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71520573346429975784107201 53640430009822481838080401)
      ·
        refine ⟨40230322507366861378560301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53640430009822481838080401 40230322507366861378560301)
        ·
          refine ⟨15086370940262573016960113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40230322507366861378560301 15086370940262573016960113)
          ·
            refine ⟨11314778205196929762720085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15086370940262573016960113 11314778205196929762720085)
            ·
              refine ⟨33148764273037880164219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11314778205196929762720085 33148764273037880164219)
              ·
                rfl

theorem cell23_5229116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 10].length) (baseStart_5229116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229116 prefixEnd_5229116 := by exact prefixLift 5229116
  have htrace : WordTrace (prefixWord ++ tailWord_5229116) baseStart_5229116 baseEnd_5229116 := by
    simpa [prefixWord, tailWord_5229116, baseEnd_5229116] using wordTrace_append hprefix tailTrace_5229116
  have hstable : (prefixWord ++ tailWord_5229116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229116).length < 2 ^ (prefixWord ++ tailWord_5229116).sum := by decide
  have hdescent : baseEnd_5229116 < baseStart_5229116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229127 : List Nat := [1, 1, 4, 1, 4, 2, 2, 1, 3, 2, 2]
def baseStart_5229127 : Nat := 118140960795 + 5229127 * 2 ^ 59
def prefixEnd_5229127 : Nat := 4983230072969 + 3 ^ 40 * 5229127 * 2
def baseEnd_5229127 : Nat := 2685055554403267750264189

theorem tailTrace_5229127 : CollatzResearch.WordTrace tailWord_5229127 prefixEnd_5229127 2685055554403267750264189 := by
  unfold tailWord_5229127
  simp only [CollatzResearch.WordTrace]
  refine ⟨190721930126773417636269635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127147953417848945090846423 190721930126773417636269635)
  ·
    refine ⟨286082895190160126454404453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190721930126773417636269635 286082895190160126454404453)
    ·
      refine ⟨53640542848155023710200835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 286082895190160126454404453 53640542848155023710200835)
      ·
        refine ⟨80460814272232535565301253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53640542848155023710200835 80460814272232535565301253)
        ·
          refine ⟨15086402676043600418493985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80460814272232535565301253 15086402676043600418493985)
          ·
            refine ⟨11314802007032700313870489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15086402676043600418493985 11314802007032700313870489)
            ·
              refine ⟨8486101505274525235402867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11314802007032700313870489 8486101505274525235402867)
              ·
                refine ⟨12729152257911787853104301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8486101505274525235402867 12729152257911787853104301)
                ·
                  refine ⟨4773432096716920444914113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12729152257911787853104301 4773432096716920444914113)
                  ·
                    refine ⟨3580074072537690333685585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4773432096716920444914113 3580074072537690333685585)
                    ·
                      refine ⟨2685055554403267750264189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3580074072537690333685585 2685055554403267750264189)
                      ·
                        rfl

theorem cell23_5229127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 2, 2].length) (baseStart_5229127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229127 prefixEnd_5229127 := by exact prefixLift 5229127
  have htrace : WordTrace (prefixWord ++ tailWord_5229127) baseStart_5229127 baseEnd_5229127 := by
    simpa [prefixWord, tailWord_5229127, baseEnd_5229127] using wordTrace_append hprefix tailTrace_5229127
  have hstable : (prefixWord ++ tailWord_5229127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229127).length < 2 ^ (prefixWord ++ tailWord_5229127).sum := by decide
  have hdescent : baseEnd_5229127 < baseStart_5229127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229140 : List Nat := [2, 4, 1, 1, 1, 5, 1, 1, 1, 2, 4]
def baseStart_5229140 : Nat := 118140960795 + 5229140 * 2 ^ 59
def prefixEnd_5229140 : Nat := 4983230072969 + 3 ^ 40 * 5229140 * 2
def baseEnd_5229140 : Nat := 2685062229651776199401629

theorem tailTrace_5229140 : CollatzResearch.WordTrace tailWord_5229140 prefixEnd_5229140 2685062229651776199401629 := by
  unfold tailWord_5229140
  simp only [CollatzResearch.WordTrace]
  refine ⟨95361202137863160428246437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127148269517150880570995249 95361202137863160428246437)
  ·
    refine ⟨17880225400849342580296207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95361202137863160428246437 17880225400849342580296207)
    ·
      refine ⟨26820338101274013870444311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17880225400849342580296207 26820338101274013870444311)
      ·
        refine ⟨40230507151911020805666467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26820338101274013870444311 40230507151911020805666467)
        ·
          refine ⟨60345760727866531208499701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40230507151911020805666467 60345760727866531208499701)
          ·
            refine ⟨5657415068237487300796847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60345760727866531208499701 5657415068237487300796847)
            ·
              refine ⟨8486122602356230951195271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5657415068237487300796847 8486122602356230951195271)
              ·
                refine ⟨12729183903534346426792907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8486122602356230951195271 12729183903534346426792907)
                ·
                  refine ⟨19093775855301519640189361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12729183903534346426792907 19093775855301519640189361)
                  ·
                    refine ⟨14320331891476139730142021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19093775855301519640189361 14320331891476139730142021)
                    ·
                      refine ⟨2685062229651776199401629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14320331891476139730142021 2685062229651776199401629)
                      ·
                        rfl

theorem cell23_5229140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_5229140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229140 prefixEnd_5229140 := by exact prefixLift 5229140
  have htrace : WordTrace (prefixWord ++ tailWord_5229140) baseStart_5229140 baseEnd_5229140 := by
    simpa [prefixWord, tailWord_5229140, baseEnd_5229140] using wordTrace_append hprefix tailTrace_5229140
  have hstable : (prefixWord ++ tailWord_5229140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229140).length < 2 ^ (prefixWord ++ tailWord_5229140).sum := by decide
  have hdescent : baseEnd_5229140 < baseStart_5229140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229156 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5]
def baseStart_5229156 : Nat := 118140960795 + 5229156 * 2 ^ 59
def prefixEnd_5229156 : Nat := 4983230072969 + 3 ^ 40 * 5229156 * 2
def baseEnd_5229156 : Nat := 2685070445342248136801555

theorem tailTrace_5229156 : CollatzResearch.WordTrace tailWord_5229156 prefixEnd_5229156 2685070445342248136801555 := by
  unfold tailWord_5229156
  simp only [CollatzResearch.WordTrace]
  refine ⟨95361493921834177794537661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127148658562445570392716881 95361493921834177794537661)
  ·
    refine ⟨35760560220687816672951623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95361493921834177794537661 35760560220687816672951623)
    ·
      refine ⟨53640840331031725009427435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35760560220687816672951623 53640840331031725009427435)
      ·
        refine ⟨80461260496547587514141153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53640840331031725009427435 80461260496547587514141153)
        ·
          refine ⟨60345945372410690635605865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80461260496547587514141153 60345945372410690635605865)
          ·
            refine ⟨45259459029308017976704399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60345945372410690635605865 45259459029308017976704399)
            ·
              refine ⟨67889188543962026965056599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45259459029308017976704399 67889188543962026965056599)
              ·
                refine ⟨101833782815943040447584899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67889188543962026965056599 101833782815943040447584899)
                ·
                  refine ⟨152750674223914560671377349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101833782815943040447584899 152750674223914560671377349)
                  ·
                    refine ⟨28640751416983980125883253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 152750674223914560671377349 28640751416983980125883253)
                    ·
                      refine ⟨2685070445342248136801555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28640751416983980125883253 2685070445342248136801555)
                      ·
                        rfl

theorem cell23_5229156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_5229156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229156 prefixEnd_5229156 := by exact prefixLift 5229156
  have htrace : WordTrace (prefixWord ++ tailWord_5229156) baseStart_5229156 baseEnd_5229156 := by
    simpa [prefixWord, tailWord_5229156, baseEnd_5229156] using wordTrace_append hprefix tailTrace_5229156
  have hstable : (prefixWord ++ tailWord_5229156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229156).length < 2 ^ (prefixWord ++ tailWord_5229156).sum := by decide
  have hdescent : baseEnd_5229156 < baseStart_5229156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229183 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 5, 4, 2]
def baseStart_5229183 : Nat := 118140960795 + 5229183 * 2 ^ 59
def prefixEnd_5229183 : Nat := 4983230072969 + 3 ^ 40 * 5229183 * 2
def baseEnd_5229183 : Nat := 2685084309319919531163931

theorem tailTrace_5229183 : CollatzResearch.WordTrace tailWord_5229183 prefixEnd_5229183 2685084309319919531163931 := by
  unfold tailWord_5229183
  simp only [CollatzResearch.WordTrace]
  refine ⟨190723972614570539200308203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127149315076380359466872135 190723972614570539200308203)
  ·
    refine ⟨286085958921855808800462305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190723972614570539200308203 286085958921855808800462305)
    ·
      refine ⟨214564469191391856600346729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286085958921855808800462305 214564469191391856600346729)
      ·
        refine ⟨160923351893543892450260047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214564469191391856600346729 160923351893543892450260047)
        ·
          refine ⟨241385027840315838675390071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160923351893543892450260047 241385027840315838675390071)
          ·
            refine ⟨362077541760473758013085107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241385027840315838675390071 362077541760473758013085107)
            ·
              refine ⟨543116312640710637019627661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362077541760473758013085107 543116312640710637019627661)
              ·
                refine ⟨203668617240266488882360373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 543116312640710637019627661 203668617240266488882360373)
                ·
                  refine ⟨19093932866274983332721285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 203668617240266488882360373 19093932866274983332721285)
                  ·
                    refine ⟨3580112412426559374885241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19093932866274983332721285 3580112412426559374885241)
                    ·
                      refine ⟨2685084309319919531163931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3580112412426559374885241 2685084309319919531163931)
                      ·
                        rfl

theorem cell23_5229183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 4, 2].length) (baseStart_5229183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229183 prefixEnd_5229183 := by exact prefixLift 5229183
  have htrace : WordTrace (prefixWord ++ tailWord_5229183) baseStart_5229183 baseEnd_5229183 := by
    simpa [prefixWord, tailWord_5229183, baseEnd_5229183] using wordTrace_append hprefix tailTrace_5229183
  have hstable : (prefixWord ++ tailWord_5229183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229183).length < 2 ^ (prefixWord ++ tailWord_5229183).sum := by decide
  have hdescent : baseEnd_5229183 < baseStart_5229183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229204 : List Nat := [2, 4, 2, 2, 1, 1, 3, 2, 1, 3, 2]
def baseStart_5229204 : Nat := 118140960795 + 5229204 * 2 ^ 59
def prefixEnd_5229204 : Nat := 4983230072969 + 3 ^ 40 * 5229204 * 2
def baseEnd_5229204 : Nat := 2685095092413663949001335

theorem tailTrace_5229204 : CollatzResearch.WordTrace tailWord_5229204 prefixEnd_5229204 2685095092413663949001335 := by
  unfold tailWord_5229204
  simp only [CollatzResearch.WordTrace]
  refine ⟨95362369273747229893411333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127149825698329639857881777 95362369273747229893411333)
  ·
    refine ⟨17880444238827605605014625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95362369273747229893411333 17880444238827605605014625)
    ·
      refine ⟨13410333179120704203760969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17880444238827605605014625 13410333179120704203760969)
      ·
        refine ⟨10057749884340528152820727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13410333179120704203760969 10057749884340528152820727)
        ·
          refine ⟨15086624826510792229231091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10057749884340528152820727 15086624826510792229231091)
          ·
            refine ⟨22629937239766188343846637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15086624826510792229231091 22629937239766188343846637)
            ·
              refine ⟨8486226464912320628942489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22629937239766188343846637 8486226464912320628942489)
              ·
                refine ⟨6364669848684240471706867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8486226464912320628942489 6364669848684240471706867)
                ·
                  refine ⟨9547004773026360707560301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6364669848684240471706867 9547004773026360707560301)
                  ·
                    refine ⟨3580126789884885265335113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9547004773026360707560301 3580126789884885265335113)
                    ·
                      refine ⟨2685095092413663949001335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3580126789884885265335113 2685095092413663949001335)
                      ·
                        rfl

theorem cell23_5229204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_5229204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229204 prefixEnd_5229204 := by exact prefixLift 5229204
  have htrace : WordTrace (prefixWord ++ tailWord_5229204) baseStart_5229204 baseEnd_5229204 := by
    simpa [prefixWord, tailWord_5229204, baseEnd_5229204] using wordTrace_append hprefix tailTrace_5229204
  have hstable : (prefixWord ++ tailWord_5229204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229204).length < 2 ^ (prefixWord ++ tailWord_5229204).sum := by decide
  have hdescent : baseEnd_5229204 < baseStart_5229204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229217 : List Nat := [1, 2, 3, 3, 3, 1, 1, 2, 1, 4, 2]
def baseStart_5229217 : Nat := 118140960795 + 5229217 * 2 ^ 59
def prefixEnd_5229217 : Nat := 4983230072969 + 3 ^ 40 * 5229217 * 2
def baseEnd_5229217 : Nat := 2685101767662172398138775

theorem tailTrace_5229217 : CollatzResearch.WordTrace tailWord_5229217 prefixEnd_5229217 2685101767662172398138775 := by
  unfold tailWord_5229217
  simp only [CollatzResearch.WordTrace]
  refine ⟨190725212696447363007045905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127150141797631575338030603 190725212696447363007045905)
  ·
    refine ⟨143043909522335522255284429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190725212696447363007045905 143043909522335522255284429)
    ·
      refine ⟨53641466070875820845731661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143043909522335522255284429 53641466070875820845731661)
      ·
        refine ⟨20115549776578432817149373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53641466070875820845731661 20115549776578432817149373)
        ·
          refine ⟨7543331166216912306431015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20115549776578432817149373 7543331166216912306431015)
          ·
            refine ⟨11314996749325368459646523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7543331166216912306431015 11314996749325368459646523)
            ·
              refine ⟨16972495123988052689469785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11314996749325368459646523 16972495123988052689469785)
              ·
                refine ⟨12729371342991039517102339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16972495123988052689469785 12729371342991039517102339)
                ·
                  refine ⟨19094057014486559275653509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12729371342991039517102339 19094057014486559275653509)
                  ·
                    refine ⟨3580135690216229864185033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19094057014486559275653509 3580135690216229864185033)
                    ·
                      refine ⟨2685101767662172398138775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3580135690216229864185033 2685101767662172398138775)
                      ·
                        rfl

theorem cell23_5229217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_5229217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229217 prefixEnd_5229217 := by exact prefixLift 5229217
  have htrace : WordTrace (prefixWord ++ tailWord_5229217) baseStart_5229217 baseEnd_5229217 := by
    simpa [prefixWord, tailWord_5229217, baseEnd_5229217] using wordTrace_append hprefix tailTrace_5229217
  have hstable : (prefixWord ++ tailWord_5229217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229217).length < 2 ^ (prefixWord ++ tailWord_5229217).sum := by decide
  have hdescent : baseEnd_5229217 < baseStart_5229217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229273 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 1, 3, 4]
def baseStart_5229273 : Nat := 118140960795 + 5229273 * 2 ^ 59
def prefixEnd_5229273 : Nat := 4983230072969 + 3 ^ 40 * 5229273 * 2
def baseEnd_5229273 : Nat := 2685130522578824179038517

theorem tailTrace_5229273 : CollatzResearch.WordTrace tailWord_5229273 prefixEnd_5229273 2685130522578824179038517 := by
  unfold tailWord_5229273
  simp only [CollatzResearch.WordTrace]
  refine ⟨190727255184244484571084473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127151503456162989714056315 190727255184244484571084473)
  ·
    refine ⟨143045441388183363428313355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190727255184244484571084473 143045441388183363428313355)
    ·
      refine ⟨214568162082275045142470033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143045441388183363428313355 214568162082275045142470033)
      ·
        refine ⟨160926121561706283856852525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214568162082275045142470033 160926121561706283856852525)
        ·
          refine ⟨60347295585639856446319697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160926121561706283856852525 60347295585639856446319697)
          ·
            refine ⟨45260471689229892334739773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60347295585639856446319697 45260471689229892334739773)
            ·
              refine ⟨16972676883461209625527415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45260471689229892334739773 16972676883461209625527415)
              ·
                refine ⟨25459015325191814438291123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16972676883461209625527415 25459015325191814438291123)
                ·
                  refine ⟨38188522987787721657436685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25459015325191814438291123 38188522987787721657436685)
                  ·
                    refine ⟨14320696120420395621538757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38188522987787721657436685 14320696120420395621538757)
                    ·
                      refine ⟨2685130522578824179038517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14320696120420395621538757 2685130522578824179038517)
                      ·
                        rfl

theorem cell23_5229273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_5229273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229273 prefixEnd_5229273 := by exact prefixLift 5229273
  have htrace : WordTrace (prefixWord ++ tailWord_5229273) baseStart_5229273 baseEnd_5229273 := by
    simpa [prefixWord, tailWord_5229273, baseEnd_5229273] using wordTrace_append hprefix tailTrace_5229273
  have hstable : (prefixWord ++ tailWord_5229273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229273).length < 2 ^ (prefixWord ++ tailWord_5229273).sum := by decide
  have hdescent : baseEnd_5229273 < baseStart_5229273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229323 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 3]
def baseStart_5229323 : Nat := 118140960795 + 5229323 * 2 ^ 59
def prefixEnd_5229323 : Nat := 4983230072969 + 3 ^ 40 * 5229323 * 2
def baseEnd_5229323 : Nat := 2685156196611548983413287

theorem tailTrace_5229323 : CollatzResearch.WordTrace tailWord_5229323 prefixEnd_5229323 2685156196611548983413287 := by
  unfold tailWord_5229323
  simp only [CollatzResearch.WordTrace]
  refine ⟨190729078834063343110404623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127152719222708895406936415 190729078834063343110404623)
  ·
    refine ⟨286093618251095014665606935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190729078834063343110404623 286093618251095014665606935)
    ·
      refine ⟨429140427376642521998410403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286093618251095014665606935 429140427376642521998410403)
      ·
        refine ⟨643710641064963782997615605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429140427376642521998410403 643710641064963782997615605)
        ·
          refine ⟨60347872599840354656026463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 643710641064963782997615605 60347872599840354656026463)
          ·
            refine ⟨90521808899760531984039695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60347872599840354656026463 90521808899760531984039695)
            ·
              refine ⟨135782713349640797976059543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90521808899760531984039695 135782713349640797976059543)
              ·
                refine ⟨203674070024461196964089315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135782713349640797976059543 203674070024461196964089315)
                ·
                  refine ⟨305511105036691795446133973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203674070024461196964089315 305511105036691795446133973)
                  ·
                    refine ⟨7160416524297463955768765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 305511105036691795446133973 7160416524297463955768765)
                    ·
                      refine ⟨2685156196611548983413287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7160416524297463955768765 2685156196611548983413287)
                      ·
                        rfl

theorem cell23_5229323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 3].length) (baseStart_5229323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229323 prefixEnd_5229323 := by exact prefixLift 5229323
  have htrace : WordTrace (prefixWord ++ tailWord_5229323) baseStart_5229323 baseEnd_5229323 := by
    simpa [prefixWord, tailWord_5229323, baseEnd_5229323] using wordTrace_append hprefix tailTrace_5229323
  have hstable : (prefixWord ++ tailWord_5229323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229323).length < 2 ^ (prefixWord ++ tailWord_5229323).sum := by decide
  have hdescent : baseEnd_5229323 < baseStart_5229323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229390 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 6, 4]
def baseStart_5229390 : Nat := 118140960795 + 5229390 * 2 ^ 59
def prefixEnd_5229390 : Nat := 4983230072969 + 3 ^ 40 * 5229390 * 2
def baseEnd_5229390 : Nat := 895063533271800073758493

theorem tailTrace_5229390 : CollatzResearch.WordTrace tailWord_5229390 prefixEnd_5229390 895063533271800073758493 := by
  unfold tailWord_5229390
  simp only [CollatzResearch.WordTrace]
  refine ⟨23841440315602576694136703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127154348349880409035395749 23841440315602576694136703)
  ·
    refine ⟨35762160473403865041205055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23841440315602576694136703 35762160473403865041205055)
    ·
      refine ⟨53643240710105797561807583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35762160473403865041205055 53643240710105797561807583)
      ·
        refine ⟨80464861065158696342711375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53643240710105797561807583 80464861065158696342711375)
        ·
          refine ⟨120697291597738044514067063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80464861065158696342711375 120697291597738044514067063)
          ·
            refine ⟨181045937396607066771100595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120697291597738044514067063 181045937396607066771100595)
            ·
              refine ⟨271568906094910600156650893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181045937396607066771100595 271568906094910600156650893)
              ·
                refine ⟨101838339785591475058744085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 271568906094910600156650893 101838339785591475058744085)
                ·
                  refine ⟨4773672177449600393378629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 101838339785591475058744085 4773672177449600393378629)
                  ·
                    refine ⟨895063533271800073758493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4773672177449600393378629 895063533271800073758493)
                    ·
                      rfl

theorem cell23_5229390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_5229390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229390 prefixEnd_5229390 := by exact prefixLift 5229390
  have htrace : WordTrace (prefixWord ++ tailWord_5229390) baseStart_5229390 baseEnd_5229390 := by
    simpa [prefixWord, tailWord_5229390, baseEnd_5229390] using wordTrace_append hprefix tailTrace_5229390
  have hstable : (prefixWord ++ tailWord_5229390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229390).length < 2 ^ (prefixWord ++ tailWord_5229390).sum := by decide
  have hdescent : baseEnd_5229390 < baseStart_5229390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229407 : List Nat := [1, 1, 2, 3, 1, 3, 4, 2, 2, 4]
def baseStart_5229407 : Nat := 118140960795 + 5229407 * 2 ^ 59
def prefixEnd_5229407 : Nat := 4983230072969 + 3 ^ 40 * 5229407 * 2
def baseEnd_5229407 : Nat := 895066442995508884920967

theorem tailTrace_5229407 : CollatzResearch.WordTrace tailWord_5229407 prefixEnd_5229407 895066442995508884920967 := by
  unfold tailWord_5229407
  simp only [CollatzResearch.WordTrace]
  refine ⟨190732142565759025456462475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127154761710506016970974983 190732142565759025456462475)
  ·
    refine ⟨286098213848638538184693713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190732142565759025456462475 286098213848638538184693713)
    ·
      refine ⟨214573660386478903638520285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286098213848638538184693713 214573660386478903638520285)
      ·
        refine ⟨80465122644929588864445107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214573660386478903638520285 80465122644929588864445107)
        ·
          refine ⟨120697683967394383296667661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80465122644929588864445107 120697683967394383296667661)
          ·
            refine ⟨45261631487772893736250373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120697683967394383296667661 45261631487772893736250373)
            ·
              refine ⟨8486555903957417575546945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45261631487772893736250373 8486555903957417575546945)
              ·
                refine ⟨6364916927968063181660209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8486555903957417575546945 6364916927968063181660209)
                ·
                  refine ⟨4773687695976047386245157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6364916927968063181660209 4773687695976047386245157)
                  ·
                    refine ⟨895066442995508884920967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4773687695976047386245157 895066442995508884920967)
                    ·
                      rfl

theorem cell23_5229407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 4].length) (baseStart_5229407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229407 prefixEnd_5229407 := by exact prefixLift 5229407
  have htrace : WordTrace (prefixWord ++ tailWord_5229407) baseStart_5229407 baseEnd_5229407 := by
    simpa [prefixWord, tailWord_5229407, baseEnd_5229407] using wordTrace_append hprefix tailTrace_5229407
  have hstable : (prefixWord ++ tailWord_5229407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229407).length < 2 ^ (prefixWord ++ tailWord_5229407).sum := by decide
  have hdescent : baseEnd_5229407 < baseStart_5229407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229423 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 6]
def baseStart_5229423 : Nat := 118140960795 + 5229423 * 2 ^ 59
def prefixEnd_5229423 : Nat := 4983230072969 + 3 ^ 40 * 5229423 * 2
def baseEnd_5229423 : Nat := 2685207544676998592162827

theorem tailTrace_5229423 : CollatzResearch.WordTrace tailWord_5229423 prefixEnd_5229423 2685207544676998592162827 := by
  unfold tailWord_5229423
  simp only [CollatzResearch.WordTrace]
  refine ⟨190732726133701060189044923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127155150755800706792696615 190732726133701060189044923)
  ·
    refine ⟨286099089200551590283567385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190732726133701060189044923 286099089200551590283567385)
    ·
      refine ⟨214574316900413692712675539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286099089200551590283567385 214574316900413692712675539)
      ·
        refine ⟨321861475350620539069013309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214574316900413692712675539 321861475350620539069013309)
        ·
          refine ⟨120698053256482702150879991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 321861475350620539069013309 120698053256482702150879991)
          ·
            refine ⟨181047079884724053226319987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120698053256482702150879991 181047079884724053226319987)
            ·
              refine ⟨271570619827086079839479981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181047079884724053226319987 271570619827086079839479981)
              ·
                refine ⟨101838982435157279939804993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 271570619827086079839479981 101838982435157279939804993)
                ·
                  refine ⟨76379236826367959954853745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101838982435157279939804993 76379236826367959954853745)
                  ·
                    refine ⟨57284427619775969966140309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76379236826367959954853745 57284427619775969966140309)
                    ·
                      refine ⟨2685207544676998592162827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57284427619775969966140309 2685207544676998592162827)
                      ·
                        rfl

theorem cell23_5229423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_5229423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229423 prefixEnd_5229423 := by exact prefixLift 5229423
  have htrace : WordTrace (prefixWord ++ tailWord_5229423) baseStart_5229423 baseEnd_5229423 := by
    simpa [prefixWord, tailWord_5229423, baseEnd_5229423] using wordTrace_append hprefix tailTrace_5229423
  have hstable : (prefixWord ++ tailWord_5229423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229423).length < 2 ^ (prefixWord ++ tailWord_5229423).sum := by decide
  have hdescent : baseEnd_5229423 < baseStart_5229423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229447 : List Nat := [1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 3]
def baseStart_5229447 : Nat := 118140960795 + 5229447 * 2 ^ 59
def prefixEnd_5229447 : Nat := 4983230072969 + 3 ^ 40 * 5229447 * 2
def baseEnd_5229447 : Nat := 2685219868212706498262717

theorem tailTrace_5229447 : CollatzResearch.WordTrace tailWord_5229447 prefixEnd_5229447 2685219868212706498262717 := by
  unfold tailWord_5229447
  simp only [CollatzResearch.WordTrace]
  refine ⟨190733601485614112287918595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127155734323742741525279063 190733601485614112287918595)
  ·
    refine ⟨286100402228421168431877893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190733601485614112287918595 286100402228421168431877893)
    ·
      refine ⟨53643825417828969080977105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 286100402228421168431877893 53643825417828969080977105)
      ·
        refine ⟨40232869063371726810732829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53643825417828969080977105 40232869063371726810732829)
        ·
          refine ⟨15087325898764397554024811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40232869063371726810732829 15087325898764397554024811)
          ·
            refine ⟨22630988848146596331037217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15087325898764397554024811 22630988848146596331037217)
            ·
              refine ⟨16973241636109947248277913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22630988848146596331037217 16973241636109947248277913)
              ·
                refine ⟨12729931227082460436208435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16973241636109947248277913 12729931227082460436208435)
                ·
                  refine ⟨19094896840623690654312653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12729931227082460436208435 19094896840623690654312653)
                  ·
                    refine ⟨7160586315233883995367245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19094896840623690654312653 7160586315233883995367245)
                    ·
                      refine ⟨2685219868212706498262717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7160586315233883995367245 2685219868212706498262717)
                      ·
                        rfl

theorem cell23_5229447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_5229447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229447 prefixEnd_5229447 := by exact prefixLift 5229447
  have htrace : WordTrace (prefixWord ++ tailWord_5229447) baseStart_5229447 baseEnd_5229447 := by
    simpa [prefixWord, tailWord_5229447, baseEnd_5229447] using wordTrace_append hprefix tailTrace_5229447
  have hstable : (prefixWord ++ tailWord_5229447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229447).length < 2 ^ (prefixWord ++ tailWord_5229447).sum := by decide
  have hdescent : baseEnd_5229447 < baseStart_5229447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229448 : List Nat := [2, 1, 3, 3, 2, 2, 2, 3, 1, 2, 2]
def baseStart_5229448 : Nat := 118140960795 + 5229448 * 2 ^ 59
def prefixEnd_5229448 : Nat := 4983230072969 + 3 ^ 40 * 5229448 * 2
def baseEnd_5229448 : Nat := 2685220381693360994350213

theorem tailTrace_5229448 : CollatzResearch.WordTrace tailWord_5229448 prefixEnd_5229448 2685220381693360994350213 := by
  unfold tailWord_5229448
  simp only [CollatzResearch.WordTrace]
  refine ⟨95366818979305244729352499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127155758639073659639136665 95366818979305244729352499)
  ·
    refine ⟨143050228468957867094028749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95366818979305244729352499 143050228468957867094028749)
    ·
      refine ⟨53643835675859200160260781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143050228468957867094028749 53643835675859200160260781)
      ·
        refine ⟨20116438378447200060097793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53643835675859200160260781 20116438378447200060097793)
        ·
          refine ⟨15087328783835400045073345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20116438378447200060097793 15087328783835400045073345)
          ·
            refine ⟨11315496587876550033805009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15087328783835400045073345 11315496587876550033805009)
            ·
              refine ⟨8486622440907412525353757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11315496587876550033805009 8486622440907412525353757)
              ·
                refine ⟨3182483415340279697007659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8486622440907412525353757 3182483415340279697007659)
                ·
                  refine ⟨4773725123010419545511489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3182483415340279697007659 4773725123010419545511489)
                  ·
                    refine ⟨3580293842257814659133617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4773725123010419545511489 3580293842257814659133617)
                    ·
                      refine ⟨2685220381693360994350213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3580293842257814659133617 2685220381693360994350213)
                      ·
                        rfl

theorem cell23_5229448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_5229448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229448 prefixEnd_5229448 := by exact prefixLift 5229448
  have htrace : WordTrace (prefixWord ++ tailWord_5229448) baseStart_5229448 baseEnd_5229448 := by
    simpa [prefixWord, tailWord_5229448, baseEnd_5229448] using wordTrace_append hprefix tailTrace_5229448
  have hstable : (prefixWord ++ tailWord_5229448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229448).length < 2 ^ (prefixWord ++ tailWord_5229448).sum := by decide
  have hdescent : baseEnd_5229448 < baseStart_5229448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229458 : List Nat := [3, 2, 3, 2, 3, 1, 1, 2, 2, 4]
def baseStart_5229458 : Nat := 118140960795 + 5229458 * 2 ^ 59
def prefixEnd_5229458 : Nat := 4983230072969 + 3 ^ 40 * 5229458 * 2
def baseEnd_5229458 : Nat := 895075172166635318408389

theorem tailTrace_5229458 : CollatzResearch.WordTrace tailWord_5229458 prefixEnd_5229458 895075172166635318408389 := by
  unfold tailWord_5229458
  simp only [CollatzResearch.WordTrace]
  refine ⟨47683500672143565291642257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127156001792382840777712685 47683500672143565291642257)
  ·
    refine ⟨35762625504107673968731693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47683500672143565291642257 35762625504107673968731693)
    ·
      refine ⟨13410984564040377738274385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35762625504107673968731693 13410984564040377738274385)
      ·
        refine ⟨10058238423030283303705789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13410984564040377738274385 10058238423030283303705789)
        ·
          refine ⟨3771839408636356238889671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10058238423030283303705789 3771839408636356238889671)
          ·
            refine ⟨5657759112954534358334507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3771839408636356238889671 5657759112954534358334507)
            ·
              refine ⟨8486638669431801537501761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5657759112954534358334507 8486638669431801537501761)
              ·
                refine ⟨6364979002073851153126321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8486638669431801537501761 6364979002073851153126321)
                ·
                  refine ⟨4773734251555388364844741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6364979002073851153126321 4773734251555388364844741)
                  ·
                    refine ⟨895075172166635318408389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4773734251555388364844741 895075172166635318408389)
                    ·
                      rfl

theorem cell23_5229458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_5229458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229458 prefixEnd_5229458 := by exact prefixLift 5229458
  have htrace : WordTrace (prefixWord ++ tailWord_5229458) baseStart_5229458 baseEnd_5229458 := by
    simpa [prefixWord, tailWord_5229458, baseEnd_5229458] using wordTrace_append hprefix tailTrace_5229458
  have hstable : (prefixWord ++ tailWord_5229458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229458).length < 2 ^ (prefixWord ++ tailWord_5229458).sum := by decide
  have hdescent : baseEnd_5229458 < baseStart_5229458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229487 : List Nat := [1, 1, 2, 1, 2, 2, 2, 5, 1, 4, 2]
def baseStart_5229487 : Nat := 118140960795 + 5229487 * 2 ^ 59
def prefixEnd_5229487 : Nat := 4983230072969 + 3 ^ 40 * 5229487 * 2
def baseEnd_5229487 : Nat := 2685240407438886341762533

theorem tailTrace_5229487 : CollatzResearch.WordTrace tailWord_5229487 prefixEnd_5229487 2685240407438886341762533 := by
  unfold tailWord_5229487
  simp only [CollatzResearch.WordTrace]
  refine ⟨190735060405469199119374715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127156706936979466079583143 190735060405469199119374715)
  ·
    refine ⟨286102590608203798679062073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190735060405469199119374715 286102590608203798679062073)
    ·
      refine ⟨214576942956152849009296555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286102590608203798679062073 214576942956152849009296555)
      ·
        refine ⟨321865414434229273513944833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214576942956152849009296555 321865414434229273513944833)
        ·
          refine ⟨241399060825671955135458625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321865414434229273513944833 241399060825671955135458625)
          ·
            refine ⟨181049295619253966351593969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241399060825671955135458625 181049295619253966351593969)
            ·
              refine ⟨135786971714440474763695477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181049295619253966351593969 135786971714440474763695477)
              ·
                refine ⟨12730028598228794509096451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135786971714440474763695477 12730028598228794509096451)
                ·
                  refine ⟨19095042897343191763644677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12730028598228794509096451 19095042897343191763644677)
                  ·
                    refine ⟨3580320543251848455683377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19095042897343191763644677 3580320543251848455683377)
                    ·
                      refine ⟨2685240407438886341762533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3580320543251848455683377 2685240407438886341762533)
                      ·
                        rfl

theorem cell23_5229487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 4, 2].length) (baseStart_5229487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229487 prefixEnd_5229487 := by exact prefixLift 5229487
  have htrace : WordTrace (prefixWord ++ tailWord_5229487) baseStart_5229487 baseEnd_5229487 := by
    simpa [prefixWord, tailWord_5229487, baseEnd_5229487] using wordTrace_append hprefix tailTrace_5229487
  have hstable : (prefixWord ++ tailWord_5229487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229487).length < 2 ^ (prefixWord ++ tailWord_5229487).sum := by decide
  have hdescent : baseEnd_5229487 < baseStart_5229487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229504 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 4, 2, 2]
def baseStart_5229504 : Nat := 118140960795 + 5229504 * 2 ^ 59
def prefixEnd_5229504 : Nat := 4983230072969 + 3 ^ 40 * 5229504 * 2
def baseEnd_5229504 : Nat := 2685249136610012775249955

theorem tailTrace_5229504 : CollatzResearch.WordTrace tailWord_5229504 prefixEnd_5229504 2685249136610012775249955 := by
  unfold tailWord_5229504
  simp only [CollatzResearch.WordTrace]
  refine ⟨95367840223203805511371783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127157120297605074015162377 95367840223203805511371783)
  ·
    refine ⟨143051760334805708267057675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95367840223203805511371783 143051760334805708267057675)
    ·
      refine ⟨214577640502208562400586513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143051760334805708267057675 214577640502208562400586513)
      ·
        refine ⟨160933230376656421800439885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214577640502208562400586513 160933230376656421800439885)
        ·
          refine ⟨60349961391246158175164957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160933230376656421800439885 60349961391246158175164957)
          ·
            refine ⟨22631235521717309315686859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60349961391246158175164957 22631235521717309315686859)
            ·
              refine ⟨33946853282575963973530289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22631235521717309315686859 33946853282575963973530289)
              ·
                refine ⟨25460139961931972980147717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33946853282575963973530289 25460139961931972980147717)
                ·
                  refine ⟨4773776242862244933777697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25460139961931972980147717 4773776242862244933777697)
                  ·
                    refine ⟨3580332182146683700333273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4773776242862244933777697 3580332182146683700333273)
                    ·
                      refine ⟨2685249136610012775249955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3580332182146683700333273 2685249136610012775249955)
                      ·
                        rfl

theorem cell23_5229504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 4, 2, 2].length) (baseStart_5229504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229504 prefixEnd_5229504 := by exact prefixLift 5229504
  have htrace : WordTrace (prefixWord ++ tailWord_5229504) baseStart_5229504 baseEnd_5229504 := by
    simpa [prefixWord, tailWord_5229504, baseEnd_5229504] using wordTrace_append hprefix tailTrace_5229504
  have hstable : (prefixWord ++ tailWord_5229504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229504).length < 2 ^ (prefixWord ++ tailWord_5229504).sum := by decide
  have hdescent : baseEnd_5229504 < baseStart_5229504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229540 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 1, 7]
def baseStart_5229540 : Nat := 118140960795 + 5229540 * 2 ^ 59
def prefixEnd_5229540 : Nat := 4983230072969 + 3 ^ 40 * 5229540 * 2
def baseEnd_5229540 : Nat := 895089207304524878133263

theorem tailTrace_5229540 : CollatzResearch.WordTrace tailWord_5229540 prefixEnd_5229540 895089207304524878133263 := by
  unfold tailWord_5229540
  simp only [CollatzResearch.WordTrace]
  refine ⟨95368496737138594585527037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127157995649518126114036049 95368496737138594585527037)
  ·
    refine ⟨35763186276426972969572639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95368496737138594585527037 35763186276426972969572639)
    ·
      refine ⟨53644779414640459454358959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35763186276426972969572639 53644779414640459454358959)
      ·
        refine ⟨80467169121960689181538439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53644779414640459454358959 80467169121960689181538439)
        ·
          refine ⟨120700753682941033772307659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80467169121960689181538439 120700753682941033772307659)
          ·
            refine ⟨181051130524411550658461489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120700753682941033772307659 181051130524411550658461489)
            ·
              refine ⟨135788347893308662993846117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181051130524411550658461489 135788347893308662993846117)
              ·
                refine ⟨25460315229995374311346147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135788347893308662993846117 25460315229995374311346147)
                ·
                  refine ⟨38190472844993061467019221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25460315229995374311346147 38190472844993061467019221)
                  ·
                    refine ⟨895089207304524878133263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38190472844993061467019221 895089207304524878133263)
                    ·
                      rfl

theorem cell23_5229540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_5229540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229540 prefixEnd_5229540 := by exact prefixLift 5229540
  have htrace : WordTrace (prefixWord ++ tailWord_5229540) baseStart_5229540 baseEnd_5229540 := by
    simpa [prefixWord, tailWord_5229540, baseEnd_5229540] using wordTrace_append hprefix tailTrace_5229540
  have hstable : (prefixWord ++ tailWord_5229540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229540).length < 2 ^ (prefixWord ++ tailWord_5229540).sum := by decide
  have hdescent : baseEnd_5229540 < baseStart_5229540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229577 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 3, 6, 2]
def baseStart_5229577 : Nat := 118140960795 + 5229577 * 2 ^ 59
def prefixEnd_5229577 : Nat := 4983230072969 + 3 ^ 40 * 5229577 * 2
def baseEnd_5229577 : Nat := 2685286620697790989637119

theorem tailTrace_5229577 : CollatzResearch.WordTrace tailWord_5229577 prefixEnd_5229577 2685286620697790989637119 := by
  unfold tailWord_5229577
  simp only [CollatzResearch.WordTrace]
  refine ⟨190738342975143144490150985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127158895316762096326767323 190738342975143144490150985)
  ·
    refine ⟨143053757231357358367613239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190738342975143144490150985 143053757231357358367613239)
    ·
      refine ⟨214580635847036037551419859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143053757231357358367613239 214580635847036037551419859)
      ·
        refine ⟨321870953770554056327129789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214580635847036037551419859 321870953770554056327129789)
        ·
          refine ⟨120701607663957771122673671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 321870953770554056327129789 120701607663957771122673671)
          ·
            refine ⟨181052411495936656684010507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120701607663957771122673671 181052411495936656684010507)
            ·
              refine ⟨271578617243904985026015761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181052411495936656684010507 271578617243904985026015761)
              ·
                refine ⟨203683962932928738769511821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271578617243904985026015761 203683962932928738769511821)
                ·
                  refine ⟨76381486099848277038566933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 203683962932928738769511821 76381486099848277038566933)
                  ·
                    refine ⟨3580382160930387986182825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76381486099848277038566933 3580382160930387986182825)
                    ·
                      refine ⟨2685286620697790989637119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3580382160930387986182825 2685286620697790989637119)
                      ·
                        rfl

theorem cell23_5229577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 6, 2].length) (baseStart_5229577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229577 prefixEnd_5229577 := by exact prefixLift 5229577
  have htrace : WordTrace (prefixWord ++ tailWord_5229577) baseStart_5229577 baseEnd_5229577 := by
    simpa [prefixWord, tailWord_5229577, baseEnd_5229577] using wordTrace_append hprefix tailTrace_5229577
  have hstable : (prefixWord ++ tailWord_5229577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229577).length < 2 ^ (prefixWord ++ tailWord_5229577).sum := by decide
  have hdescent : baseEnd_5229577 < baseStart_5229577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229587 : List Nat := [1, 1, 1, 2, 1, 4, 1, 5, 3, 4]
def baseStart_5229587 : Nat := 118140960795 + 5229587 * 2 ^ 59
def prefixEnd_5229587 : Nat := 4983230072969 + 3 ^ 40 * 5229587 * 2
def baseEnd_5229587 : Nat := 895097251834778650170691

theorem tailTrace_5229587 : CollatzResearch.WordTrace tailWord_5229587 prefixEnd_5229587 895097251834778650170691 := by
  unfold tailWord_5229587
  simp only [CollatzResearch.WordTrace]
  refine ⟨190738707705106916198015015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127159138470071277465343343 190738707705106916198015015)
  ·
    refine ⟨286108061557660374297022523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190738707705106916198015015 286108061557660374297022523)
    ·
      refine ⟨429162092336490561445533785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286108061557660374297022523 429162092336490561445533785)
      ·
        refine ⟨321871569252367921084150339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429162092336490561445533785 321871569252367921084150339)
        ·
          refine ⟨482807353878551881626225509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321871569252367921084150339 482807353878551881626225509)
          ·
            refine ⟨90526378852228477804917283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 482807353878551881626225509 90526378852228477804917283)
            ·
              refine ⟨135789568278342716707375925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90526378852228477804917283 135789568278342716707375925)
              ·
                refine ⟨12730272026094629691316493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135789568278342716707375925 12730272026094629691316493)
                ·
                  refine ⟨4773852009785486134243685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12730272026094629691316493 4773852009785486134243685)
                  ·
                    refine ⟨895097251834778650170691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4773852009785486134243685 895097251834778650170691)
                    ·
                      rfl

theorem cell23_5229587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 4].length) (baseStart_5229587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229587 prefixEnd_5229587 := by exact prefixLift 5229587
  have htrace : WordTrace (prefixWord ++ tailWord_5229587) baseStart_5229587 baseEnd_5229587 := by
    simpa [prefixWord, tailWord_5229587, baseEnd_5229587] using wordTrace_append hprefix tailTrace_5229587
  have hstable : (prefixWord ++ tailWord_5229587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229587).length < 2 ^ (prefixWord ++ tailWord_5229587).sum := by decide
  have hdescent : baseEnd_5229587 < baseStart_5229587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229594 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2]
def baseStart_5229594 : Nat := 118140960795 + 5229594 * 2 ^ 59
def prefixEnd_5229594 : Nat := 4983230072969 + 3 ^ 40 * 5229594 * 2
def baseEnd_5229594 : Nat := 2685295349868917423124541

theorem tailTrace_5229594 : CollatzResearch.WordTrace tailWord_5229594 prefixEnd_5229594 2685295349868917423124541 := by
  unfold tailWord_5229594
  simp only [CollatzResearch.WordTrace]
  refine ⟨47684740754020389098379959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127159308677387704262346557 47684740754020389098379959)
  ·
    refine ⟨71527111131030583647569939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47684740754020389098379959 71527111131030583647569939)
    ·
      refine ⟨107290666696545875471354909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71527111131030583647569939 107290666696545875471354909)
      ·
        refine ⟨40234000011204703301758091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107290666696545875471354909 40234000011204703301758091)
        ·
          refine ⟨60351000016807054952637137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40234000011204703301758091 60351000016807054952637137)
          ·
            refine ⟨45263250012605291214477853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60351000016807054952637137 45263250012605291214477853)
            ·
              refine ⟨16973718754726984205429195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45263250012605291214477853 16973718754726984205429195)
              ·
                refine ⟨25460578132090476308143793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16973718754726984205429195 25460578132090476308143793)
                ·
                  refine ⟨19095433599067857231107845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25460578132090476308143793 19095433599067857231107845)
                  ·
                    refine ⟨3580393799825223230832721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19095433599067857231107845 3580393799825223230832721)
                    ·
                      refine ⟨2685295349868917423124541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3580393799825223230832721 2685295349868917423124541)
                      ·
                        rfl

theorem cell23_5229594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_5229594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229594 prefixEnd_5229594 := by exact prefixLift 5229594
  have htrace : WordTrace (prefixWord ++ tailWord_5229594) baseStart_5229594 baseEnd_5229594 := by
    simpa [prefixWord, tailWord_5229594, baseEnd_5229594] using wordTrace_append hprefix tailTrace_5229594
  have hstable : (prefixWord ++ tailWord_5229594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229594).length < 2 ^ (prefixWord ++ tailWord_5229594).sum := by decide
  have hdescent : baseEnd_5229594 < baseStart_5229594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229604 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 5, 4]
def baseStart_5229604 : Nat := 118140960795 + 5229604 * 2 ^ 59
def prefixEnd_5229604 : Nat := 4983230072969 + 3 ^ 40 * 5229604 * 2
def baseEnd_5229604 : Nat := 895100161558487461333165

theorem tailTrace_5229604 : CollatzResearch.WordTrace tailWord_5229604 prefixEnd_5229604 895100161558487461333165 := by
  unfold tailWord_5229604
  simp only [CollatzResearch.WordTrace]
  refine ⟨95369663873022664050691933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127159551830696885400922577 95369663873022664050691933)
  ·
    refine ⟨35763623952383499019009475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95369663873022664050691933 35763623952383499019009475)
    ·
      refine ⟨53645435928575248528514213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35763623952383499019009475 53645435928575248528514213)
      ·
        refine ⟨10058519236607859099096415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53645435928575248528514213 10058519236607859099096415)
        ·
          refine ⟨15087778854911788648644623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10058519236607859099096415 15087778854911788648644623)
          ·
            refine ⟨22631668282367682972966935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15087778854911788648644623 22631668282367682972966935)
            ·
              refine ⟨33947502423551524459450403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22631668282367682972966935 33947502423551524459450403)
              ·
                refine ⟨50921253635327286689175605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33947502423551524459450403 50921253635327286689175605)
                ·
                  refine ⟨4773867528311933127110213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50921253635327286689175605 4773867528311933127110213)
                  ·
                    refine ⟨895100161558487461333165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4773867528311933127110213 895100161558487461333165)
                    ·
                      rfl

theorem cell23_5229604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_5229604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229604 prefixEnd_5229604 := by exact prefixLift 5229604
  have htrace : WordTrace (prefixWord ++ tailWord_5229604) baseStart_5229604 baseEnd_5229604 := by
    simpa [prefixWord, tailWord_5229604, baseEnd_5229604] using wordTrace_append hprefix tailTrace_5229604
  have hstable : (prefixWord ++ tailWord_5229604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229604).length < 2 ^ (prefixWord ++ tailWord_5229604).sum := by decide
  have hdescent : baseEnd_5229604 < baseStart_5229604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229614 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_5229614 : Nat := 118140960795 + 5229614 * 2 ^ 59
def prefixEnd_5229614 : Nat := 4983230072969 + 3 ^ 40 * 5229614 * 2
def baseEnd_5229614 : Nat := 2685305619482007344874449

theorem tailTrace_5229614 : CollatzResearch.WordTrace tailWord_5229614 prefixEnd_5229614 2685305619482007344874449 := by
  unfold tailWord_5229614
  simp only [CollatzResearch.WordTrace]
  refine ⟨23842461559501137476155987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127159794984006066539498597 23842461559501137476155987)
  ·
    refine ⟨35763692339251706214233981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23842461559501137476155987 35763692339251706214233981)
    ·
      refine ⟨13411384627219389830337743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35763692339251706214233981 13411384627219389830337743)
      ·
        refine ⟨20117076940829084745506615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13411384627219389830337743 20117076940829084745506615)
        ·
          refine ⟨30175615411243627118259923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20117076940829084745506615 30175615411243627118259923)
          ·
            refine ⟨45263423116865440677389885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30175615411243627118259923 45263423116865440677389885)
            ·
              refine ⟨16973783668824540254021207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45263423116865440677389885 16973783668824540254021207)
              ·
                refine ⟨25460675503236810381031811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16973783668824540254021207 25460675503236810381031811)
                ·
                  refine ⟨38191013254855215571547717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25460675503236810381031811 38191013254855215571547717)
                  ·
                    refine ⟨7160814985285352919665197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38191013254855215571547717 7160814985285352919665197)
                    ·
                      refine ⟨2685305619482007344874449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7160814985285352919665197 2685305619482007344874449)
                      ·
                        rfl

theorem cell23_5229614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_5229614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229614 prefixEnd_5229614 := by exact prefixLift 5229614
  have htrace : WordTrace (prefixWord ++ tailWord_5229614) baseStart_5229614 baseEnd_5229614 := by
    simpa [prefixWord, tailWord_5229614, baseEnd_5229614] using wordTrace_append hprefix tailTrace_5229614
  have hstable : (prefixWord ++ tailWord_5229614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229614).length < 2 ^ (prefixWord ++ tailWord_5229614).sum := by decide
  have hdescent : baseEnd_5229614 < baseStart_5229614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229638 : List Nat := [6, 1, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_5229638 : Nat := 118140960795 + 5229638 * 2 ^ 59
def prefixEnd_5229638 : Nat := 4983230072969 + 3 ^ 40 * 5229638 * 2
def baseEnd_5229638 : Nat := 895105981005905083658113

theorem tailTrace_5229638 : CollatzResearch.WordTrace tailWord_5229638 prefixEnd_5229638 895105981005905083658113 := by
  unfold tailWord_5229638
  simp only [CollatzResearch.WordTrace]
  refine ⟨5960642744622567247128799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 127160378551948101272081045 5960642744622567247128799)
  ·
    refine ⟨8940964116933850870693199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5960642744622567247128799 8940964116933850870693199)
    ·
      refine ⟨13411446175400776306039799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8940964116933850870693199 13411446175400776306039799)
      ·
        refine ⟨20117169263101164459059699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13411446175400776306039799 20117169263101164459059699)
        ·
          refine ⟨30175753894651746688589549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20117169263101164459059699 30175753894651746688589549)
          ·
            refine ⟨11315907710494405008221081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30175753894651746688589549 11315907710494405008221081)
            ·
              refine ⟨8486930782870803756165811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11315907710494405008221081 8486930782870803756165811)
              ·
                refine ⟨12730396174306205634248717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8486930782870803756165811 12730396174306205634248717)
                ·
                  refine ⟨4773898565364827112843269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12730396174306205634248717 4773898565364827112843269)
                  ·
                    refine ⟨895105981005905083658113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4773898565364827112843269 895105981005905083658113)
                    ·
                      rfl

theorem cell23_5229638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_5229638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229638 prefixEnd_5229638 := by exact prefixLift 5229638
  have htrace : WordTrace (prefixWord ++ tailWord_5229638) baseStart_5229638 baseEnd_5229638 := by
    simpa [prefixWord, tailWord_5229638, baseEnd_5229638] using wordTrace_append hprefix tailTrace_5229638
  have hstable : (prefixWord ++ tailWord_5229638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229638).length < 2 ^ (prefixWord ++ tailWord_5229638).sum := by decide
  have hdescent : baseEnd_5229638 < baseStart_5229638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229664 : List Nat := [2, 1, 1, 3, 2, 2, 4, 2, 1, 5]
def baseStart_5229664 : Nat := 118140960795 + 5229664 * 2 ^ 59
def prefixEnd_5229664 : Nat := 4983230072969 + 3 ^ 40 * 5229664 * 2
def baseEnd_5229664 : Nat := 895110431171577383083073

theorem tailTrace_5229664 : CollatzResearch.WordTrace tailWord_5229664 prefixEnd_5229664 895110431171577383083073 := by
  unfold tailWord_5229664
  simp only [CollatzResearch.WordTrace]
  refine ⟨95370758062913979174284023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127161010750551972232378697 95370758062913979174284023)
  ·
    refine ⟨143056137094370968761426035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95370758062913979174284023 143056137094370968761426035)
    ·
      refine ⟨214584205641556453142139053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143056137094370968761426035 214584205641556453142139053)
      ·
        refine ⟨80469077115583669928302145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214584205641556453142139053 80469077115583669928302145)
        ·
          refine ⟨60351807836687752446226609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80469077115583669928302145 60351807836687752446226609)
          ·
            refine ⟨45263855877515814334669957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60351807836687752446226609 45263855877515814334669957)
            ·
              refine ⟨8486972977034215187750617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45263855877515814334669957 8486972977034215187750617)
              ·
                refine ⟨6365229732775661390812963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8486972977034215187750617 6365229732775661390812963)
                ·
                  refine ⟨9547844599163492086219445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6365229732775661390812963 9547844599163492086219445)
                  ·
                    refine ⟨895110431171577383083073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9547844599163492086219445 895110431171577383083073)
                    ·
                      rfl

theorem cell23_5229664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 1, 5].length) (baseStart_5229664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229664 prefixEnd_5229664 := by exact prefixLift 5229664
  have htrace : WordTrace (prefixWord ++ tailWord_5229664) baseStart_5229664 baseEnd_5229664 := by
    simpa [prefixWord, tailWord_5229664, baseEnd_5229664] using wordTrace_append hprefix tailTrace_5229664
  have hstable : (prefixWord ++ tailWord_5229664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229664).length < 2 ^ (prefixWord ++ tailWord_5229664).sum := by decide
  have hdescent : baseEnd_5229664 < baseStart_5229664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229672 : List Nat := [2, 1, 4, 4, 2, 1, 1, 3, 1, 4]
def baseStart_5229672 : Nat := 118140960795 + 5229672 * 2 ^ 59
def prefixEnd_5229672 : Nat := 4983230072969 + 3 ^ 40 * 5229672 * 2
def baseEnd_5229672 : Nat := 895111800453322705983061

theorem tailTrace_5229672 : CollatzResearch.WordTrace tailWord_5229672 prefixEnd_5229672 895111800453322705983061 := by
  unfold tailWord_5229672
  simp only [CollatzResearch.WordTrace]
  refine ⟨95370903954899487857429635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127161205273199317143239513 95370903954899487857429635)
  ·
    refine ⟨143056355932349231786144453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95370903954899487857429635 143056355932349231786144453)
    ·
      refine ⟨26823066737315480959902085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143056355932349231786144453 26823066737315480959902085)
      ·
        refine ⟨5029325013246652679981641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26823066737315480959902085 5029325013246652679981641)
        ·
          refine ⟨3771993759934989509986231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5029325013246652679981641 3771993759934989509986231)
          ·
            refine ⟨5657990639902484264979347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3771993759934989509986231 5657990639902484264979347)
            ·
              refine ⟨8486985959853726397469021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5657990639902484264979347 8486985959853726397469021)
              ·
                refine ⟨3182619734945147399050883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8486985959853726397469021 3182619734945147399050883)
                ·
                  refine ⟨4773929602417721098576325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3182619734945147399050883 4773929602417721098576325)
                  ·
                    refine ⟨895111800453322705983061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4773929602417721098576325 895111800453322705983061)
                    ·
                      rfl

theorem cell23_5229672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_5229672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229672 prefixEnd_5229672 := by exact prefixLift 5229672
  have htrace : WordTrace (prefixWord ++ tailWord_5229672) baseStart_5229672 baseEnd_5229672 := by
    simpa [prefixWord, tailWord_5229672, baseEnd_5229672] using wordTrace_append hprefix tailTrace_5229672
  have hstable : (prefixWord ++ tailWord_5229672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229672).length < 2 ^ (prefixWord ++ tailWord_5229672).sum := by decide
  have hdescent : baseEnd_5229672 < baseStart_5229672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229714 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_5229714 : Nat := 118140960795 + 5229714 * 2 ^ 59
def prefixEnd_5229714 : Nat := 4983230072969 + 3 ^ 40 * 5229714 * 2
def baseEnd_5229714 : Nat := 2685356967547456953623989

theorem tailTrace_5229714 : CollatzResearch.WordTrace tailWord_5229714 prefixEnd_5229714 2685356967547456953623989 := by
  unfold tailWord_5229714
  simp only [CollatzResearch.WordTrace]
  refine ⟨47685834943911704221972049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127162226517097877925258797 47685834943911704221972049)
  ·
    refine ⟨35764376207933778166479037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47685834943911704221972049 35764376207933778166479037)
    ·
      refine ⟨13411641077975166812429639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35764376207933778166479037 13411641077975166812429639)
      ·
        refine ⟨20117461616962750218644459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13411641077975166812429639 20117461616962750218644459)
        ·
          refine ⟨30176192425444125327966689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20117461616962750218644459 30176192425444125327966689)
          ·
            refine ⟨22632144319083093995975017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30176192425444125327966689 22632144319083093995975017)
            ·
              refine ⟨16974108239312320496981263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22632144319083093995975017 16974108239312320496981263)
              ·
                refine ⟨25461162358968480745471895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16974108239312320496981263 25461162358968480745471895)
                ·
                  refine ⟨38191743538452721118207843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25461162358968480745471895 38191743538452721118207843)
                  ·
                    refine ⟨57287615307679081677311765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38191743538452721118207843 57287615307679081677311765)
                    ·
                      refine ⟨2685356967547456953623989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57287615307679081677311765 2685356967547456953623989)
                      ·
                        rfl

theorem cell23_5229714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_5229714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229714 prefixEnd_5229714 := by exact prefixLift 5229714
  have htrace : WordTrace (prefixWord ++ tailWord_5229714) baseStart_5229714 baseEnd_5229714 := by
    simpa [prefixWord, tailWord_5229714, baseEnd_5229714] using wordTrace_append hprefix tailTrace_5229714
  have hstable : (prefixWord ++ tailWord_5229714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229714).length < 2 ^ (prefixWord ++ tailWord_5229714).sum := by decide
  have hdescent : baseEnd_5229714 < baseStart_5229714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229738 : List Nat := [3, 1, 5, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_5229738 : Nat := 118140960795 + 5229738 * 2 ^ 59
def prefixEnd_5229738 : Nat := 4983230072969 + 3 ^ 40 * 5229738 * 2
def baseEnd_5229738 : Nat := 2685369291083164859723879

theorem tailTrace_5229738 : CollatzResearch.WordTrace tailWord_5229738 prefixEnd_5229738 2685369291083164859723879 := by
  unfold tailWord_5229738
  simp only [CollatzResearch.WordTrace]
  refine ⟨47686053781889967246690467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127162810085039912657841245 47686053781889967246690467)
  ·
    refine ⟨71529080672834950870035701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47686053781889967246690467 71529080672834950870035701)
    ·
      refine ⟨6705851313078276644065847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71529080672834950870035701 6705851313078276644065847)
      ·
        refine ⟨10058776969617414966098771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6705851313078276644065847 10058776969617414966098771)
        ·
          refine ⟨15088165454426122449148157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10058776969617414966098771 15088165454426122449148157)
          ·
            refine ⟨5658062045409795918430559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15088165454426122449148157 5658062045409795918430559)
            ·
              refine ⟨8487093068114693877645839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5658062045409795918430559 8487093068114693877645839)
              ·
                refine ⟨12730639602172040816468759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8487093068114693877645839 12730639602172040816468759)
                ·
                  refine ⟨19095959403258061224703139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12730639602172040816468759 19095959403258061224703139)
                  ·
                    refine ⟨28643939104887091837054709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19095959403258061224703139 28643939104887091837054709)
                    ·
                      refine ⟨2685369291083164859723879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28643939104887091837054709 2685369291083164859723879)
                      ·
                        rfl

theorem cell23_5229738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_5229738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229738 prefixEnd_5229738 := by exact prefixLift 5229738
  have htrace : WordTrace (prefixWord ++ tailWord_5229738) baseStart_5229738 baseEnd_5229738 := by
    simpa [prefixWord, tailWord_5229738, baseEnd_5229738] using wordTrace_append hprefix tailTrace_5229738
  have hstable : (prefixWord ++ tailWord_5229738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229738).length < 2 ^ (prefixWord ++ tailWord_5229738).sum := by decide
  have hdescent : baseEnd_5229738 < baseStart_5229738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229747 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 5]
def baseStart_5229747 : Nat := 118140960795 + 5229747 * 2 ^ 59
def prefixEnd_5229747 : Nat := 4983230072969 + 3 ^ 40 * 5229747 * 2
def baseEnd_5229747 : Nat := 2685373912409055324511337

theorem tailTrace_5229747 : CollatzResearch.WordTrace tailWord_5229747 prefixEnd_5229747 2685373912409055324511337 := by
  unfold tailWord_5229747
  simp only [CollatzResearch.WordTrace]
  refine ⟨190744543384527263523839495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127163028923018175682559663 190744543384527263523839495)
  ·
    refine ⟨286116815076790895285759243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190744543384527263523839495 286116815076790895285759243)
    ·
      refine ⟨429175222615186342928638865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286116815076790895285759243 429175222615186342928638865)
      ·
        refine ⟨321881416961389757196479149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429175222615186342928638865 321881416961389757196479149)
        ·
          refine ⟨120705531360521158948679681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 321881416961389757196479149 120705531360521158948679681)
          ·
            refine ⟨90529148520390869211509761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120705531360521158948679681 90529148520390869211509761)
            ·
              refine ⟨67896861390293151908632321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90529148520390869211509761 67896861390293151908632321)
              ·
                refine ⟨50922646042719863931474241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67896861390293151908632321 50922646042719863931474241)
                ·
                  refine ⟨38191984532039897948605681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50922646042719863931474241 38191984532039897948605681)
                  ·
                    refine ⟨28643988399029923461454261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38191984532039897948605681 28643988399029923461454261)
                    ·
                      refine ⟨2685373912409055324511337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28643988399029923461454261 2685373912409055324511337)
                      ·
                        rfl

theorem cell23_5229747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_5229747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229747 prefixEnd_5229747 := by exact prefixLift 5229747
  have htrace : WordTrace (prefixWord ++ tailWord_5229747) baseStart_5229747 baseEnd_5229747 := by
    simpa [prefixWord, tailWord_5229747, baseEnd_5229747] using wordTrace_append hprefix tailTrace_5229747
  have hstable : (prefixWord ++ tailWord_5229747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229747).length < 2 ^ (prefixWord ++ tailWord_5229747).sum := by decide
  have hdescent : baseEnd_5229747 < baseStart_5229747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229778 : List Nat := [3, 2, 2, 2, 1, 1, 2, 4, 1, 3, 2]
def baseStart_5229778 : Nat := 118140960795 + 5229778 * 2 ^ 59
def prefixEnd_5229778 : Nat := 4983230072969 + 3 ^ 40 * 5229778 * 2
def baseEnd_5229778 : Nat := 2685389830309344703223695

theorem tailTrace_5229778 : CollatzResearch.WordTrace tailWord_5229778 prefixEnd_5229778 2685389830309344703223695 := by
  unfold tailWord_5229778
  simp only [CollatzResearch.WordTrace]
  refine ⟨47686418511853738954554497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127163782698276637212145325 47686418511853738954554497)
  ·
    refine ⟨35764813883890304215915873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47686418511853738954554497 35764813883890304215915873)
    ·
      refine ⟨26823610412917728161936905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35764813883890304215915873 26823610412917728161936905)
      ·
        refine ⟨20117707809688296121452679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26823610412917728161936905 20117707809688296121452679)
        ·
          refine ⟨30176561714532444182179019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20117707809688296121452679 30176561714532444182179019)
          ·
            refine ⟨45264842571798666273268529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30176561714532444182179019 45264842571798666273268529)
            ·
              refine ⟨33948631928848999704951397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45264842571798666273268529 33948631928848999704951397)
              ·
                refine ⟨6365368486659187444678387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33948631928848999704951397 6365368486659187444678387)
                ·
                  refine ⟨9548052729988781167017581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6365368486659187444678387 9548052729988781167017581)
                  ·
                    refine ⟨3580519773745792937631593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9548052729988781167017581 3580519773745792937631593)
                    ·
                      refine ⟨2685389830309344703223695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3580519773745792937631593 2685389830309344703223695)
                      ·
                        rfl

theorem cell23_5229778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_5229778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229778 prefixEnd_5229778 := by exact prefixLift 5229778
  have htrace : WordTrace (prefixWord ++ tailWord_5229778) baseStart_5229778 baseEnd_5229778 := by
    simpa [prefixWord, tailWord_5229778, baseEnd_5229778] using wordTrace_append hprefix tailTrace_5229778
  have hstable : (prefixWord ++ tailWord_5229778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229778).length < 2 ^ (prefixWord ++ tailWord_5229778).sum := by decide
  have hdescent : baseEnd_5229778 < baseStart_5229778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229791 : List Nat := [1, 1, 2, 3, 2, 1, 4, 2, 1, 4, 2]
def baseStart_5229791 : Nat := 118140960795 + 5229791 * 2 ^ 59
def prefixEnd_5229791 : Nat := 4983230072969 + 3 ^ 40 * 5229791 * 2
def baseEnd_5229791 : Nat := 2685396505557853152361135

theorem tailTrace_5229791 : CollatzResearch.WordTrace tailWord_5229791 prefixEnd_5229791 2685396505557853152361135 := by
  unfold tailWord_5229791
  simp only [CollatzResearch.WordTrace]
  refine ⟨190746148196367859038441227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127164098797578572692294151 190746148196367859038441227)
  ·
    refine ⟨286119222294551788557661841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190746148196367859038441227 286119222294551788557661841)
    ·
      refine ⟨214589416720913841418246381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286119222294551788557661841 214589416720913841418246381)
      ·
        refine ⟨80471031270342690531842393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214589416720913841418246381 80471031270342690531842393)
        ·
          refine ⟨60353273452757017898881795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80471031270342690531842393 60353273452757017898881795)
          ·
            refine ⟨90529910179135526848322693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60353273452757017898881795 90529910179135526848322693)
            ·
              refine ⟨16974358158587911284060505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90529910179135526848322693 16974358158587911284060505)
              ·
                refine ⟨12730768618940933463045379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16974358158587911284060505 12730768618940933463045379)
                ·
                  refine ⟨19096152928411400194568069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12730768618940933463045379 19096152928411400194568069)
                  ·
                    refine ⟨3580528674077137536481513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19096152928411400194568069 3580528674077137536481513)
                    ·
                      refine ⟨2685396505557853152361135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3580528674077137536481513 2685396505557853152361135)
                      ·
                        rfl

theorem cell23_5229791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 4, 2].length) (baseStart_5229791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229791 prefixEnd_5229791 := by exact prefixLift 5229791
  have htrace : WordTrace (prefixWord ++ tailWord_5229791) baseStart_5229791 baseEnd_5229791 := by
    simpa [prefixWord, tailWord_5229791, baseEnd_5229791] using wordTrace_append hprefix tailTrace_5229791
  have hstable : (prefixWord ++ tailWord_5229791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229791).length < 2 ^ (prefixWord ++ tailWord_5229791).sum := by decide
  have hdescent : baseEnd_5229791 < baseStart_5229791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229804 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 4]
def baseStart_5229804 : Nat := 118140960795 + 5229804 * 2 ^ 59
def prefixEnd_5229804 : Nat := 4983230072969 + 3 ^ 40 * 5229804 * 2
def baseEnd_5229804 : Nat := 2685403180806361601498575

theorem tailTrace_5229804 : CollatzResearch.WordTrace tailWord_5229804 prefixEnd_5229804 2685403180806361601498575 := by
  unfold tailWord_5229804
  simp only [CollatzResearch.WordTrace]
  refine ⟨95373311172660381129332233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127164414896880508172442977 95373311172660381129332233)
  ·
    refine ⟨71529983379495285846999175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95373311172660381129332233 71529983379495285846999175)
    ·
      refine ⟨107294975069242928770498763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71529983379495285846999175 107294975069242928770498763)
      ·
        refine ⟨160942462603864393155748145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107294975069242928770498763 160942462603864393155748145)
        ·
          refine ⟨120706846952898294866811109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160942462603864393155748145 120706846952898294866811109)
          ·
            refine ⟨22632533803668430287527083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120706846952898294866811109 22632533803668430287527083)
            ·
              refine ⟨33948800705502645431290625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22632533803668430287527083 33948800705502645431290625)
              ·
                refine ⟨25461600529126984073467969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33948800705502645431290625 25461600529126984073467969)
                ·
                  refine ⟨19096200396845238055100977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25461600529126984073467969 19096200396845238055100977)
                  ·
                    refine ⟨14322150297633928541325733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19096200396845238055100977 14322150297633928541325733)
                    ·
                      refine ⟨2685403180806361601498575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14322150297633928541325733 2685403180806361601498575)
                      ·
                        rfl

theorem cell23_5229804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_5229804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229804 prefixEnd_5229804 := by exact prefixLift 5229804
  have htrace : WordTrace (prefixWord ++ tailWord_5229804) baseStart_5229804 baseEnd_5229804 := by
    simpa [prefixWord, tailWord_5229804, baseEnd_5229804] using wordTrace_append hprefix tailTrace_5229804
  have hstable : (prefixWord ++ tailWord_5229804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229804).length < 2 ^ (prefixWord ++ tailWord_5229804).sum := by decide
  have hdescent : baseEnd_5229804 < baseStart_5229804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229848 : List Nat := [2, 1, 2, 3, 1, 5, 1, 3, 5]
def baseStart_5229848 : Nat := 118140960795 + 5229848 * 2 ^ 59
def prefixEnd_5229848 : Nat := 4983230072969 + 3 ^ 40 * 5229848 * 2
def baseEnd_5229848 : Nat := 298380641550573269927597

theorem tailTrace_5229848 : CollatzResearch.WordTrace tailWord_5229848 prefixEnd_5229848 298380641550573269927597 := by
  unfold tailWord_5229848
  simp only [CollatzResearch.WordTrace]
  refine ⟨95374113578580678886633099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127165484771440905182177465 95374113578580678886633099)
  ·
    refine ⟨143061170367871018329949649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95374113578580678886633099 143061170367871018329949649)
    ·
      refine ⟨107295877775903263747462237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143061170367871018329949649 107295877775903263747462237)
      ·
        refine ⟨40235954165963723905298339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107295877775903263747462237 40235954165963723905298339)
        ·
          refine ⟨60353931248945585857947509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40235954165963723905298339 60353931248945585857947509)
          ·
            refine ⟨5658181054588648674182579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60353931248945585857947509 5658181054588648674182579)
            ·
              refine ⟨8487271581882973011273869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5658181054588648674182579 8487271581882973011273869)
              ·
                refine ⟨3182726843206114879227701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8487271581882973011273869 3182726843206114879227701)
                ·
                  refine ⟨298380641550573269927597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3182726843206114879227701 298380641550573269927597)
                  ·
                    rfl

theorem cell23_5229848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 5].length) (baseStart_5229848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229848 prefixEnd_5229848 := by exact prefixLift 5229848
  have htrace : WordTrace (prefixWord ++ tailWord_5229848) baseStart_5229848 baseEnd_5229848 := by
    simpa [prefixWord, tailWord_5229848, baseEnd_5229848] using wordTrace_append hprefix tailTrace_5229848
  have hstable : (prefixWord ++ tailWord_5229848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229848).length < 2 ^ (prefixWord ++ tailWord_5229848).sum := by decide
  have hdescent : baseEnd_5229848 < baseStart_5229848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229861 : List Nat := [1, 3, 1, 2, 4, 2, 1, 2, 2, 5]
def baseStart_5229861 : Nat := 118140960795 + 5229861 * 2 ^ 59
def prefixEnd_5229861 : Nat := 4983230072969 + 3 ^ 40 * 5229861 * 2
def baseEnd_5229861 : Nat := 895144149734555959495271

theorem tailTrace_5229861 : CollatzResearch.WordTrace tailWord_5229861 prefixEnd_5229861 895144149734555959495271 := by
  unfold tailWord_5229861
  simp only [CollatzResearch.WordTrace]
  refine ⟨190748701306114260993489437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127165800870742840662326291 190748701306114260993489437)
  ·
    refine ⟨71530762989792847872558539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190748701306114260993489437 71530762989792847872558539)
    ·
      refine ⟨107296144484689271808837809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71530762989792847872558539 107296144484689271808837809)
      ·
        refine ⟨80472108363516953856628357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107296144484689271808837809 80472108363516953856628357)
        ·
          refine ⟨15088520318159428848117817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80472108363516953856628357 15088520318159428848117817)
          ·
            refine ⟨11316390238619571636088363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15088520318159428848117817 11316390238619571636088363)
            ·
              refine ⟨16974585357929357454132545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11316390238619571636088363 16974585357929357454132545)
              ·
                refine ⟨12730939018447018090599409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16974585357929357454132545 12730939018447018090599409)
                ·
                  refine ⟨9548204263835263567949557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12730939018447018090599409 9548204263835263567949557)
                  ·
                    refine ⟨895144149734555959495271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9548204263835263567949557 895144149734555959495271)
                    ·
                      rfl

theorem cell23_5229861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_5229861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229861 prefixEnd_5229861 := by exact prefixLift 5229861
  have htrace : WordTrace (prefixWord ++ tailWord_5229861) baseStart_5229861 baseEnd_5229861 := by
    simpa [prefixWord, tailWord_5229861, baseEnd_5229861] using wordTrace_append hprefix tailTrace_5229861
  have hstable : (prefixWord ++ tailWord_5229861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229861).length < 2 ^ (prefixWord ++ tailWord_5229861).sum := by decide
  have hdescent : baseEnd_5229861 < baseStart_5229861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229948 : List Nat := [2, 2, 2, 1, 1, 1, 5, 2, 3, 1, 3]
def baseStart_5229948 : Nat := 118140960795 + 5229948 * 2 ^ 59
def prefixEnd_5229948 : Nat := 4983230072969 + 3 ^ 40 * 5229948 * 2
def baseEnd_5229948 : Nat := 2685477122020609038097913

theorem tailTrace_5229948 : CollatzResearch.WordTrace tailWord_5229948 prefixEnd_5229948 2685477122020609038097913 := by
  unfold tailWord_5229948
  simp only [CollatzResearch.WordTrace]
  refine ⟨95375937228399537425953249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127167916304532716567937665 95375937228399537425953249)
  ·
    refine ⟨71531952921299653069464937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95375937228399537425953249 71531952921299653069464937)
    ·
      refine ⟨53648964690974739802098703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71531952921299653069464937 53648964690974739802098703)
      ·
        refine ⟨80473447036462109703148055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53648964690974739802098703 80473447036462109703148055)
        ·
          refine ⟨120710170554693164554722083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80473447036462109703148055 120710170554693164554722083)
          ·
            refine ⟨181065255832039746832083125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120710170554693164554722083 181065255832039746832083125)
            ·
              refine ⟨16974867734253726265507793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 181065255832039746832083125 16974867734253726265507793)
              ·
                refine ⟨12731150800690294699130845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16974867734253726265507793 12731150800690294699130845)
                ·
                  refine ⟨4774181550258860512174067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12731150800690294699130845 4774181550258860512174067)
                  ·
                    refine ⟨7161272325388290768261101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4774181550258860512174067 7161272325388290768261101)
                    ·
                      refine ⟨2685477122020609038097913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7161272325388290768261101 2685477122020609038097913)
                      ·
                        rfl

theorem cell23_5229948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_5229948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229948 prefixEnd_5229948 := by exact prefixLift 5229948
  have htrace : WordTrace (prefixWord ++ tailWord_5229948) baseStart_5229948 baseEnd_5229948 := by
    simpa [prefixWord, tailWord_5229948, baseEnd_5229948] using wordTrace_append hprefix tailTrace_5229948
  have hstable : (prefixWord ++ tailWord_5229948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229948).length < 2 ^ (prefixWord ++ tailWord_5229948).sum := by decide
  have hdescent : baseEnd_5229948 < baseStart_5229948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5229971 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 3, 8, 2]
def baseStart_5229971 : Nat := 118140960795 + 5229971 * 2 ^ 59
def prefixEnd_5229971 : Nat := 4983230072969 + 3 ^ 40 * 5229971 * 2
def baseEnd_5229971 : Nat := 2685488932075662448110307

theorem tailTrace_5229971 : CollatzResearch.WordTrace tailWord_5229971 prefixEnd_5229971 2685488932075662448110307 := by
  unfold tailWord_5229971
  simp only [CollatzResearch.WordTrace]
  refine ⟨190752713335715749779993767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127168475557143833186662511 190752713335715749779993767)
  ·
    refine ⟨286129070003573624669990651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190752713335715749779993767 286129070003573624669990651)
    ·
      refine ⟨429193605005360437004985977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286129070003573624669990651 429193605005360437004985977)
      ·
        refine ⟨321895203754020327753739483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429193605005360437004985977 321895203754020327753739483)
        ·
          refine ⟨482842805631030491630609225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321895203754020327753739483 482842805631030491630609225)
          ·
            refine ⟨362132104223272868722956919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 482842805631030491630609225 362132104223272868722956919)
            ·
              refine ⟨543198156334909303084435379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362132104223272868722956919 543198156334909303084435379)
              ·
                refine ⟨814797234502363954626653069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543198156334909303084435379 814797234502363954626653069)
                ·
                  refine ⟨305548962938386482984994901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 814797234502363954626653069 305548962938386482984994901)
                  ·
                    refine ⟨3580651909434216597480409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 305548962938386482984994901 3580651909434216597480409)
                    ·
                      refine ⟨2685488932075662448110307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3580651909434216597480409 2685488932075662448110307)
                      ·
                        rfl

theorem cell23_5229971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 8, 2].length) (baseStart_5229971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5229971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5229971 prefixEnd_5229971 := by exact prefixLift 5229971
  have htrace : WordTrace (prefixWord ++ tailWord_5229971) baseStart_5229971 baseEnd_5229971 := by
    simpa [prefixWord, tailWord_5229971, baseEnd_5229971] using wordTrace_append hprefix tailTrace_5229971
  have hstable : (prefixWord ++ tailWord_5229971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5229971).length < 2 ^ (prefixWord ++ tailWord_5229971).sum := by decide
  have hdescent : baseEnd_5229971 < baseStart_5229971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5229971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230001 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 1, 1, 6]
def baseStart_5230001 : Nat := 118140960795 + 5230001 * 2 ^ 59
def prefixEnd_5230001 : Nat := 4983230072969 + 3 ^ 40 * 5230001 * 2
def baseEnd_5230001 : Nat := 2685504336495297330735169

theorem tailTrace_5230001 : CollatzResearch.WordTrace tailWord_5230001 prefixEnd_5230001 2685504336495297330735169 := by
  unfold tailWord_5230001
  simp only [CollatzResearch.WordTrace]
  refine ⟨190753807525607064903585857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127169205017071376602390571 190753807525607064903585857)
  ·
    refine ⟨143065355644205298677689393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190753807525607064903585857 143065355644205298677689393)
    ·
      refine ⟨107299016733153974008267045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143065355644205298677689393 107299016733153974008267045)
      ·
        refine ⟨20118565637466370126550071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107299016733153974008267045 20118565637466370126550071)
        ·
          refine ⟨30177848456199555189825107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20118565637466370126550071 30177848456199555189825107)
          ·
            refine ⟨45266772684299332784737661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30177848456199555189825107 45266772684299332784737661)
            ·
              refine ⟨16975039756612249794276623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45266772684299332784737661 16975039756612249794276623)
              ·
                refine ⟨25462559634918374691414935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16975039756612249794276623 25462559634918374691414935)
                ·
                  refine ⟨38193839452377562037122403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25462559634918374691414935 38193839452377562037122403)
                  ·
                    refine ⟨57290759178566343055683605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38193839452377562037122403 57290759178566343055683605)
                    ·
                      refine ⟨2685504336495297330735169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57290759178566343055683605 2685504336495297330735169)
                      ·
                        rfl

theorem cell23_5230001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_5230001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230001 prefixEnd_5230001 := by exact prefixLift 5230001
  have htrace : WordTrace (prefixWord ++ tailWord_5230001) baseStart_5230001 baseEnd_5230001 := by
    simpa [prefixWord, tailWord_5230001, baseEnd_5230001] using wordTrace_append hprefix tailTrace_5230001
  have hstable : (prefixWord ++ tailWord_5230001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230001).length < 2 ^ (prefixWord ++ tailWord_5230001).sum := by decide
  have hdescent : baseEnd_5230001 < baseStart_5230001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230005 : List Nat := [1, 3, 3, 2, 2, 2, 2, 2, 1, 1, 4]
def baseStart_5230005 : Nat := 118140960795 + 5230005 * 2 ^ 59
def prefixEnd_5230005 : Nat := 4983230072969 + 3 ^ 40 * 5230005 * 2
def baseEnd_5230005 : Nat := 2685506390417915315085151

theorem tailTrace_5230005 : CollatzResearch.WordTrace tailWord_5230005 prefixEnd_5230005 2685506390417915315085151 := by
  unfold tailWord_5230005
  simp only [CollatzResearch.WordTrace]
  refine ⟨190753953417592573586731469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127169302278395049057820979 190753953417592573586731469)
  ·
    refine ⟨71532732531597215095024301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190753953417592573586731469 71532732531597215095024301)
    ·
      refine ⟨26824774699348955660634113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71532732531597215095024301 26824774699348955660634113)
      ·
        refine ⟨20118581024511716745475585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26824774699348955660634113 20118581024511716745475585)
        ·
          refine ⟨15088935768383787559106689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20118581024511716745475585 15088935768383787559106689)
          ·
            refine ⟨11316701826287840669330017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15088935768383787559106689 11316701826287840669330017)
            ·
              refine ⟨8487526369715880501997513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11316701826287840669330017 8487526369715880501997513)
              ·
                refine ⟨6365644777286910376498135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8487526369715880501997513 6365644777286910376498135)
                ·
                  refine ⟨9548467165930365564747203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6365644777286910376498135 9548467165930365564747203)
                  ·
                    refine ⟨14322700748895548347120805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9548467165930365564747203 14322700748895548347120805)
                    ·
                      refine ⟨2685506390417915315085151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14322700748895548347120805 2685506390417915315085151)
                      ·
                        rfl

theorem cell23_5230005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_5230005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230005 prefixEnd_5230005 := by exact prefixLift 5230005
  have htrace : WordTrace (prefixWord ++ tailWord_5230005) baseStart_5230005 baseEnd_5230005 := by
    simpa [prefixWord, tailWord_5230005, baseEnd_5230005] using wordTrace_append hprefix tailTrace_5230005
  have hstable : (prefixWord ++ tailWord_5230005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230005).length < 2 ^ (prefixWord ++ tailWord_5230005).sum := by decide
  have hdescent : baseEnd_5230005 < baseStart_5230005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230008 : List Nat := [2, 1, 2, 1, 2, 2, 3, 4, 1, 2, 3]
def baseStart_5230008 : Nat := 118140960795 + 5230008 * 2 ^ 59
def prefixEnd_5230008 : Nat := 4983230072969 + 3 ^ 40 * 5230008 * 2
def baseEnd_5230008 : Nat := 2685507930859878803347637

theorem tailTrace_5230008 : CollatzResearch.WordTrace tailWord_5230008 prefixEnd_5230008 2685507930859878803347637 := by
  unfold tailWord_5230008
  simp only [CollatzResearch.WordTrace]
  refine ⟨95377031418290852549545339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127169375224387803399393785 95377031418290852549545339)
  ·
    refine ⟨143065547127436278824318009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95377031418290852549545339 143065547127436278824318009)
    ·
      refine ⟨107299160345577209118238507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143065547127436278824318009 107299160345577209118238507)
      ·
        refine ⟨160948740518365813677357761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107299160345577209118238507 160948740518365813677357761)
        ·
          refine ⟨120711555388774360258018321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160948740518365813677357761 120711555388774360258018321)
          ·
            refine ⟨90533666541580770193513741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120711555388774360258018321 90533666541580770193513741)
            ·
              refine ⟨33950124953092788822567653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90533666541580770193513741 33950124953092788822567653)
              ·
                refine ⟨6365648428704897904231435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33950124953092788822567653 6365648428704897904231435)
                ·
                  refine ⟨9548472643057346856347153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6365648428704897904231435 9548472643057346856347153)
                  ·
                    refine ⟨7161354482293010142260365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9548472643057346856347153 7161354482293010142260365)
                    ·
                      refine ⟨2685507930859878803347637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7161354482293010142260365 2685507930859878803347637)
                      ·
                        rfl

theorem cell23_5230008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 1, 2, 3].length) (baseStart_5230008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230008 prefixEnd_5230008 := by exact prefixLift 5230008
  have htrace : WordTrace (prefixWord ++ tailWord_5230008) baseStart_5230008 baseEnd_5230008 := by
    simpa [prefixWord, tailWord_5230008, baseEnd_5230008] using wordTrace_append hprefix tailTrace_5230008
  have hstable : (prefixWord ++ tailWord_5230008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230008).length < 2 ^ (prefixWord ++ tailWord_5230008).sum := by decide
  have hdescent : baseEnd_5230008 < baseStart_5230008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230065 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 3, 3, 2]
def baseStart_5230065 : Nat := 118140960795 + 5230065 * 2 ^ 59
def prefixEnd_5230065 : Nat := 4983230072969 + 3 ^ 40 * 5230065 * 2
def baseEnd_5230065 : Nat := 2685537199257185080334875

theorem tailTrace_5230065 : CollatzResearch.WordTrace tailWord_5230065 prefixEnd_5230065 2685537199257185080334875 := by
  unfold tailWord_5230065
  simp only [CollatzResearch.WordTrace]
  refine ⟨190756141797375203833915649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127170761198250135889277099 190756141797375203833915649)
  ·
    refine ⟨143067106348031402875436737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190756141797375203833915649 143067106348031402875436737)
    ·
      refine ⟨107300329761023552156577553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143067106348031402875436737 107300329761023552156577553)
      ·
        refine ⟨80475247320767664117433165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107300329761023552156577553 80475247320767664117433165)
        ·
          refine ⟨30178217745287874044037437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80475247320767664117433165 30178217745287874044037437)
          ·
            refine ⟨11316831654482952766514039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30178217745287874044037437 11316831654482952766514039)
            ·
              refine ⟨16975247481724429149771059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11316831654482952766514039 16975247481724429149771059)
              ·
                refine ⟨25462871222586643724656589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16975247481724429149771059 25462871222586643724656589)
                ·
                  refine ⟨9548576708469991396746221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25462871222586643724656589 9548576708469991396746221)
                  ·
                    refine ⟨3580716265676246773779833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9548576708469991396746221 3580716265676246773779833)
                    ·
                      refine ⟨2685537199257185080334875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3580716265676246773779833 2685537199257185080334875)
                      ·
                        rfl

theorem cell23_5230065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 3, 2].length) (baseStart_5230065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230065 prefixEnd_5230065 := by exact prefixLift 5230065
  have htrace : WordTrace (prefixWord ++ tailWord_5230065) baseStart_5230065 baseEnd_5230065 := by
    simpa [prefixWord, tailWord_5230065, baseEnd_5230065] using wordTrace_append hprefix tailTrace_5230065
  have hstable : (prefixWord ++ tailWord_5230065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230065).length < 2 ^ (prefixWord ++ tailWord_5230065).sum := by decide
  have hdescent : baseEnd_5230065 < baseStart_5230065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230108 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_5230108 : Nat := 118140960795 + 5230108 * 2 ^ 59
def prefixEnd_5230108 : Nat := 4983230072969 + 3 ^ 40 * 5230108 * 2
def baseEnd_5230108 : Nat := 2685559278925328412097177

theorem tailTrace_5230108 : CollatzResearch.WordTrace tailWord_5230108 prefixEnd_5230108 2685559278925328412097177 := by
  unfold tailWord_5230108
  simp only [CollatzResearch.WordTrace]
  refine ⟨95378855068109711088865489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127171806757479614785153985 95378855068109711088865489)
  ·
    refine ⟨71534141301082283316649117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95378855068109711088865489 71534141301082283316649117)
    ·
      refine ⟨26825302987905856243743419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71534141301082283316649117 26825302987905856243743419)
      ·
        refine ⟨40237954481858784365615129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26825302987905856243743419 40237954481858784365615129)
        ·
          refine ⟨30178465861394088274211347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40237954481858784365615129 30178465861394088274211347)
          ·
            refine ⟨45267698792091132411317021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30178465861394088274211347 45267698792091132411317021)
            ·
              refine ⟨16975387047034174654243883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45267698792091132411317021 16975387047034174654243883)
              ·
                refine ⟨25463080570551261981365825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16975387047034174654243883 25463080570551261981365825)
                ·
                  refine ⟨19097310427913446486024369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25463080570551261981365825 19097310427913446486024369)
                  ·
                    refine ⟨14322982820935084864518277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19097310427913446486024369 14322982820935084864518277)
                    ·
                      refine ⟨2685559278925328412097177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14322982820935084864518277 2685559278925328412097177)
                      ·
                        rfl

theorem cell23_5230108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_5230108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230108 prefixEnd_5230108 := by exact prefixLift 5230108
  have htrace : WordTrace (prefixWord ++ tailWord_5230108) baseStart_5230108 baseEnd_5230108 := by
    simpa [prefixWord, tailWord_5230108, baseEnd_5230108] using wordTrace_append hprefix tailTrace_5230108
  have hstable : (prefixWord ++ tailWord_5230108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230108).length < 2 ^ (prefixWord ++ tailWord_5230108).sum := by decide
  have hdescent : baseEnd_5230108 < baseStart_5230108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230112 : List Nat := [2, 1, 1, 6, 1, 2, 2, 1, 1, 4, 2]
def baseStart_5230112 : Nat := 118140960795 + 5230112 * 2 ^ 59
def prefixEnd_5230112 : Nat := 4983230072969 + 3 ^ 40 * 5230112 * 2
def baseEnd_5230112 : Nat := 2685561332847946396447159

theorem tailTrace_5230112 : CollatzResearch.WordTrace tailWord_5230112 prefixEnd_5230112 2685561332847946396447159 := by
  unfold tailWord_5230112
  simp only [CollatzResearch.WordTrace]
  refine ⟨95378928014102465430438295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127171904018803287240584393 95378928014102465430438295)
  ·
    refine ⟨143068392021153698145657443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95378928014102465430438295 143068392021153698145657443)
    ·
      refine ⟨214602588031730547218486165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143068392021153698145657443 214602588031730547218486165)
      ·
        refine ⟨10059496313987369400866539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 214602588031730547218486165 10059496313987369400866539)
        ·
          refine ⟨15089244470981054101299809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10059496313987369400866539 15089244470981054101299809)
          ·
            refine ⟨11316933353235790575974857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15089244470981054101299809 11316933353235790575974857)
            ·
              refine ⟨8487700014926842931981143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11316933353235790575974857 8487700014926842931981143)
              ·
                refine ⟨12731550022390264397971715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8487700014926842931981143 12731550022390264397971715)
                ·
                  refine ⟨19097325033585396596957573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12731550022390264397971715 19097325033585396596957573)
                  ·
                    refine ⟨3580748443797261861929545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19097325033585396596957573 3580748443797261861929545)
                    ·
                      refine ⟨2685561332847946396447159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3580748443797261861929545 2685561332847946396447159)
                      ·
                        rfl

theorem cell23_5230112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_5230112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230112 prefixEnd_5230112 := by exact prefixLift 5230112
  have htrace : WordTrace (prefixWord ++ tailWord_5230112) baseStart_5230112 baseEnd_5230112 := by
    simpa [prefixWord, tailWord_5230112, baseEnd_5230112] using wordTrace_append hprefix tailTrace_5230112
  have hstable : (prefixWord ++ tailWord_5230112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230112).length < 2 ^ (prefixWord ++ tailWord_5230112).sum := by decide
  have hdescent : baseEnd_5230112 < baseStart_5230112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230135 : List Nat := [1, 1, 3, 1, 2, 5, 2, 3, 5]
def baseStart_5230135 : Nat := 118140960795 + 5230135 * 2 ^ 59
def prefixEnd_5230135 : Nat := 4983230072969 + 3 ^ 40 * 5230135 * 2
def baseEnd_5230135 : Nat := 298397015878111089606617

theorem tailTrace_5230135 : CollatzResearch.WordTrace tailWord_5230135 prefixEnd_5230135 298397015878111089606617 := by
  unfold tailWord_5230135
  simp only [CollatzResearch.WordTrace]
  refine ⟨190758694907121605788963859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127172463271414403859309239 190758694907121605788963859)
  ·
    refine ⟨286138042360682408683445789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190758694907121605788963859 286138042360682408683445789)
    ·
      refine ⟨107301765885255903256292171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 286138042360682408683445789 107301765885255903256292171)
      ·
        refine ⟨160952648827883854884438257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107301765885255903256292171 160952648827883854884438257)
        ·
          refine ⟨120714486620912891163328693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160952648827883854884438257 120714486620912891163328693)
          ·
            refine ⟨11316983120710583546562065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120714486620912891163328693 11316983120710583546562065)
            ·
              refine ⟨8487737340532937659921549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11316983120710583546562065 8487737340532937659921549)
              ·
                refine ⟨3182901502699851622470581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8487737340532937659921549 3182901502699851622470581)
                ·
                  refine ⟨298397015878111089606617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3182901502699851622470581 298397015878111089606617)
                  ·
                    rfl

theorem cell23_5230135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 5].length) (baseStart_5230135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230135 prefixEnd_5230135 := by exact prefixLift 5230135
  have htrace : WordTrace (prefixWord ++ tailWord_5230135) baseStart_5230135 baseEnd_5230135 := by
    simpa [prefixWord, tailWord_5230135, baseEnd_5230135] using wordTrace_append hprefix tailTrace_5230135
  have hstable : (prefixWord ++ tailWord_5230135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230135).length < 2 ^ (prefixWord ++ tailWord_5230135).sum := by decide
  have hdescent : baseEnd_5230135 < baseStart_5230135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230205 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 4, 2, 3]
def baseStart_5230205 : Nat := 118140960795 + 5230205 * 2 ^ 59
def prefixEnd_5230205 : Nat := 4983230072969 + 3 ^ 40 * 5230205 * 2
def baseEnd_5230205 : Nat := 2685609086548814532584231

theorem tailTrace_5230205 : CollatzResearch.WordTrace tailWord_5230205 prefixEnd_5230205 2685609086548814532584231 := by
  unfold tailWord_5230205
  simp only [CollatzResearch.WordTrace]
  refine ⟨190761248016868007744012069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127174165344578671829341379 190761248016868007744012069)
  ·
    refine ⟨35767734003162751452002263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190761248016868007744012069 35767734003162751452002263)
    ·
      refine ⟨53651601004744127178003395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35767734003162751452002263 53651601004744127178003395)
      ·
        refine ⟨80477401507116190767005093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53651601004744127178003395 80477401507116190767005093)
        ·
          refine ⟨15089512782584285768813455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80477401507116190767005093 15089512782584285768813455)
          ·
            refine ⟨22634269173876428653220183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15089512782584285768813455 22634269173876428653220183)
            ·
              refine ⟨33951403760814642979830275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22634269173876428653220183 33951403760814642979830275)
              ·
                refine ⟨50927105641221964469745413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33951403760814642979830275 50927105641221964469745413)
                ·
                  refine ⟨9548832307729118338077265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50927105641221964469745413 9548832307729118338077265)
                  ·
                    refine ⟨7161624230796838753557949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9548832307729118338077265 7161624230796838753557949)
                    ·
                      refine ⟨2685609086548814532584231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7161624230796838753557949 2685609086548814532584231)
                      ·
                        rfl

theorem cell23_5230205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_5230205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230205 prefixEnd_5230205 := by exact prefixLift 5230205
  have htrace : WordTrace (prefixWord ++ tailWord_5230205) baseStart_5230205 baseEnd_5230205 := by
    simpa [prefixWord, tailWord_5230205, baseEnd_5230205] using wordTrace_append hprefix tailTrace_5230205
  have hstable : (prefixWord ++ tailWord_5230205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230205).length < 2 ^ (prefixWord ++ tailWord_5230205).sum := by decide
  have hdescent : baseEnd_5230205 < baseStart_5230205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230208 : List Nat := [2, 1, 1, 2, 1, 4, 2, 4, 6]
def baseStart_5230208 : Nat := 118140960795 + 5230208 * 2 ^ 59
def prefixEnd_5230208 : Nat := 4983230072969 + 3 ^ 40 * 5230208 * 2
def baseEnd_5230208 : Nat := 298401180776753113427413

theorem tailTrace_5230208 : CollatzResearch.WordTrace tailWord_5230208 prefixEnd_5230208 298401180776753113427413 := by
  unfold tailWord_5230208
  simp only [CollatzResearch.WordTrace]
  refine ⟨95380678717928569628185639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127174238290571426170914185 95380678717928569628185639)
  ·
    refine ⟨143071018076892854442278459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95380678717928569628185639 143071018076892854442278459)
    ·
      refine ⟨214606527115339281663417689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143071018076892854442278459 214606527115339281663417689)
      ·
        refine ⟨160954895336504461247563267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214606527115339281663417689 160954895336504461247563267)
        ·
          refine ⟨241432343004756691871344901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160954895336504461247563267 241432343004756691871344901)
          ·
            refine ⟨45268564313391879725877169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 241432343004756691871344901 45268564313391879725877169)
            ·
              refine ⟨33951423235043909794407877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45268564313391879725877169 33951423235043909794407877)
              ·
                refine ⟨6365891856570733086451477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33951423235043909794407877 6365891856570733086451477)
                ·
                  refine ⟨298401180776753113427413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6365891856570733086451477 298401180776753113427413)
                  ·
                    rfl

theorem cell23_5230208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 6].length) (baseStart_5230208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230208 prefixEnd_5230208 := by exact prefixLift 5230208
  have htrace : WordTrace (prefixWord ++ tailWord_5230208) baseStart_5230208 baseEnd_5230208 := by
    simpa [prefixWord, tailWord_5230208, baseEnd_5230208] using wordTrace_append hprefix tailTrace_5230208
  have hstable : (prefixWord ++ tailWord_5230208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230208).length < 2 ^ (prefixWord ++ tailWord_5230208).sum := by decide
  have hdescent : baseEnd_5230208 < baseStart_5230208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230239 : List Nat := [1, 1, 2, 7, 1, 1, 2, 1, 2, 2, 3]
def baseStart_5230239 : Nat := 118140960795 + 5230239 * 2 ^ 59
def prefixEnd_5230239 : Nat := 4983230072969 + 3 ^ 40 * 5230239 * 2
def baseEnd_5230239 : Nat := 2685626544891067399559075

theorem tailTrace_5230239 : CollatzResearch.WordTrace tailWord_5230239 prefixEnd_5230239 2685626544891067399559075 := by
  unfold tailWord_5230239
  simp only [CollatzResearch.WordTrace]
  refine ⟨190762488098744831550749771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127174992065829887700499847 190762488098744831550749771)
  ·
    refine ⟨286143732148117247326124657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190762488098744831550749771 286143732148117247326124657)
    ·
      refine ⟨214607799111087935494593493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286143732148117247326124657 214607799111087935494593493)
      ·
        refine ⟨5029870291666123488154535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 214607799111087935494593493 5029870291666123488154535)
        ·
          refine ⟨7544805437499185232231803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5029870291666123488154535 7544805437499185232231803)
          ·
            refine ⟨11317208156248777848347705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7544805437499185232231803 11317208156248777848347705)
            ·
              refine ⟨8487906117186583386260779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11317208156248777848347705 8487906117186583386260779)
              ·
                refine ⟨12731859175779875079391169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8487906117186583386260779 12731859175779875079391169)
                ·
                  refine ⟨9548894381834906309543377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12731859175779875079391169 9548894381834906309543377)
                  ·
                    refine ⟨7161670786376179732157533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9548894381834906309543377 7161670786376179732157533)
                    ·
                      refine ⟨2685626544891067399559075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7161670786376179732157533 2685626544891067399559075)
                      ·
                        rfl

theorem cell23_5230239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_5230239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230239 prefixEnd_5230239 := by exact prefixLift 5230239
  have htrace : WordTrace (prefixWord ++ tailWord_5230239) baseStart_5230239 baseEnd_5230239 := by
    simpa [prefixWord, tailWord_5230239, baseEnd_5230239] using wordTrace_append hprefix tailTrace_5230239
  have hstable : (prefixWord ++ tailWord_5230239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230239).length < 2 ^ (prefixWord ++ tailWord_5230239).sum := by decide
  have hdescent : baseEnd_5230239 < baseStart_5230239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230245 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 1, 5, 2]
def baseStart_5230245 : Nat := 118140960795 + 5230245 * 2 ^ 59
def prefixEnd_5230245 : Nat := 4983230072969 + 3 ^ 40 * 5230245 * 2
def baseEnd_5230245 : Nat := 2685629625774994376084047

theorem tailTrace_5230245 : CollatzResearch.WordTrace tailWord_5230245 prefixEnd_5230245 2685629625774994376084047 := by
  unfold tailWord_5230245
  simp only [CollatzResearch.WordTrace]
  refine ⟨190762706936723094575468189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127175137957815396383645459 190762706936723094575468189)
  ·
    refine ⟨71536015101271160465800571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190762706936723094575468189 71536015101271160465800571)
    ·
      refine ⟨107304022651906740698700857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71536015101271160465800571 107304022651906740698700857)
      ·
        refine ⟨80478016988930055524025643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107304022651906740698700857 80478016988930055524025643)
        ·
          refine ⟨120717025483395083286038465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80478016988930055524025643 120717025483395083286038465)
          ·
            refine ⟨90537769112546312464528849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120717025483395083286038465 90537769112546312464528849)
            ·
              refine ⟨67903326834409734348396637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90537769112546312464528849 67903326834409734348396637)
              ·
                refine ⟨25463747562903650380648739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67903326834409734348396637 25463747562903650380648739)
                ·
                  refine ⟨38195621344355475570973109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25463747562903650380648739 38195621344355475570973109)
                  ·
                    refine ⟨3580839501033325834778729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38195621344355475570973109 3580839501033325834778729)
                    ·
                      refine ⟨2685629625774994376084047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3580839501033325834778729 2685629625774994376084047)
                      ·
                        rfl

theorem cell23_5230245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 5, 2].length) (baseStart_5230245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230245 prefixEnd_5230245 := by exact prefixLift 5230245
  have htrace : WordTrace (prefixWord ++ tailWord_5230245) baseStart_5230245 baseEnd_5230245 := by
    simpa [prefixWord, tailWord_5230245, baseEnd_5230245] using wordTrace_append hprefix tailTrace_5230245
  have hstable : (prefixWord ++ tailWord_5230245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230245).length < 2 ^ (prefixWord ++ tailWord_5230245).sum := by decide
  have hdescent : baseEnd_5230245 < baseStart_5230245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230269 : List Nat := [1, 4, 1, 2, 1, 2, 3, 4, 1, 1, 3]
def baseStart_5230269 : Nat := 118140960795 + 5230269 * 2 ^ 59
def prefixEnd_5230269 : Nat := 4983230072969 + 3 ^ 40 * 5230269 * 2
def baseEnd_5230269 : Nat := 2685641949310702282183937

theorem tailTrace_5230269 : CollatzResearch.WordTrace tailWord_5230269 prefixEnd_5230269 2685641949310702282183937 := by
  unfold tailWord_5230269
  simp only [CollatzResearch.WordTrace]
  refine ⟨190763582288636146674341861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127175721525757431116227907 190763582288636146674341861)
  ·
    refine ⟨35768171679119277501439099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190763582288636146674341861 35768171679119277501439099)
    ·
      refine ⟨53652257518678916252158649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35768171679119277501439099 53652257518678916252158649)
      ·
        refine ⟨40239193139009187189118987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53652257518678916252158649 40239193139009187189118987)
        ·
          refine ⟨60358789708513780783678481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40239193139009187189118987 60358789708513780783678481)
          ·
            refine ⟨45269092281385335587758861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60358789708513780783678481 45269092281385335587758861)
            ·
              refine ⟨16975909605519500845409573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45269092281385335587758861 16975909605519500845409573)
              ·
                refine ⟨3182983051034906408514295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16975909605519500845409573 3182983051034906408514295)
                ·
                  refine ⟨4774474576552359612771443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3182983051034906408514295 4774474576552359612771443)
                  ·
                    refine ⟨7161711864828539419157165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4774474576552359612771443 7161711864828539419157165)
                    ·
                      refine ⟨2685641949310702282183937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7161711864828539419157165 2685641949310702282183937)
                      ·
                        rfl

theorem cell23_5230269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_5230269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230269 prefixEnd_5230269 := by exact prefixLift 5230269
  have htrace : WordTrace (prefixWord ++ tailWord_5230269) baseStart_5230269 baseEnd_5230269 := by
    simpa [prefixWord, tailWord_5230269, baseEnd_5230269] using wordTrace_append hprefix tailTrace_5230269
  have hstable : (prefixWord ++ tailWord_5230269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230269).length < 2 ^ (prefixWord ++ tailWord_5230269).sum := by decide
  have hdescent : baseEnd_5230269 < baseStart_5230269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230292 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_5230292 : Nat := 118140960795 + 5230292 * 2 ^ 59
def prefixEnd_5230292 : Nat := 4983230072969 + 3 ^ 40 * 5230292 * 2
def baseEnd_5230292 : Nat := 2685653759365755692196331

theorem tailTrace_5230292 : CollatzResearch.WordTrace tailWord_5230292 prefixEnd_5230292 2685653759365755692196331 := by
  unfold tailWord_5230292
  simp only [CollatzResearch.WordTrace]
  refine ⟨95382210583776410801214565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127176280778368547734952753 95382210583776410801214565)
  ·
    refine ⟨17884164484458077025227731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95382210583776410801214565 17884164484458077025227731)
    ·
      refine ⟨26826246726687115537841597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17884164484458077025227731 26826246726687115537841597)
      ·
        refine ⟨10059842522507668326690599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26826246726687115537841597 10059842522507668326690599)
        ·
          refine ⟨15089763783761502490035899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10059842522507668326690599 15089763783761502490035899)
          ·
            refine ⟨22634645675642253735053849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15089763783761502490035899 22634645675642253735053849)
            ·
              refine ⟨16975984256731690301290387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22634645675642253735053849 16975984256731690301290387)
              ·
                refine ⟨25463976385097535451935581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16975984256731690301290387 25463976385097535451935581)
                ·
                  refine ⟨9548991144411575794475843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25463976385097535451935581 9548991144411575794475843)
                  ·
                    refine ⟨14323486716617363691713765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9548991144411575794475843 14323486716617363691713765)
                    ·
                      refine ⟨2685653759365755692196331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14323486716617363691713765 2685653759365755692196331)
                      ·
                        rfl

theorem cell23_5230292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_5230292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230292 prefixEnd_5230292 := by exact prefixLift 5230292
  have htrace : WordTrace (prefixWord ++ tailWord_5230292) baseStart_5230292 baseEnd_5230292 := by
    simpa [prefixWord, tailWord_5230292, baseEnd_5230292] using wordTrace_append hprefix tailTrace_5230292
  have hstable : (prefixWord ++ tailWord_5230292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230292).length < 2 ^ (prefixWord ++ tailWord_5230292).sum := by decide
  have hdescent : baseEnd_5230292 < baseStart_5230292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230295 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 3]
def baseStart_5230295 : Nat := 118140960795 + 5230295 * 2 ^ 59
def prefixEnd_5230295 : Nat := 4983230072969 + 3 ^ 40 * 5230295 * 2
def baseEnd_5230295 : Nat := 2685655299807719180458817

theorem tailTrace_5230295 : CollatzResearch.WordTrace tailWord_5230295 prefixEnd_5230295 2685655299807719180458817 := by
  unfold tailWord_5230295
  simp only [CollatzResearch.WordTrace]
  refine ⟨190764530586541953114788339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127176353724361302076525559 190764530586541953114788339)
  ·
    refine ⟨286146795879812929672182509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190764530586541953114788339 286146795879812929672182509)
    ·
      refine ⟨107305048454929848627068441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 286146795879812929672182509 107305048454929848627068441)
      ·
        refine ⟨80478786341197386470301331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107305048454929848627068441 80478786341197386470301331)
        ·
          refine ⟨120718179511796079705451997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80478786341197386470301331 120718179511796079705451997)
          ·
            refine ⟨45269317316923529889544499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120718179511796079705451997 45269317316923529889544499)
            ·
              refine ⟨67903975975385294834316749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45269317316923529889544499 67903975975385294834316749)
              ·
                refine ⟨25463990990769485562868781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67903975975385294834316749 25463990990769485562868781)
                ·
                  refine ⟨9548996621538557086075793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25463990990769485562868781 9548996621538557086075793)
                  ·
                    refine ⟨7161747466153917814556845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9548996621538557086075793 7161747466153917814556845)
                    ·
                      refine ⟨2685655299807719180458817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7161747466153917814556845 2685655299807719180458817)
                      ·
                        rfl

theorem cell23_5230295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_5230295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230295 prefixEnd_5230295 := by exact prefixLift 5230295
  have htrace : WordTrace (prefixWord ++ tailWord_5230295) baseStart_5230295 baseEnd_5230295 := by
    simpa [prefixWord, tailWord_5230295, baseEnd_5230295] using wordTrace_append hprefix tailTrace_5230295
  have hstable : (prefixWord ++ tailWord_5230295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230295).length < 2 ^ (prefixWord ++ tailWord_5230295).sum := by decide
  have hdescent : baseEnd_5230295 < baseStart_5230295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230326 : List Nat := [5, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2]
def baseStart_5230326 : Nat := 118140960795 + 5230326 * 2 ^ 59
def prefixEnd_5230326 : Nat := 4983230072969 + 3 ^ 40 * 5230326 * 2
def baseEnd_5230326 : Nat := 2685671217708008559171175

theorem tailTrace_5230326 : CollatzResearch.WordTrace tailWord_5230326 prefixEnd_5230326 2685671217708008559171175 := by
  unfold tailWord_5230326
  simp only [CollatzResearch.WordTrace]
  refine ⟨11922853828089352838072927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127177107499619763606111221 11922853828089352838072927)
  ·
    refine ⟨17884280742134029257109391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11922853828089352838072927 17884280742134029257109391)
    ·
      refine ⟨26826421113201043885664087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17884280742134029257109391 26826421113201043885664087)
      ·
        refine ⟨40239631669801565828496131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26826421113201043885664087 40239631669801565828496131)
        ·
          refine ⟨60359447504702348742744197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40239631669801565828496131 60359447504702348742744197)
          ·
            refine ⟨11317396407131690389264537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60359447504702348742744197 11317396407131690389264537)
            ·
              refine ⟨8488047305348767791948403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11317396407131690389264537 8488047305348767791948403)
              ·
                refine ⟨12732070958023151687922605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8488047305348767791948403 12732070958023151687922605)
                ·
                  refine ⟨4774526609258681882970977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12732070958023151687922605 4774526609258681882970977)
                  ·
                    refine ⟨3580894956944011412228233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4774526609258681882970977 3580894956944011412228233)
                    ·
                      refine ⟨2685671217708008559171175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3580894956944011412228233 2685671217708008559171175)
                      ·
                        rfl

theorem cell23_5230326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_5230326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230326 prefixEnd_5230326 := by exact prefixLift 5230326
  have htrace : WordTrace (prefixWord ++ tailWord_5230326) baseStart_5230326 baseEnd_5230326 := by
    simpa [prefixWord, tailWord_5230326, baseEnd_5230326] using wordTrace_append hprefix tailTrace_5230326
  have hstable : (prefixWord ++ tailWord_5230326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230326).length < 2 ^ (prefixWord ++ tailWord_5230326).sum := by decide
  have hdescent : baseEnd_5230326 < baseStart_5230326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230328 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 2, 7]
def baseStart_5230328 : Nat := 118140960795 + 5230328 * 2 ^ 59
def prefixEnd_5230328 : Nat := 4983230072969 + 3 ^ 40 * 5230328 * 2
def baseEnd_5230328 : Nat := 895224081556439183782055

theorem tailTrace_5230328 : CollatzResearch.WordTrace tailWord_5230328 prefixEnd_5230328 895224081556439183782055 := by
  unfold tailWord_5230328
  simp only [CollatzResearch.WordTrace]
  refine ⟨95382867097711199875369819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127177156130281599833826425 95382867097711199875369819)
  ·
    refine ⟨143074300646566799813054729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95382867097711199875369819 143074300646566799813054729)
    ·
      refine ⟨107305725484925099859791047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143074300646566799813054729 107305725484925099859791047)
      ·
        refine ⟨160958588227387649789686571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107305725484925099859791047 160958588227387649789686571)
        ·
          refine ⟨241437882341081474684529857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160958588227387649789686571 241437882341081474684529857)
          ·
            refine ⟨181078411755811106013397393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241437882341081474684529857 181078411755811106013397393)
            ·
              refine ⟨135808808816858329510048045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181078411755811106013397393 135808808816858329510048045)
              ·
                refine ⟨50928303306321873566268017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135808808816858329510048045 50928303306321873566268017)
                ·
                  refine ⟨38196227479741405174701013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50928303306321873566268017 38196227479741405174701013)
                  ·
                    refine ⟨895224081556439183782055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38196227479741405174701013 895224081556439183782055)
                    ·
                      rfl

theorem cell23_5230328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_5230328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230328 prefixEnd_5230328 := by exact prefixLift 5230328
  have htrace : WordTrace (prefixWord ++ tailWord_5230328) baseStart_5230328 baseEnd_5230328 := by
    simpa [prefixWord, tailWord_5230328, baseEnd_5230328] using wordTrace_append hprefix tailTrace_5230328
  have hstable : (prefixWord ++ tailWord_5230328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230328).length < 2 ^ (prefixWord ++ tailWord_5230328).sum := by decide
  have hdescent : baseEnd_5230328 < baseStart_5230328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230366 : List Nat := [4, 3, 2, 2, 2, 1, 9]
def baseStart_5230366 : Nat := 118140960795 + 5230366 * 2 ^ 59
def prefixEnd_5230366 : Nat := 4983230072969 + 3 ^ 40 * 5230366 * 2
def baseEnd_5230366 : Nat := 33156688357212202502111

theorem tailTrace_5230366 : CollatzResearch.WordTrace tailWord_5230366 prefixEnd_5230366 33156688357212202502111 := by
  unfold tailWord_5230366
  simp only [CollatzResearch.WordTrace]
  refine ⟨23845890021160591530077869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127178080112856488160415301 23845890021160591530077869)
  ·
    refine ⟨8942208757935221823779201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23845890021160591530077869 8942208757935221823779201)
    ·
      refine ⟨6706656568451416367834401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8942208757935221823779201 6706656568451416367834401)
      ·
        refine ⟨5029992426338562275875801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6706656568451416367834401 5029992426338562275875801)
        ·
          refine ⟨3772494319753921706906851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5029992426338562275875801 3772494319753921706906851)
          ·
            refine ⟨5658741479630882560360277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3772494319753921706906851 5658741479630882560360277)
            ·
              refine ⟨33156688357212202502111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5658741479630882560360277 33156688357212202502111)
              ·
                rfl

theorem cell23_5230366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 9].length) (baseStart_5230366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230366 prefixEnd_5230366 := by exact prefixLift 5230366
  have htrace : WordTrace (prefixWord ++ tailWord_5230366) baseStart_5230366 baseEnd_5230366 := by
    simpa [prefixWord, tailWord_5230366, baseEnd_5230366] using wordTrace_append hprefix tailTrace_5230366
  have hstable : (prefixWord ++ tailWord_5230366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230366).length < 2 ^ (prefixWord ++ tailWord_5230366).sum := by decide
  have hdescent : baseEnd_5230366 < baseStart_5230366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230369 : List Nat := [1, 2, 3, 2, 1, 3, 2, 3, 1, 3, 2]
def baseStart_5230369 : Nat := 118140960795 + 5230369 * 2 ^ 59
def prefixEnd_5230369 : Nat := 4983230072969 + 3 ^ 40 * 5230369 * 2
def baseEnd_5230369 : Nat := 2685693297376151890933477

theorem tailTrace_5230369 : CollatzResearch.WordTrace tailWord_5230369 prefixEnd_5230369 2685693297376151890933477 := by
  unfold tailWord_5230369
  simp only [CollatzResearch.WordTrace]
  refine ⟨190767229588273863752982161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127178153058849242501988107 190767229588273863752982161)
  ·
    refine ⟨143075422191205397814736621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190767229588273863752982161 143075422191205397814736621)
    ·
      refine ⟨53653283321702024180526233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143075422191205397814736621 53653283321702024180526233)
      ·
        refine ⟨40239962491276518135394675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53653283321702024180526233 40239962491276518135394675)
        ·
          refine ⟨60359943736914777203092013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40239962491276518135394675 60359943736914777203092013)
          ·
            refine ⟨22634978901343041451159505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60359943736914777203092013 22634978901343041451159505)
            ·
              refine ⟨16976234176007281088369629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22634978901343041451159505 16976234176007281088369629)
              ·
                refine ⟨6366087816002730408138611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16976234176007281088369629 6366087816002730408138611)
                ·
                  refine ⟨9549131724004095612207917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6366087816002730408138611 9549131724004095612207917)
                  ·
                    refine ⟨3580924396501535854577969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9549131724004095612207917 3580924396501535854577969)
                    ·
                      refine ⟨2685693297376151890933477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3580924396501535854577969 2685693297376151890933477)
                      ·
                        rfl

theorem cell23_5230369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_5230369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230369 prefixEnd_5230369 := by exact prefixLift 5230369
  have htrace : WordTrace (prefixWord ++ tailWord_5230369) baseStart_5230369 baseEnd_5230369 := by
    simpa [prefixWord, tailWord_5230369, baseEnd_5230369] using wordTrace_append hprefix tailTrace_5230369
  have hstable : (prefixWord ++ tailWord_5230369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230369).length < 2 ^ (prefixWord ++ tailWord_5230369).sum := by decide
  have hdescent : baseEnd_5230369 < baseStart_5230369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230485 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 1, 3, 6]
def baseStart_5230485 : Nat := 118140960795 + 5230485 * 2 ^ 59
def prefixEnd_5230485 : Nat := 4983230072969 + 3 ^ 40 * 5230485 * 2
def baseEnd_5230485 : Nat := 2685752861132073437082943

theorem tailTrace_5230485 : CollatzResearch.WordTrace tailWord_5230485 prefixEnd_5230485 2685752861132073437082943 := by
  unfold tailWord_5230485
  simp only [CollatzResearch.WordTrace]
  refine ⟨190771460455853615564204909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127180973637235743709469939 190771460455853615564204909)
  ·
    refine ⟨71539297670945105836576841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190771460455853615564204909 71539297670945105836576841)
    ·
      refine ⟨53654473253208829377432631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71539297670945105836576841 53654473253208829377432631)
      ·
        refine ⟨80481709879813244066148947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53654473253208829377432631 80481709879813244066148947)
        ·
          refine ⟨120722564819719866099223421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80481709879813244066148947 120722564819719866099223421)
          ·
            refine ⟨45270961807394949787208783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120722564819719866099223421 45270961807394949787208783)
            ·
              refine ⟨67906442711092424680813175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45270961807394949787208783 67906442711092424680813175)
              ·
                refine ⟨101859664066638637021219763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67906442711092424680813175 101859664066638637021219763)
                ·
                  refine ⟨152789496099957955531829645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101859664066638637021219763 152789496099957955531829645)
                  ·
                    refine ⟨57296061037484233324436117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 152789496099957955531829645 57296061037484233324436117)
                    ·
                      refine ⟨2685752861132073437082943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57296061037484233324436117 2685752861132073437082943)
                      ·
                        rfl

theorem cell23_5230485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_5230485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230485 prefixEnd_5230485 := by exact prefixLift 5230485
  have htrace : WordTrace (prefixWord ++ tailWord_5230485) baseStart_5230485 baseEnd_5230485 := by
    simpa [prefixWord, tailWord_5230485, baseEnd_5230485] using wordTrace_append hprefix tailTrace_5230485
  have hstable : (prefixWord ++ tailWord_5230485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230485).length < 2 ^ (prefixWord ++ tailWord_5230485).sum := by decide
  have hdescent : baseEnd_5230485 < baseStart_5230485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230515 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 6]
def baseStart_5230515 : Nat := 118140960795 + 5230515 * 2 ^ 59
def prefixEnd_5230515 : Nat := 4983230072969 + 3 ^ 40 * 5230515 * 2
def baseEnd_5230515 : Nat := 2685768265551708319707805

theorem tailTrace_5230515 : CollatzResearch.WordTrace tailWord_5230515 prefixEnd_5230515 2685768265551708319707805 := by
  unfold tailWord_5230515
  simp only [CollatzResearch.WordTrace]
  refine ⟨190772554645744930687796999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127181703097163287125197999 190772554645744930687796999)
  ·
    refine ⟨286158831968617396031695499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190772554645744930687796999 286158831968617396031695499)
    ·
      refine ⟨429238247952926094047543249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286158831968617396031695499 429238247952926094047543249)
      ·
        refine ⟨321928685964694570535657437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429238247952926094047543249 321928685964694570535657437)
        ·
          refine ⟨120723257236760463950871539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 321928685964694570535657437 120723257236760463950871539)
          ·
            refine ⟨181084885855140695926307309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120723257236760463950871539 181084885855140695926307309)
            ·
              refine ⟨67906832195677760972365241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181084885855140695926307309 67906832195677760972365241)
              ·
                refine ⟨50930124146758320729273931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67906832195677760972365241 50930124146758320729273931)
                ·
                  refine ⟨76395186220137481093910897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50930124146758320729273931 76395186220137481093910897)
                  ·
                    refine ⟨57296389665103110820433173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76395186220137481093910897 57296389665103110820433173)
                    ·
                      refine ⟨2685768265551708319707805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57296389665103110820433173 2685768265551708319707805)
                      ·
                        rfl

theorem cell23_5230515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_5230515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230515 prefixEnd_5230515 := by exact prefixLift 5230515
  have htrace : WordTrace (prefixWord ++ tailWord_5230515) baseStart_5230515 baseEnd_5230515 := by
    simpa [prefixWord, tailWord_5230515, baseEnd_5230515] using wordTrace_append hprefix tailTrace_5230515
  have hstable : (prefixWord ++ tailWord_5230515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230515).length < 2 ^ (prefixWord ++ tailWord_5230515).sum := by decide
  have hdescent : baseEnd_5230515 < baseStart_5230515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230550 : List Nat := [5, 2, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_5230550 : Nat := 118140960795 + 5230550 * 2 ^ 59
def prefixEnd_5230550 : Nat := 4983230072969 + 3 ^ 40 * 5230550 * 2
def baseEnd_5230550 : Nat := 895262079124871894256715

theorem tailTrace_5230550 : CollatzResearch.WordTrace tailWord_5230550 prefixEnd_5230550 895262079124871894256715 := by
  unfold tailWord_5230550
  simp only [CollatzResearch.WordTrace]
  refine ⟨11923364450038633229082569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127182554133745421110214069 11923364450038633229082569)
  ·
    refine ⟨8942523337528974921811927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11923364450038633229082569 8942523337528974921811927)
    ·
      refine ⟨13413785006293462382717891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8942523337528974921811927 13413785006293462382717891)
      ·
        refine ⟨20120677509440193574076837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13413785006293462382717891 20120677509440193574076837)
        ·
          refine ⟨3772627033020036295139407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20120677509440193574076837 3772627033020036295139407)
          ·
            refine ⟨5658940549530054442709111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3772627033020036295139407 5658940549530054442709111)
            ·
              refine ⟨8488410824295081664063667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5658940549530054442709111 8488410824295081664063667)
              ·
                refine ⟨12732616236442622496095501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8488410824295081664063667 12732616236442622496095501)
                ·
                  refine ⟨4774731088665983436035813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12732616236442622496095501 4774731088665983436035813)
                  ·
                    refine ⟨895262079124871894256715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4774731088665983436035813 895262079124871894256715)
                    ·
                      rfl

theorem cell23_5230550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_5230550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230550 prefixEnd_5230550 := by exact prefixLift 5230550
  have htrace : WordTrace (prefixWord ++ tailWord_5230550) baseStart_5230550 baseEnd_5230550 := by
    simpa [prefixWord, tailWord_5230550, baseEnd_5230550] using wordTrace_append hprefix tailTrace_5230550
  have hstable : (prefixWord ++ tailWord_5230550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230550).length < 2 ^ (prefixWord ++ tailWord_5230550).sum := by decide
  have hdescent : baseEnd_5230550 < baseStart_5230550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230599 : List Nat := [1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 5]
def baseStart_5230599 : Nat := 118140960795 + 5230599 * 2 ^ 59
def prefixEnd_5230599 : Nat := 4983230072969 + 3 ^ 40 * 5230599 * 2
def baseEnd_5230599 : Nat := 2685811397926685991057419

theorem tailTrace_5230599 : CollatzResearch.WordTrace tailWord_5230599 prefixEnd_5230599 2685811397926685991057419 := by
  unfold tailWord_5230599
  simp only [CollatzResearch.WordTrace]
  refine ⟨190775618377440613033854851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127183745584960408689236567 190775618377440613033854851)
  ·
    refine ⟨286163427566160919550782277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190775618377440613033854851 286163427566160919550782277)
    ·
      refine ⟨53655642668655172415771677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 286163427566160919550782277 53655642668655172415771677)
      ·
        refine ⟨20120866000745689655914379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53655642668655172415771677 20120866000745689655914379)
        ·
          refine ⟨30181299001118534483871569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20120866000745689655914379 30181299001118534483871569)
          ·
            refine ⟨22635974250838900862903677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30181299001118534483871569 22635974250838900862903677)
            ·
              refine ⟨8488490344064587823588879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22635974250838900862903677 8488490344064587823588879)
              ·
                refine ⟨12732735516096881735383319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8488490344064587823588879 12732735516096881735383319)
                ·
                  refine ⟨19099103274145322603074979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12732735516096881735383319 19099103274145322603074979)
                  ·
                    refine ⟨28648654911217983904612469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19099103274145322603074979 28648654911217983904612469)
                    ·
                      refine ⟨2685811397926685991057419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28648654911217983904612469 2685811397926685991057419)
                      ·
                        rfl

theorem cell23_5230599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_5230599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230599 prefixEnd_5230599 := by exact prefixLift 5230599
  have htrace : WordTrace (prefixWord ++ tailWord_5230599) baseStart_5230599 baseEnd_5230599 := by
    simpa [prefixWord, tailWord_5230599, baseEnd_5230599] using wordTrace_append hprefix tailTrace_5230599
  have hstable : (prefixWord ++ tailWord_5230599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230599).length < 2 ^ (prefixWord ++ tailWord_5230599).sum := by decide
  have hdescent : baseEnd_5230599 < baseStart_5230599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230602 : List Nat := [3, 1, 2, 2, 4, 11]
def baseStart_5230602 : Nat := 118140960795 + 5230602 * 2 ^ 59
def prefixEnd_5230602 : Nat := 4983230072969 + 3 ^ 40 * 5230602 * 2
def baseEnd_5230602 : Nat := 11052728141434771519835

theorem tailTrace_5230602 : CollatzResearch.WordTrace tailWord_5230602 prefixEnd_5230602 11052728141434771519835 := by
  unfold tailWord_5230602
  simp only [CollatzResearch.WordTrace]
  refine ⟨47693931949107436136553515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127183818530953163030809373 47693931949107436136553515)
  ·
    refine ⟨71540897923661154204830273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47693931949107436136553515 71540897923661154204830273)
    ·
      refine ⟨53655673442745865653622705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71540897923661154204830273 53655673442745865653622705)
      ·
        refine ⟨40241755082059399240217029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53655673442745865653622705 40241755082059399240217029)
        ·
          refine ⟨7545329077886137357540693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40241755082059399240217029 7545329077886137357540693)
          ·
            refine ⟨11052728141434771519835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7545329077886137357540693 11052728141434771519835)
            ·
              rfl

theorem cell23_5230602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 11].length) (baseStart_5230602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230602 prefixEnd_5230602 := by exact prefixLift 5230602
  have htrace : WordTrace (prefixWord ++ tailWord_5230602) baseStart_5230602 baseEnd_5230602 := by
    simpa [prefixWord, tailWord_5230602, baseEnd_5230602] using wordTrace_append hprefix tailTrace_5230602
  have hstable : (prefixWord ++ tailWord_5230602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230602).length < 2 ^ (prefixWord ++ tailWord_5230602).sum := by decide
  have hdescent : baseEnd_5230602 < baseStart_5230602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230606 : List Nat := [4, 1, 1, 2, 2, 1, 4, 2, 2, 4]
def baseStart_5230606 : Nat := 118140960795 + 5230606 * 2 ^ 59
def prefixEnd_5230606 : Nat := 4983230072969 + 3 ^ 40 * 5230606 * 2
def baseEnd_5230606 : Nat := 895271664097089154556629

theorem tailTrace_5230606 : CollatzResearch.WordTrace tailWord_5230606 prefixEnd_5230606 895271664097089154556629 := by
  unfold tailWord_5230606
  simp only [CollatzResearch.WordTrace]
  refine ⟨23846984211051906653669959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127183915792276835486239781 23846984211051906653669959)
  ·
    refine ⟨35770476316577859980504939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23846984211051906653669959 35770476316577859980504939)
    ·
      refine ⟨53655714474866789970757409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35770476316577859980504939 53655714474866789970757409)
      ·
        refine ⟨40241785856150092478068057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53655714474866789970757409 40241785856150092478068057)
        ·
          refine ⟨30181339392112569358551043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40241785856150092478068057 30181339392112569358551043)
          ·
            refine ⟨45272009088168854037826565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30181339392112569358551043 45272009088168854037826565)
            ·
              refine ⟨8488501704031660132092481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45272009088168854037826565 8488501704031660132092481)
              ·
                refine ⟨6366376278023745099069361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8488501704031660132092481 6366376278023745099069361)
                ·
                  refine ⟨4774782208517808824302021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6366376278023745099069361 4774782208517808824302021)
                  ·
                    refine ⟨895271664097089154556629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4774782208517808824302021 895271664097089154556629)
                    ·
                      rfl

theorem cell23_5230606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_5230606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230606 prefixEnd_5230606 := by exact prefixLift 5230606
  have htrace : WordTrace (prefixWord ++ tailWord_5230606) baseStart_5230606 baseEnd_5230606 := by
    simpa [prefixWord, tailWord_5230606, baseEnd_5230606] using wordTrace_append hprefix tailTrace_5230606
  have hstable : (prefixWord ++ tailWord_5230606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230606).length < 2 ^ (prefixWord ++ tailWord_5230606).sum := by decide
  have hdescent : baseEnd_5230606 < baseStart_5230606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230629 : List Nat := [1, 3, 1, 2, 2, 3, 1, 3, 1, 3, 3]
def baseStart_5230629 : Nat := 118140960795 + 5230629 * 2 ^ 59
def prefixEnd_5230629 : Nat := 4983230072969 + 3 ^ 40 * 5230629 * 2
def baseEnd_5230629 : Nat := 2685826802346320873682281

theorem tailTrace_5230629 : CollatzResearch.WordTrace tailWord_5230629 prefixEnd_5230629 2685826802346320873682281 := by
  unfold tailWord_5230629
  simp only [CollatzResearch.WordTrace]
  refine ⟨190776712567331928157446941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127184475044887952104964627 190776712567331928157446941)
  ·
    refine ⟨71541267212749473059042603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190776712567331928157446941 71541267212749473059042603)
    ·
      refine ⟨107311900819124209588563905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71541267212749473059042603 107311900819124209588563905)
      ·
        refine ⟨80483925614343157191422929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107311900819124209588563905 80483925614343157191422929)
        ·
          refine ⟨60362944210757367893567197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80483925614343157191422929 60362944210757367893567197)
          ·
            refine ⟨22636104079034012960087699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60362944210757367893567197 22636104079034012960087699)
            ·
              refine ⟨33954156118551019440131549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22636104079034012960087699 33954156118551019440131549)
              ·
                refine ⟨12732808544456632290049331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33954156118551019440131549 12732808544456632290049331)
                ·
                  refine ⟨19099212816684948435073997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12732808544456632290049331 19099212816684948435073997)
                  ·
                    refine ⟨7162204806256855663152749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19099212816684948435073997 7162204806256855663152749)
                    ·
                      refine ⟨2685826802346320873682281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7162204806256855663152749 2685826802346320873682281)
                      ·
                        rfl

theorem cell23_5230629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_5230629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230629 prefixEnd_5230629 := by exact prefixLift 5230629
  have htrace : WordTrace (prefixWord ++ tailWord_5230629) baseStart_5230629 baseEnd_5230629 := by
    simpa [prefixWord, tailWord_5230629, baseEnd_5230629] using wordTrace_append hprefix tailTrace_5230629
  have hstable : (prefixWord ++ tailWord_5230629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230629).length < 2 ^ (prefixWord ++ tailWord_5230629).sum := by decide
  have hdescent : baseEnd_5230629 < baseStart_5230629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230646 : List Nat := [5, 1, 2, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_5230646 : Nat := 118140960795 + 5230646 * 2 ^ 59
def prefixEnd_5230646 : Nat := 4983230072969 + 3 ^ 40 * 5230646 * 2
def baseEnd_5230646 : Nat := 2685835531517447307169703

theorem tailTrace_5230646 : CollatzResearch.WordTrace tailWord_5230646 prefixEnd_5230646 2685835531517447307169703 := by
  unfold tailWord_5230646
  simp only [CollatzResearch.WordTrace]
  refine ⟨11923583288016896253800987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127184888405513560040543861 11923583288016896253800987)
  ·
    refine ⟨17885374932025344380701481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11923583288016896253800987 17885374932025344380701481)
    ·
      refine ⟨13414031199019008285526111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17885374932025344380701481 13414031199019008285526111)
      ·
        refine ⟨20121046798528512428289167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13414031199019008285526111 20121046798528512428289167)
        ·
          refine ⟨30181570197792768642433751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20121046798528512428289167 30181570197792768642433751)
          ·
            refine ⟨45272355296689152963650627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30181570197792768642433751 45272355296689152963650627)
            ·
              refine ⟨67908532945033729445475941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45272355296689152963650627 67908532945033729445475941)
              ·
                refine ⟨12732849927193824271026739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67908532945033729445475941 12732849927193824271026739)
                ·
                  refine ⟨19099274890790736406540109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12732849927193824271026739 19099274890790736406540109)
                  ·
                    refine ⟨7162228084046526152452541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19099274890790736406540109 7162228084046526152452541)
                    ·
                      refine ⟨2685835531517447307169703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7162228084046526152452541 2685835531517447307169703)
                      ·
                        rfl

theorem cell23_5230646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_5230646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230646 prefixEnd_5230646 := by exact prefixLift 5230646
  have htrace : WordTrace (prefixWord ++ tailWord_5230646) baseStart_5230646 baseEnd_5230646 := by
    simpa [prefixWord, tailWord_5230646, baseEnd_5230646] using wordTrace_append hprefix tailTrace_5230646
  have hstable : (prefixWord ++ tailWord_5230646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230646).length < 2 ^ (prefixWord ++ tailWord_5230646).sum := by decide
  have hdescent : baseEnd_5230646 < baseStart_5230646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230672 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 5]
def baseStart_5230672 : Nat := 118140960795 + 5230672 * 2 ^ 59
def prefixEnd_5230672 : Nat := 4983230072969 + 3 ^ 40 * 5230672 * 2
def baseEnd_5230672 : Nat := 2685848882014464205444583

theorem tailTrace_5230672 : CollatzResearch.WordTrace tailWord_5230672 prefixEnd_5230672 2685848882014464205444583 := by
  unfold tailWord_5230672
  simp only [CollatzResearch.WordTrace]
  refine ⟨95389140453088073250631135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127185520604117431000841513 95389140453088073250631135)
  ·
    refine ⟨143083710679632109875946703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95389140453088073250631135 143083710679632109875946703)
    ·
      refine ⟨214625566019448164813920055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143083710679632109875946703 214625566019448164813920055)
      ·
        refine ⟨321938349029172247220880083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214625566019448164813920055 321938349029172247220880083)
        ·
          refine ⟨482907523543758370831320125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321938349029172247220880083 482907523543758370831320125)
          ·
            refine ⟨181090321328909389061745047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 482907523543758370831320125 181090321328909389061745047)
            ·
              refine ⟨271635481993364083592617571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181090321328909389061745047 271635481993364083592617571)
              ·
                refine ⟨407453222990046125388926357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271635481993364083592617571 407453222990046125388926357)
                ·
                  refine ⟨19099369827658412127605923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 407453222990046125388926357 19099369827658412127605923)
                  ·
                    refine ⟨28649054741487618191408885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19099369827658412127605923 28649054741487618191408885)
                    ·
                      refine ⟨2685848882014464205444583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28649054741487618191408885 2685848882014464205444583)
                      ·
                        rfl

theorem cell23_5230672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 5].length) (baseStart_5230672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230672 prefixEnd_5230672 := by exact prefixLift 5230672
  have htrace : WordTrace (prefixWord ++ tailWord_5230672) baseStart_5230672 baseEnd_5230672 := by
    simpa [prefixWord, tailWord_5230672, baseEnd_5230672] using wordTrace_append hprefix tailTrace_5230672
  have hstable : (prefixWord ++ tailWord_5230672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230672).length < 2 ^ (prefixWord ++ tailWord_5230672).sum := by decide
  have hdescent : baseEnd_5230672 < baseStart_5230672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230776 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 2, 4, 2]
def baseStart_5230776 : Nat := 118140960795 + 5230776 * 2 ^ 59
def prefixEnd_5230776 : Nat := 4983230072969 + 3 ^ 40 * 5230776 * 2
def baseEnd_5230776 : Nat := 2685902284002531798544105

theorem tailTrace_5230776 : CollatzResearch.WordTrace tailWord_5230776 prefixEnd_5230776 2685902284002531798544105 := by
  unfold tailWord_5230776
  simp only [CollatzResearch.WordTrace]
  refine ⟨95391037048899686131524091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127188049398532914842032121 95391037048899686131524091)
  ·
    refine ⟨143086555573349529197286137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95391037048899686131524091 143086555573349529197286137)
    ·
      refine ⟨107314916680012146897964603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143086555573349529197286137 107314916680012146897964603)
      ·
        refine ⟨160972375020018220346946905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107314916680012146897964603 160972375020018220346946905)
        ·
          refine ⟨120729281265013665260210179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160972375020018220346946905 120729281265013665260210179)
          ·
            refine ⟨181093921897520497890315269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120729281265013665260210179 181093921897520497890315269)
            ·
              refine ⟨33955110355785093354434113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 181093921897520497890315269 33955110355785093354434113)
              ·
                refine ⟨25466332766838820015825585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33955110355785093354434113 25466332766838820015825585)
                ·
                  refine ⟨19099749575129115011869189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25466332766838820015825585 19099749575129115011869189)
                  ·
                    refine ⟨3581203045336709064725473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19099749575129115011869189 3581203045336709064725473)
                    ·
                      refine ⟨2685902284002531798544105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3581203045336709064725473 2685902284002531798544105)
                      ·
                        rfl

theorem cell23_5230776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 2, 4, 2].length) (baseStart_5230776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230776 prefixEnd_5230776 := by exact prefixLift 5230776
  have htrace : WordTrace (prefixWord ++ tailWord_5230776) baseStart_5230776 baseEnd_5230776 := by
    simpa [prefixWord, tailWord_5230776, baseEnd_5230776] using wordTrace_append hprefix tailTrace_5230776
  have hstable : (prefixWord ++ tailWord_5230776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230776).length < 2 ^ (prefixWord ++ tailWord_5230776).sum := by decide
  have hdescent : baseEnd_5230776 < baseStart_5230776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230799 : List Nat := [1, 1, 2, 1, 1, 3, 3, 5, 6]
def baseStart_5230799 : Nat := 118140960795 + 5230799 * 2 ^ 59
def prefixEnd_5230799 : Nat := 4983230072969 + 3 ^ 40 * 5230799 * 2
def baseEnd_5230799 : Nat := 298434899339731689839611

theorem tailTrace_5230799 : CollatzResearch.WordTrace tailWord_5230799 prefixEnd_5230799 298434899339731689839611 := by
  unfold tailWord_5230799
  simp only [CollatzResearch.WordTrace]
  refine ⟨190782912976716047191135451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127188608651144031460756967 190782912976716047191135451)
  ·
    refine ⟨286174369465074070786703177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190782912976716047191135451 286174369465074070786703177)
    ·
      refine ⟨214630777098805553090027383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286174369465074070786703177 214630777098805553090027383)
      ·
        refine ⟨321946165648208329635041075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214630777098805553090027383 321946165648208329635041075)
        ·
          refine ⟨482919248472312494452561613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321946165648208329635041075 482919248472312494452561613)
          ·
            refine ⟨181094718177117185419710605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 482919248472312494452561613 181094718177117185419710605)
            ·
              refine ⟨67910519316418944532391477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181094718177117185419710605 67910519316418944532391477)
              ·
                refine ⟨6366611185914276049911701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67910519316418944532391477 6366611185914276049911701)
                ·
                  refine ⟨298434899339731689839611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6366611185914276049911701 298434899339731689839611)
                  ·
                    rfl

theorem cell23_5230799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 6].length) (baseStart_5230799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230799 prefixEnd_5230799 := by exact prefixLift 5230799
  have htrace : WordTrace (prefixWord ++ tailWord_5230799) baseStart_5230799 baseEnd_5230799 := by
    simpa [prefixWord, tailWord_5230799, baseEnd_5230799] using wordTrace_append hprefix tailTrace_5230799
  have hstable : (prefixWord ++ tailWord_5230799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230799).length < 2 ^ (prefixWord ++ tailWord_5230799).sum := by decide
  have hdescent : baseEnd_5230799 < baseStart_5230799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230813 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_5230813 : Nat := 118140960795 + 5230813 * 2 ^ 59
def prefixEnd_5230813 : Nat := 4983230072969 + 3 ^ 40 * 5230813 * 2
def baseEnd_5230813 : Nat := 2685921282786748153781435

theorem tailTrace_5230813 : CollatzResearch.WordTrace tailWord_5230813 prefixEnd_5230813 2685921282786748153781435 := by
  unfold tailWord_5230813
  simp only [CollatzResearch.WordTrace]
  refine ⟨190783423598665327582145093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127188949065776885054763395 190783423598665327582145093)
  ·
    refine ⟨35771891924749748921652205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190783423598665327582145093 35771891924749748921652205)
    ·
      refine ⟨13414459471781155845619577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35771891924749748921652205 13414459471781155845619577)
      ·
        refine ⟨10060844603835866884214683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13414459471781155845619577 10060844603835866884214683)
        ·
          refine ⟨15091266905753800326322025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10060844603835866884214683 15091266905753800326322025)
          ·
            refine ⟨11318450179315350244741519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15091266905753800326322025 11318450179315350244741519)
            ·
              refine ⟨16977675268973025367112279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11318450179315350244741519 16977675268973025367112279)
              ·
                refine ⟨25466512903459538050668419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16977675268973025367112279 25466512903459538050668419)
                ·
                  refine ⟨38199769355189307076002629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25466512903459538050668419 38199769355189307076002629)
                  ·
                    refine ⟨7162456754097995076750493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38199769355189307076002629 7162456754097995076750493)
                    ·
                      refine ⟨2685921282786748153781435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7162456754097995076750493 2685921282786748153781435)
                      ·
                        rfl

theorem cell23_5230813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_5230813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230813 prefixEnd_5230813 := by exact prefixLift 5230813
  have htrace : WordTrace (prefixWord ++ tailWord_5230813) baseStart_5230813 baseEnd_5230813 := by
    simpa [prefixWord, tailWord_5230813, baseEnd_5230813] using wordTrace_append hprefix tailTrace_5230813
  have hstable : (prefixWord ++ tailWord_5230813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230813).length < 2 ^ (prefixWord ++ tailWord_5230813).sum := by decide
  have hdescent : baseEnd_5230813 < baseStart_5230813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230850 : List Nat := [3, 4, 1, 1, 2, 2, 3, 1, 6]
def baseStart_5230850 : Nat := 118140960795 + 5230850 * 2 ^ 59
def prefixEnd_5230850 : Nat := 4983230072969 + 3 ^ 40 * 5230850 * 2
def baseEnd_5230850 : Nat := 298437809063440501002085

theorem tailTrace_5230850 : CollatzResearch.WordTrace tailWord_5230850 prefixEnd_5230850 298437809063440501002085 := by
  unfold tailWord_5230850
  simp only [CollatzResearch.WordTrace]
  refine ⟨47696193274882820725310501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127189848733020855267494669 47696193274882820725310501)
  ·
    refine ⟨8943036239040528885995719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47696193274882820725310501 8943036239040528885995719)
    ·
      refine ⟨13414554358560793328993579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8943036239040528885995719 13414554358560793328993579)
      ·
        refine ⟨20121831537841189993490369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13414554358560793328993579 20121831537841189993490369)
        ·
          refine ⟨15091373653380892495117777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20121831537841189993490369 15091373653380892495117777)
          ·
            refine ⟨11318530240035669371338333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15091373653380892495117777 11318530240035669371338333)
            ·
              refine ⟨4244448840013376014251875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11318530240035669371338333 4244448840013376014251875)
              ·
                refine ⟨6366673260020064021377813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4244448840013376014251875 6366673260020064021377813)
                ·
                  refine ⟨298437809063440501002085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6366673260020064021377813 298437809063440501002085)
                  ·
                    rfl

theorem cell23_5230850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_5230850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230850 prefixEnd_5230850 := by exact prefixLift 5230850
  have htrace : WordTrace (prefixWord ++ tailWord_5230850) baseStart_5230850 baseEnd_5230850 := by
    simpa [prefixWord, tailWord_5230850, baseEnd_5230850] using wordTrace_append hprefix tailTrace_5230850
  have hstable : (prefixWord ++ tailWord_5230850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230850).length < 2 ^ (prefixWord ++ tailWord_5230850).sum := by decide
  have hdescent : baseEnd_5230850 < baseStart_5230850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230894 : List Nat := [4, 1, 3, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_5230894 : Nat := 118140960795 + 5230894 * 2 ^ 59
def prefixEnd_5230894 : Nat := 4983230072969 + 3 ^ 40 * 5230894 * 2
def baseEnd_5230894 : Nat := 2685962874719762336868563

theorem tailTrace_5230894 : CollatzResearch.WordTrace tailWord_5230894 prefixEnd_5230894 2685962874719762336868563 := by
  unfold tailWord_5230894
  simp only [CollatzResearch.WordTrace]
  refine ⟨23848297238921484801980467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127190918607581252277229157 23848297238921484801980467)
  ·
    refine ⟨35772445858382227202970701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23848297238921484801980467 35772445858382227202970701)
    ·
      refine ⟨13414667196893335201114013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35772445858382227202970701 13414667196893335201114013)
      ·
        refine ⟨5030500198835000700417755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13414667196893335201114013 5030500198835000700417755)
        ·
          refine ⟨7545750298252501050626633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5030500198835000700417755 7545750298252501050626633)
          ·
            refine ⟨5659312723689375787969975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7545750298252501050626633 5659312723689375787969975)
            ·
              refine ⟨8488969085534063681954963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5659312723689375787969975 8488969085534063681954963)
              ·
                refine ⟨12733453628301095522932445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8488969085534063681954963 12733453628301095522932445)
                ·
                  refine ⟨4775045110612910821099667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12733453628301095522932445 4775045110612910821099667)
                  ·
                    refine ⟨7162567665919366231649501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4775045110612910821099667 7162567665919366231649501)
                    ·
                      refine ⟨2685962874719762336868563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7162567665919366231649501 2685962874719762336868563)
                      ·
                        rfl

theorem cell23_5230894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_5230894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230894 prefixEnd_5230894 := by exact prefixLift 5230894
  have htrace : WordTrace (prefixWord ++ tailWord_5230894) baseStart_5230894 baseEnd_5230894 := by
    simpa [prefixWord, tailWord_5230894, baseEnd_5230894] using wordTrace_append hprefix tailTrace_5230894
  have hstable : (prefixWord ++ tailWord_5230894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230894).length < 2 ^ (prefixWord ++ tailWord_5230894).sum := by decide
  have hdescent : baseEnd_5230894 < baseStart_5230894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230906 : List Nat := [3, 1, 1, 1, 4, 3, 2, 8]
def baseStart_5230906 : Nat := 118140960795 + 5230906 * 2 ^ 59
def prefixEnd_5230906 : Nat := 4983230072969 + 3 ^ 40 * 5230906 * 2
def baseEnd_5230906 : Nat := 99480334684726529256241

theorem tailTrace_5230906 : CollatzResearch.WordTrace tailWord_5230906 prefixEnd_5230906 99480334684726529256241 := by
  unfold tailWord_5230906
  simp only [CollatzResearch.WordTrace]
  refine ⟨47696703896832101116320143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127191210391552269643520381 47696703896832101116320143)
  ·
    refine ⟨71545055845248151674480215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47696703896832101116320143 71545055845248151674480215)
    ·
      refine ⟨107317583767872227511720323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71545055845248151674480215 107317583767872227511720323)
      ·
        refine ⟨160976375651808341267580485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107317583767872227511720323 160976375651808341267580485)
        ·
          refine ⟨30183070434714063987671341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160976375651808341267580485 30183070434714063987671341)
          ·
            refine ⟨11318651413017773995376753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30183070434714063987671341 11318651413017773995376753)
            ·
              refine ⟨8488988559763330496532565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11318651413017773995376753 8488988559763330496532565)
              ·
                refine ⟨99480334684726529256241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8488988559763330496532565 99480334684726529256241)
                ·
                  rfl

theorem cell23_5230906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 8].length) (baseStart_5230906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230906 prefixEnd_5230906 := by exact prefixLift 5230906
  have htrace : WordTrace (prefixWord ++ tailWord_5230906) baseStart_5230906 baseEnd_5230906 := by
    simpa [prefixWord, tailWord_5230906, baseEnd_5230906] using wordTrace_append hprefix tailTrace_5230906
  have hstable : (prefixWord ++ tailWord_5230906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230906).length < 2 ^ (prefixWord ++ tailWord_5230906).sum := by decide
  have hdescent : baseEnd_5230906 < baseStart_5230906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230910 : List Nat := [4, 2, 1, 2, 1, 3, 1, 3, 2, 4]
def baseStart_5230910 : Nat := 118140960795 + 5230910 * 2 ^ 59
def prefixEnd_5230910 : Nat := 4983230072969 + 3 ^ 40 * 5230910 * 2
def baseEnd_5230910 : Nat := 895323696803411424756163

theorem tailTrace_5230910 : CollatzResearch.WordTrace tailWord_5230910 prefixEnd_5230910 895323696803411424756163 := by
  unfold tailWord_5230910
  simp only [CollatzResearch.WordTrace]
  refine ⟨23848370184914239143553273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127191307652875942098950789 23848370184914239143553273)
  ·
    refine ⟨17886277638685679357664955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23848370184914239143553273 17886277638685679357664955)
    ·
      refine ⟨26829416458028519036497433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17886277638685679357664955 26829416458028519036497433)
      ·
        refine ⟨20122062343521389277373075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26829416458028519036497433 20122062343521389277373075)
        ·
          refine ⟨30183093515282083916059613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20122062343521389277373075 30183093515282083916059613)
          ·
            refine ⟨11318660068230781468522355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30183093515282083916059613 11318660068230781468522355)
            ·
              refine ⟨16977990102346172202783533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11318660068230781468522355 16977990102346172202783533)
              ·
                refine ⟨6366746288379814576043825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16977990102346172202783533 6366746288379814576043825)
                ·
                  refine ⟨4775059716284860932032869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6366746288379814576043825 4775059716284860932032869)
                  ·
                    refine ⟨895323696803411424756163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4775059716284860932032869 895323696803411424756163)
                    ·
                      rfl

theorem cell23_5230910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_5230910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230910 prefixEnd_5230910 := by exact prefixLift 5230910
  have htrace : WordTrace (prefixWord ++ tailWord_5230910) baseStart_5230910 baseEnd_5230910 := by
    simpa [prefixWord, tailWord_5230910, baseEnd_5230910] using wordTrace_append hprefix tailTrace_5230910
  have hstable : (prefixWord ++ tailWord_5230910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230910).length < 2 ^ (prefixWord ++ tailWord_5230910).sum := by decide
  have hdescent : baseEnd_5230910 < baseStart_5230910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5230951 : List Nat := [1, 1, 5, 1, 3, 3, 2, 2, 1, 2, 2]
def baseStart_5230951 : Nat := 118140960795 + 5230951 * 2 ^ 59
def prefixEnd_5230951 : Nat := 4983230072969 + 3 ^ 40 * 5230951 * 2
def baseEnd_5230951 : Nat := 2685992143117068613855801

theorem tailTrace_5230951 : CollatzResearch.WordTrace tailWord_5230951 prefixEnd_5230951 2685992143117068613855801 := by
  unfold tailWord_5230951
  simp only [CollatzResearch.WordTrace]
  refine ⟨190788456872165377150668707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127192304581443584767112471 190788456872165377150668707)
  ·
    refine ⟨286182685308248065726003061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190788456872165377150668707 286182685308248065726003061)
    ·
      refine ⟨26829626747648256161812787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 286182685308248065726003061 26829626747648256161812787)
      ·
        refine ⟨40244440121472384242719181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26829626747648256161812787 40244440121472384242719181)
        ·
          refine ⟨15091665045552144091019693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40244440121472384242719181 15091665045552144091019693)
          ·
            refine ⟨5659374392082054034132385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15091665045552144091019693 5659374392082054034132385)
            ·
              refine ⟨4244530794061540525599289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5659374392082054034132385 4244530794061540525599289)
              ·
                refine ⟨3183398095546155394199467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4244530794061540525599289 3183398095546155394199467)
                ·
                  refine ⟨4775097143319233091299201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3183398095546155394199467 4775097143319233091299201)
                  ·
                    refine ⟨3581322857489424818474401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4775097143319233091299201 3581322857489424818474401)
                    ·
                      refine ⟨2685992143117068613855801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3581322857489424818474401 2685992143117068613855801)
                      ·
                        rfl

theorem cell23_5230951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_5230951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5230951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5230951 prefixEnd_5230951 := by exact prefixLift 5230951
  have htrace : WordTrace (prefixWord ++ tailWord_5230951) baseStart_5230951 baseEnd_5230951 := by
    simpa [prefixWord, tailWord_5230951, baseEnd_5230951] using wordTrace_append hprefix tailTrace_5230951
  have hstable : (prefixWord ++ tailWord_5230951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5230951).length < 2 ^ (prefixWord ++ tailWord_5230951).sum := by decide
  have hdescent : baseEnd_5230951 < baseStart_5230951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5230951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231013 : List Nat := [1, 3, 1, 2, 1, 1, 3, 6, 5]
def baseStart_5231013 : Nat := 118140960795 + 5231013 * 2 ^ 59
def prefixEnd_5231013 : Nat := 4983230072969 + 3 ^ 40 * 5231013 * 2
def baseEnd_5231013 : Nat := 298447108768627485697835

theorem tailTrace_5231013 : CollatzResearch.WordTrace tailWord_5231013 prefixEnd_5231013 298447108768627485697835 := by
  unfold tailWord_5231013
  simp only [CollatzResearch.WordTrace]
  refine ⟨190790718197940761739425693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127193812131960507826283795 190790718197940761739425693)
  ·
    refine ⟨71546519324227785652284635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190790718197940761739425693 71546519324227785652284635)
    ·
      refine ⟨107319778986341678478426953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71546519324227785652284635 107319778986341678478426953)
      ·
        refine ⟨80489834239756258858820215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107319778986341678478426953 80489834239756258858820215)
        ·
          refine ⟨120734751359634388288230323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80489834239756258858820215 120734751359634388288230323)
          ·
            refine ⟨181102127039451582432345485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120734751359634388288230323 181102127039451582432345485)
            ·
              refine ⟨67913297639794343412129557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181102127039451582432345485 67913297639794343412129557)
              ·
                refine ⟨3183435826865359847443573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67913297639794343412129557 3183435826865359847443573)
                ·
                  refine ⟨298447108768627485697835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3183435826865359847443573 298447108768627485697835)
                  ·
                    rfl

theorem cell23_5231013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 5].length) (baseStart_5231013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231013 prefixEnd_5231013 := by exact prefixLift 5231013
  have htrace : WordTrace (prefixWord ++ tailWord_5231013) baseStart_5231013 baseEnd_5231013 := by
    simpa [prefixWord, tailWord_5231013, baseEnd_5231013] using wordTrace_append hprefix tailTrace_5231013
  have hstable : (prefixWord ++ tailWord_5231013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231013).length < 2 ^ (prefixWord ++ tailWord_5231013).sum := by decide
  have hdescent : baseEnd_5231013 < baseStart_5231013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231018 : List Nat := [3, 1, 6, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_5231018 : Nat := 118140960795 + 5231018 * 2 ^ 59
def prefixEnd_5231018 : Nat := 4983230072969 + 3 ^ 40 * 5231018 * 2
def baseEnd_5231018 : Nat := 2686026546320919851717993

theorem tailTrace_5231018 : CollatzResearch.WordTrace tailWord_5231018 prefixEnd_5231018 2686026546320919851717993 := by
  unfold tailWord_5231018
  simp only [CollatzResearch.WordTrace]
  refine ⟨47697725140730661898339427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127193933708615098395571805 47697725140730661898339427)
  ·
    refine ⟨71546587711095992847509141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47697725140730661898339427 71546587711095992847509141)
    ·
      refine ⟨3353746298957624664726991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 71546587711095992847509141 3353746298957624664726991)
      ·
        refine ⟨5030619448436436997090487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3353746298957624664726991 5030619448436436997090487)
        ·
          refine ⟨7545929172654655495635731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5030619448436436997090487 7545929172654655495635731)
          ·
            refine ⟨11318893758981983243453597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7545929172654655495635731 11318893758981983243453597)
            ·
              refine ⟨4244585159618243716295099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11318893758981983243453597 4244585159618243716295099)
              ·
                refine ⟨6366877739427365574442649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4244585159618243716295099 6366877739427365574442649)
                ·
                  refine ⟨4775158304570524180831987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6366877739427365574442649 4775158304570524180831987)
                  ·
                    refine ⟨7162737456855786271247981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4775158304570524180831987 7162737456855786271247981)
                    ·
                      refine ⟨2686026546320919851717993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7162737456855786271247981 2686026546320919851717993)
                      ·
                        rfl

theorem cell23_5231018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_5231018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231018 prefixEnd_5231018 := by exact prefixLift 5231018
  have htrace : WordTrace (prefixWord ++ tailWord_5231018) baseStart_5231018 baseEnd_5231018 := by
    simpa [prefixWord, tailWord_5231018, baseEnd_5231018] using wordTrace_append hprefix tailTrace_5231018
  have hstable : (prefixWord ++ tailWord_5231018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231018).length < 2 ^ (prefixWord ++ tailWord_5231018).sum := by decide
  have hdescent : baseEnd_5231018 < baseStart_5231018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231026 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 3, 7]
def baseStart_5231026 : Nat := 118140960795 + 5231026 * 2 ^ 59
def prefixEnd_5231026 : Nat := 4983230072969 + 3 ^ 40 * 5231026 * 2
def baseEnd_5231026 : Nat := 895343551388718606805985

theorem tailTrace_5231026 : CollatzResearch.WordTrace tailWord_5231026 prefixEnd_5231026 895343551388718606805985 := by
  unfold tailWord_5231026
  simp only [CollatzResearch.WordTrace]
  refine ⟨47697798086723416239912233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127194128231262443306432621 47697798086723416239912233)
  ·
    refine ⟨35773348565042562179934175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47697798086723416239912233 35773348565042562179934175)
    ·
      refine ⟨53660022847563843269901263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35773348565042562179934175 53660022847563843269901263)
      ·
        refine ⟨80490034271345764904851895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53660022847563843269901263 80490034271345764904851895)
        ·
          refine ⟨120735051407018647357277843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80490034271345764904851895 120735051407018647357277843)
          ·
            refine ⟨181102577110527971035916765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120735051407018647357277843 181102577110527971035916765)
            ·
              refine ⟨67913466416447989138468787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181102577110527971035916765 67913466416447989138468787)
              ·
                refine ⟨101870199624671983707703181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67913466416447989138468787 101870199624671983707703181)
                ·
                  refine ⟨38201324859251993890388693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101870199624671983707703181 38201324859251993890388693)
                  ·
                    refine ⟨895343551388718606805985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38201324859251993890388693 895343551388718606805985)
                    ·
                      rfl

theorem cell23_5231026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_5231026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231026 prefixEnd_5231026 := by exact prefixLift 5231026
  have htrace : WordTrace (prefixWord ++ tailWord_5231026) baseStart_5231026 baseEnd_5231026 := by
    simpa [prefixWord, tailWord_5231026, baseEnd_5231026] using wordTrace_append hprefix tailTrace_5231026
  have hstable : (prefixWord ++ tailWord_5231026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231026).length < 2 ^ (prefixWord ++ tailWord_5231026).sum := by decide
  have hdescent : baseEnd_5231026 < baseStart_5231026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231060 : List Nat := [2, 4, 1, 2, 2, 2, 1, 2, 2, 5]
def baseStart_5231060 : Nat := 118140960795 + 5231060 * 2 ^ 59
def prefixEnd_5231060 : Nat := 4983230072969 + 3 ^ 40 * 5231060 * 2
def baseEnd_5231060 : Nat := 895349370836136229130933

theorem tailTrace_5231060 : CollatzResearch.WordTrace tailWord_5231060 prefixEnd_5231060 895349370836136229130933 := by
  unfold tailWord_5231060
  simp only [CollatzResearch.WordTrace]
  refine ⟨95396216214385244383193317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127194954952513659177591089 95396216214385244383193317)
  ·
    refine ⟨17886790540197233321848747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95396216214385244383193317 17886790540197233321848747)
    ·
      refine ⟨26830185810295849982773121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17886790540197233321848747 26830185810295849982773121)
      ·
        refine ⟨20122639357721887487079841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26830185810295849982773121 20122639357721887487079841)
        ·
          refine ⟨15091979518291415615309881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20122639357721887487079841 15091979518291415615309881)
          ·
            refine ⟨11318984638718561711482411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15091979518291415615309881 11318984638718561711482411)
            ·
              refine ⟨16978476958077842567223617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11318984638718561711482411 16978476958077842567223617)
              ·
                refine ⟨12733857718558381925417713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16978476958077842567223617 12733857718558381925417713)
                ·
                  refine ⟨9550393288918786444063285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12733857718558381925417713 9550393288918786444063285)
                  ·
                    refine ⟨895349370836136229130933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9550393288918786444063285 895349370836136229130933)
                    ·
                      rfl

theorem cell23_5231060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_5231060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231060 prefixEnd_5231060 := by exact prefixLift 5231060
  have htrace : WordTrace (prefixWord ++ tailWord_5231060) baseStart_5231060 baseEnd_5231060 := by
    simpa [prefixWord, tailWord_5231060, baseEnd_5231060] using wordTrace_append hprefix tailTrace_5231060
  have hstable : (prefixWord ++ tailWord_5231060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231060).length < 2 ^ (prefixWord ++ tailWord_5231060).sum := by decide
  have hdescent : baseEnd_5231060 < baseStart_5231060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231083 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 3]
def baseStart_5231083 : Nat := 118140960795 + 5231083 * 2 ^ 59
def prefixEnd_5231083 : Nat := 4983230072969 + 3 ^ 40 * 5231083 * 2
def baseEnd_5231083 : Nat := 2686059922563462097405193

theorem tailTrace_5231083 : CollatzResearch.WordTrace tailWord_5231083 prefixEnd_5231083 2686059922563462097405193 := by
  unfold tailWord_5231083
  simp only [CollatzResearch.WordTrace]
  refine ⟨190793271307687163694473903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127195514205124775796315935 190793271307687163694473903)
  ·
    refine ⟨286189906961530745541710855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190793271307687163694473903 286189906961530745541710855)
    ·
      refine ⟨429284860442296118312566283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286189906961530745541710855 429284860442296118312566283)
      ·
        refine ⟨643927290663444177468849425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429284860442296118312566283 643927290663444177468849425)
        ·
          refine ⟨482945467997583133101637069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 643927290663444177468849425 482945467997583133101637069)
          ·
            refine ⟨181104550499093674913113901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 482945467997583133101637069 181104550499093674913113901)
            ·
              refine ⟨67914206437160128092417713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181104550499093674913113901 67914206437160128092417713)
              ·
                refine ⟨50935654827870096069313285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67914206437160128092417713 50935654827870096069313285)
                ·
                  refine ⟨9550435280225643012996241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50935654827870096069313285 9550435280225643012996241)
                  ·
                    refine ⟨7162826460169232259747181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9550435280225643012996241 7162826460169232259747181)
                    ·
                      refine ⟨2686059922563462097405193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7162826460169232259747181 2686059922563462097405193)
                      ·
                        rfl

theorem cell23_5231083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 3].length) (baseStart_5231083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231083 prefixEnd_5231083 := by exact prefixLift 5231083
  have htrace : WordTrace (prefixWord ++ tailWord_5231083) baseStart_5231083 baseEnd_5231083 := by
    simpa [prefixWord, tailWord_5231083, baseEnd_5231083] using wordTrace_append hprefix tailTrace_5231083
  have hstable : (prefixWord ++ tailWord_5231083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231083).length < 2 ^ (prefixWord ++ tailWord_5231083).sum := by decide
  have hdescent : baseEnd_5231083 < baseStart_5231083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231164 : List Nat := [2, 2, 2, 2, 3, 1, 1, 5, 1, 1, 3]
def baseStart_5231164 : Nat := 118140960795 + 5231164 * 2 ^ 59
def prefixEnd_5231164 : Nat := 4983230072969 + 3 ^ 40 * 5231164 * 2
def baseEnd_5231164 : Nat := 2686101514496476280492321

theorem tailTrace_5231164 : CollatzResearch.WordTrace tailWord_5231164 prefixEnd_5231164 2686101514496476280492321 := by
  unfold tailWord_5231164
  simp only [CollatzResearch.WordTrace]
  refine ⟨95398112810196857264086273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127197483746929143018781697 95398112810196857264086273)
  ·
    refine ⟨71548584607647642948064705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95398112810196857264086273 71548584607647642948064705)
    ·
      refine ⟨53661438455735732211048529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71548584607647642948064705 53661438455735732211048529)
      ·
        refine ⟨40246078841801799158286397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53661438455735732211048529 40246078841801799158286397)
        ·
          refine ⟨15092279565675674684357399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40246078841801799158286397 15092279565675674684357399)
          ·
            refine ⟨22638419348513512026536099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15092279565675674684357399 22638419348513512026536099)
            ·
              refine ⟨33957629022770268039804149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22638419348513512026536099 33957629022770268039804149)
              ·
                refine ⟨3183527720884712628731639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33957629022770268039804149 3183527720884712628731639)
                ·
                  refine ⟨4775291581327068943097459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3183527720884712628731639 4775291581327068943097459)
                  ·
                    refine ⟨7162937371990603414646189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4775291581327068943097459 7162937371990603414646189)
                    ·
                      refine ⟨2686101514496476280492321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7162937371990603414646189 2686101514496476280492321)
                      ·
                        rfl

theorem cell23_5231164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_5231164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231164 prefixEnd_5231164 := by exact prefixLift 5231164
  have htrace : WordTrace (prefixWord ++ tailWord_5231164) baseStart_5231164 baseEnd_5231164 := by
    simpa [prefixWord, tailWord_5231164, baseEnd_5231164] using wordTrace_append hprefix tailTrace_5231164
  have hstable : (prefixWord ++ tailWord_5231164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231164).length < 2 ^ (prefixWord ++ tailWord_5231164).sum := by decide
  have hdescent : baseEnd_5231164 < baseStart_5231164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231180 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 4, 4]
def baseStart_5231180 : Nat := 118140960795 + 5231180 * 2 ^ 59
def prefixEnd_5231180 : Nat := 4983230072969 + 3 ^ 40 * 5231180 * 2
def baseEnd_5231180 : Nat := 895369910062316072630749

theorem tailTrace_5231180 : CollatzResearch.WordTrace tailWord_5231180 prefixEnd_5231180 895369910062316072630749 := by
  unfold tailWord_5231180
  simp only [CollatzResearch.WordTrace]
  refine ⟨95398404594167874630377497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127197872792223832840503329 95398404594167874630377497)
  ·
    refine ⟨71548803445625905972783123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95398404594167874630377497 71548803445625905972783123)
    ·
      refine ⟨107323205168438858959174685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71548803445625905972783123 107323205168438858959174685)
      ·
        refine ⟨40246201938164572109690507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107323205168438858959174685 40246201938164572109690507)
        ·
          refine ⟨60369302907246858164535761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40246201938164572109690507 60369302907246858164535761)
          ·
            refine ⟨45276977180435143623401821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60369302907246858164535761 45276977180435143623401821)
            ·
              refine ⟨16978866442663178858775683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45276977180435143623401821 16978866442663178858775683)
              ·
                refine ⟨25468299663994768288163525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16978866442663178858775683 25468299663994768288163525)
                ·
                  refine ⟨4775306186999019054030661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25468299663994768288163525 4775306186999019054030661)
                  ·
                    refine ⟨895369910062316072630749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4775306186999019054030661 895369910062316072630749)
                    ·
                      rfl

theorem cell23_5231180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 4, 4].length) (baseStart_5231180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231180 prefixEnd_5231180 := by exact prefixLift 5231180
  have htrace : WordTrace (prefixWord ++ tailWord_5231180) baseStart_5231180 baseEnd_5231180 := by
    simpa [prefixWord, tailWord_5231180, baseEnd_5231180] using wordTrace_append hprefix tailTrace_5231180
  have hstable : (prefixWord ++ tailWord_5231180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231180).length < 2 ^ (prefixWord ++ tailWord_5231180).sum := by decide
  have hdescent : baseEnd_5231180 < baseStart_5231180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231181 : List Nat := [1, 6, 1, 1, 2, 1, 2, 4, 1, 1, 3]
def baseStart_5231181 : Nat := 118140960795 + 5231181 * 2 ^ 59
def prefixEnd_5231181 : Nat := 4983230072969 + 3 ^ 40 * 5231181 * 2
def baseEnd_5231181 : Nat := 2686110243667602713979743

theorem tailTrace_5231181 : CollatzResearch.WordTrace tailWord_5231181 prefixEnd_5231181 2686110243667602713979743 := by
  unfold tailWord_5231181
  simp only [CollatzResearch.WordTrace]
  refine ⟨190796845661332126431541397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127197897107554750954360931 190796845661332126431541397)
  ·
    refine ⟨8943602140374943426478503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 190796845661332126431541397 8943602140374943426478503)
    ·
      refine ⟨13415403210562415139717755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8943602140374943426478503 13415403210562415139717755)
      ·
        refine ⟨20123104815843622709576633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13415403210562415139717755 20123104815843622709576633)
        ·
          refine ⟨15092328611882717032182475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20123104815843622709576633 15092328611882717032182475)
          ·
            refine ⟨22638492917824075548273713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15092328611882717032182475 22638492917824075548273713)
            ·
              refine ⟨16978869688368056661205285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22638492917824075548273713 16978869688368056661205285)
              ·
                refine ⟨3183538066569010623975991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16978869688368056661205285 3183538066569010623975991)
                ·
                  refine ⟨4775307099853515935963987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3183538066569010623975991 4775307099853515935963987)
                  ·
                    refine ⟨7162960649780273903945981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4775307099853515935963987 7162960649780273903945981)
                    ·
                      refine ⟨2686110243667602713979743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7162960649780273903945981 2686110243667602713979743)
                      ·
                        rfl

theorem cell23_5231181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_5231181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231181 prefixEnd_5231181 := by exact prefixLift 5231181
  have htrace : WordTrace (prefixWord ++ tailWord_5231181) baseStart_5231181 baseEnd_5231181 := by
    simpa [prefixWord, tailWord_5231181, baseEnd_5231181] using wordTrace_append hprefix tailTrace_5231181
  have hstable : (prefixWord ++ tailWord_5231181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231181).length < 2 ^ (prefixWord ++ tailWord_5231181).sum := by decide
  have hdescent : baseEnd_5231181 < baseStart_5231181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231183 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 4]
def baseStart_5231183 : Nat := 118140960795 + 5231183 * 2 ^ 59
def prefixEnd_5231183 : Nat := 4983230072969 + 3 ^ 40 * 5231183 * 2
def baseEnd_5231183 : Nat := 2686111270628911706154733

theorem tailTrace_5231183 : CollatzResearch.WordTrace tailWord_5231183 prefixEnd_5231183 2686111270628911706154733 := by
  unfold tailWord_5231183
  simp only [CollatzResearch.WordTrace]
  refine ⟨190796918607324880773114203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127197945738216587182076135 190796918607324880773114203)
  ·
    refine ⟨286195377910987321159671305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190796918607324880773114203 286195377910987321159671305)
    ·
      refine ⟨214646533433240490869753479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286195377910987321159671305 214646533433240490869753479)
      ·
        refine ⟨321969800149860736304630219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214646533433240490869753479 321969800149860736304630219)
        ·
          refine ⟨482954700224791104456945329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321969800149860736304630219 482954700224791104456945329)
          ·
            refine ⟨362216025168593328342708997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 482954700224791104456945329 362216025168593328342708997)
            ·
              refine ⟨67915504719111249064257937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 362216025168593328342708997 67915504719111249064257937)
              ·
                refine ⟨50936628539333436798193453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67915504719111249064257937 50936628539333436798193453)
                ·
                  refine ⟨19101235702250038799322545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50936628539333436798193453 19101235702250038799322545)
                  ·
                    refine ⟨14325926776687529099491909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19101235702250038799322545 14325926776687529099491909)
                    ·
                      refine ⟨2686111270628911706154733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14325926776687529099491909 2686111270628911706154733)
                      ·
                        rfl

theorem cell23_5231183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 4].length) (baseStart_5231183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231183 prefixEnd_5231183 := by exact prefixLift 5231183
  have htrace : WordTrace (prefixWord ++ tailWord_5231183) baseStart_5231183 baseEnd_5231183 := by
    simpa [prefixWord, tailWord_5231183, baseEnd_5231183] using wordTrace_append hprefix tailTrace_5231183
  have hstable : (prefixWord ++ tailWord_5231183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231183).length < 2 ^ (prefixWord ++ tailWord_5231183).sum := by decide
  have hdescent : baseEnd_5231183 < baseStart_5231183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231200 : List Nat := [2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 4]
def baseStart_5231200 : Nat := 118140960795 + 5231200 * 2 ^ 59
def prefixEnd_5231200 : Nat := 4983230072969 + 3 ^ 40 * 5231200 * 2
def baseEnd_5231200 : Nat := 2686119999800038139642155

theorem tailTrace_5231200 : CollatzResearch.WordTrace tailWord_5231200 prefixEnd_5231200 2686119999800038139642155 := by
  unfold tailWord_5231200
  simp only [CollatzResearch.WordTrace]
  refine ⟨95398769324131646338241527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127198359098842195117655369 95398769324131646338241527)
  ·
    refine ⟨143098153986197469507362291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95398769324131646338241527 143098153986197469507362291)
    ·
      refine ⟨214647230979296204261043437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143098153986197469507362291 214647230979296204261043437)
      ·
        refine ⟨80492711617236076597891289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214647230979296204261043437 80492711617236076597891289)
        ·
          refine ⟨60369533712927057448418467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80492711617236076597891289 60369533712927057448418467)
          ·
            refine ⟨90554300569390586172627701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60369533712927057448418467 90554300569390586172627701)
            ·
              refine ⟨8489465678380367453683847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90554300569390586172627701 8489465678380367453683847)
              ·
                refine ⟨12734198517570551180525771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8489465678380367453683847 12734198517570551180525771)
                ·
                  refine ⟨19101297776355826770788657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12734198517570551180525771 19101297776355826770788657)
                  ·
                    refine ⟨14325973332266870078091493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19101297776355826770788657 14325973332266870078091493)
                    ·
                      refine ⟨2686119999800038139642155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14325973332266870078091493 2686119999800038139642155)
                      ·
                        rfl

theorem cell23_5231200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_5231200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231200 prefixEnd_5231200 := by exact prefixLift 5231200
  have htrace : WordTrace (prefixWord ++ tailWord_5231200) baseStart_5231200 baseEnd_5231200 := by
    simpa [prefixWord, tailWord_5231200, baseEnd_5231200] using wordTrace_append hprefix tailTrace_5231200
  have hstable : (prefixWord ++ tailWord_5231200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231200).length < 2 ^ (prefixWord ++ tailWord_5231200).sum := by decide
  have hdescent : baseEnd_5231200 < baseStart_5231200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231237 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 4, 1, 3]
def baseStart_5231237 : Nat := 118140960795 + 5231237 * 2 ^ 59
def prefixEnd_5231237 : Nat := 4983230072969 + 3 ^ 40 * 5231237 * 2
def baseEnd_5231237 : Nat := 2686138998584254494879485

theorem tailTrace_5231237 : CollatzResearch.WordTrace tailWord_5231237 prefixEnd_5231237 2686138998584254494879485 := by
  unfold tailWord_5231237
  simp only [CollatzResearch.WordTrace]
  refine ⟨190798888149129247995579965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127199258766086165330386643 190798888149129247995579965)
  ·
    refine ⟨71549583055923467998342487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190798888149129247995579965 71549583055923467998342487)
    ·
      refine ⟨107324374583885201997513731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71549583055923467998342487 107324374583885201997513731)
      ·
        refine ⟨160986561875827802996270597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107324374583885201997513731 160986561875827802996270597)
        ·
          refine ⟨30184980351717713061800737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160986561875827802996270597 30184980351717713061800737)
          ·
            refine ⟨22638735263788284796350553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30184980351717713061800737 22638735263788284796350553)
            ·
              refine ⟨16979051447841213597262915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22638735263788284796350553 16979051447841213597262915)
              ·
                refine ⟨25468577171761820395894373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16979051447841213597262915 25468577171761820395894373)
                ·
                  refine ⟨4775358219705341324230195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25468577171761820395894373 4775358219705341324230195)
                  ·
                    refine ⟨7163037329558011986345293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4775358219705341324230195 7163037329558011986345293)
                    ·
                      refine ⟨2686138998584254494879485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7163037329558011986345293 2686138998584254494879485)
                      ·
                        rfl

theorem cell23_5231237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 1, 3].length) (baseStart_5231237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231237 prefixEnd_5231237 := by exact prefixLift 5231237
  have htrace : WordTrace (prefixWord ++ tailWord_5231237) baseStart_5231237 baseEnd_5231237 := by
    simpa [prefixWord, tailWord_5231237, baseEnd_5231237] using wordTrace_append hprefix tailTrace_5231237
  have hstable : (prefixWord ++ tailWord_5231237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231237).length < 2 ^ (prefixWord ++ tailWord_5231237).sum := by decide
  have hdescent : baseEnd_5231237 < baseStart_5231237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231258 : List Nat := [3, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3]
def baseStart_5231258 : Nat := 118140960795 + 5231258 * 2 ^ 59
def prefixEnd_5231258 : Nat := 4983230072969 + 3 ^ 40 * 5231258 * 2
def baseEnd_5231258 : Nat := 2686149781677998912716889

theorem tailTrace_5231258 : CollatzResearch.WordTrace tailWord_5231258 prefixEnd_5231258 2686149781677998912716889 := by
  unfold tailWord_5231258
  simp only [CollatzResearch.WordTrace]
  refine ⟨47699913520513292145523607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127199769388035445721396285 47699913520513292145523607)
  ·
    refine ⟨71549870280769938218285411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47699913520513292145523607 71549870280769938218285411)
    ·
      refine ⟨107324805421154907327428117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71549870280769938218285411 107324805421154907327428117)
      ·
        refine ⟨5030850254116636280973193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 107324805421154907327428117 5030850254116636280973193)
        ·
          refine ⟨3773137690587477210729895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5030850254116636280973193 3773137690587477210729895)
          ·
            refine ⟨5659706535881215816094843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3773137690587477210729895 5659706535881215816094843)
            ·
              refine ⟨8489559803821823724142265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5659706535881215816094843 8489559803821823724142265)
              ·
                refine ⟨6367169852866367793106699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8489559803821823724142265 6367169852866367793106699)
                ·
                  refine ⟨9550754779299551689660049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6367169852866367793106699 9550754779299551689660049)
                  ·
                    refine ⟨7163066084474663767245037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9550754779299551689660049 7163066084474663767245037)
                    ·
                      refine ⟨2686149781677998912716889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7163066084474663767245037 2686149781677998912716889)
                      ·
                        rfl

theorem cell23_5231258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_5231258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231258 prefixEnd_5231258 := by exact prefixLift 5231258
  have htrace : WordTrace (prefixWord ++ tailWord_5231258) baseStart_5231258 baseEnd_5231258 := by
    simpa [prefixWord, tailWord_5231258, baseEnd_5231258] using wordTrace_append hprefix tailTrace_5231258
  have hstable : (prefixWord ++ tailWord_5231258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231258).length < 2 ^ (prefixWord ++ tailWord_5231258).sum := by decide
  have hdescent : baseEnd_5231258 < baseStart_5231258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231264 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 3, 3, 2]
def baseStart_5231264 : Nat := 118140960795 + 5231264 * 2 ^ 59
def prefixEnd_5231264 : Nat := 4983230072969 + 3 ^ 40 * 5231264 * 2
def baseEnd_5231264 : Nat := 2686152862561925889241861

theorem tailTrace_5231264 : CollatzResearch.WordTrace tailWord_5231264 prefixEnd_5231264 2686152862561925889241861 := by
  unfold tailWord_5231264
  simp only [CollatzResearch.WordTrace]
  refine ⟨95399936460015715803406423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127199915280020954404541897 95399936460015715803406423)
  ·
    refine ⟨143099904690023573705109635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95399936460015715803406423 143099904690023573705109635)
    ·
      refine ⟨214649857035035360557664453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143099904690023573705109635 214649857035035360557664453)
      ·
        refine ⟨40246848194069130104562085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 214649857035035360557664453 40246848194069130104562085)
        ·
          refine ⟨7546284036387961894605391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40246848194069130104562085 7546284036387961894605391)
          ·
            refine ⟨11319426054581942841908087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7546284036387961894605391 11319426054581942841908087)
            ·
              refine ⟨16979139081872914262862131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11319426054581942841908087 16979139081872914262862131)
              ·
                refine ⟨25468708622809371394293197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16979139081872914262862131 25468708622809371394293197)
                ·
                  refine ⟨9550765733553514272859949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25468708622809371394293197 9550765733553514272859949)
                  ·
                    refine ⟨3581537150082567852322481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9550765733553514272859949 3581537150082567852322481)
                    ·
                      refine ⟨2686152862561925889241861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3581537150082567852322481 2686152862561925889241861)
                      ·
                        rfl

theorem cell23_5231264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_5231264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231264 prefixEnd_5231264 := by exact prefixLift 5231264
  have htrace : WordTrace (prefixWord ++ tailWord_5231264) baseStart_5231264 baseEnd_5231264 := by
    simpa [prefixWord, tailWord_5231264, baseEnd_5231264] using wordTrace_append hprefix tailTrace_5231264
  have hstable : (prefixWord ++ tailWord_5231264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231264).length < 2 ^ (prefixWord ++ tailWord_5231264).sum := by decide
  have hdescent : baseEnd_5231264 < baseStart_5231264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231290 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4]
def baseStart_5231290 : Nat := 118140960795 + 5231290 * 2 ^ 59
def prefixEnd_5231290 : Nat := 4983230072969 + 3 ^ 40 * 5231290 * 2
def baseEnd_5231290 : Nat := 2686166213058942787516741

theorem tailTrace_5231290 : CollatzResearch.WordTrace tailWord_5231290 prefixEnd_5231290 2686166213058942787516741 := by
  unfold tailWord_5231290
  simp only [CollatzResearch.WordTrace]
  refine ⟨47700205304484309511814831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127200547478624825364839549 47700205304484309511814831)
  ·
    refine ⟨71550307956726464267722247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47700205304484309511814831 71550307956726464267722247)
    ·
      refine ⟨107325461935089696401583371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71550307956726464267722247 107325461935089696401583371)
      ·
        refine ⟨160988192902634544602375057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107325461935089696401583371 160988192902634544602375057)
        ·
          refine ⟨120741144676975908451781293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160988192902634544602375057 120741144676975908451781293)
          ·
            refine ⟨45277929253865965669417985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120741144676975908451781293 45277929253865965669417985)
            ·
              refine ⟨33958446940399474252063489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45277929253865965669417985 33958446940399474252063489)
              ·
                refine ⟨25468835205299605689047617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33958446940399474252063489 25468835205299605689047617)
                ·
                  refine ⟨19101626403974704266785713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25468835205299605689047617 19101626403974704266785713)
                  ·
                    refine ⟨14326219802981028200089285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19101626403974704266785713 14326219802981028200089285)
                    ·
                      refine ⟨2686166213058942787516741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14326219802981028200089285 2686166213058942787516741)
                      ·
                        rfl

theorem cell23_5231290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_5231290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231290 prefixEnd_5231290 := by exact prefixLift 5231290
  have htrace : WordTrace (prefixWord ++ tailWord_5231290) baseStart_5231290 baseEnd_5231290 := by
    simpa [prefixWord, tailWord_5231290, baseEnd_5231290] using wordTrace_append hprefix tailTrace_5231290
  have hstable : (prefixWord ++ tailWord_5231290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231290).length < 2 ^ (prefixWord ++ tailWord_5231290).sum := by decide
  have hdescent : baseEnd_5231290 < baseStart_5231290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231367 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 4]
def baseStart_5231367 : Nat := 118140960795 + 5231367 * 2 ^ 59
def prefixEnd_5231367 : Nat := 4983230072969 + 3 ^ 40 * 5231367 * 2
def baseEnd_5231367 : Nat := 2686205751069338986253887

theorem tailTrace_5231367 : CollatzResearch.WordTrace tailWord_5231367 prefixEnd_5231367 2686205751069338986253887 := by
  unfold tailWord_5231367
  simp only [CollatzResearch.WordTrace]
  refine ⟨190803629638658280197812355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127202419759105520131874903 190803629638658280197812355)
  ·
    refine ⟨286205444457987420296718533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190803629638658280197812355 286205444457987420296718533)
    ·
      refine ⟨53663520835872641305634725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 286205444457987420296718533 53663520835872641305634725)
      ·
        refine ⟨10061910156726120244806511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53663520835872641305634725 10061910156726120244806511)
        ·
          refine ⟨15092865235089180367209767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10061910156726120244806511 15092865235089180367209767)
          ·
            refine ⟨22639297852633770550814651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15092865235089180367209767 22639297852633770550814651)
            ·
              refine ⟨33958946778950655826221977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22639297852633770550814651 33958946778950655826221977)
              ·
                refine ⟨25469210084212991869666483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33958946778950655826221977 25469210084212991869666483)
                ·
                  refine ⟨38203815126319487804499725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25469210084212991869666483 38203815126319487804499725)
                  ·
                    refine ⟨14326430672369807926687397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38203815126319487804499725 14326430672369807926687397)
                    ·
                      refine ⟨2686205751069338986253887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14326430672369807926687397 2686205751069338986253887)
                      ·
                        rfl

theorem cell23_5231367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_5231367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231367 prefixEnd_5231367 := by exact prefixLift 5231367
  have htrace : WordTrace (prefixWord ++ tailWord_5231367) baseStart_5231367 baseEnd_5231367 := by
    simpa [prefixWord, tailWord_5231367, baseEnd_5231367] using wordTrace_append hprefix tailTrace_5231367
  have hstable : (prefixWord ++ tailWord_5231367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231367).length < 2 ^ (prefixWord ++ tailWord_5231367).sum := by decide
  have hdescent : baseEnd_5231367 < baseStart_5231367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231377 : List Nat := [1, 2, 2, 1, 1, 3, 4, 2, 3, 4]
def baseStart_5231377 : Nat := 118140960795 + 5231377 * 2 ^ 59
def prefixEnd_5231377 : Nat := 4983230072969 + 3 ^ 40 * 5231377 * 2
def baseEnd_5231377 : Nat := 895403628625294649042947

theorem tailTrace_5231377 : CollatzResearch.WordTrace tailWord_5231377 prefixEnd_5231377 895403628625294649042947 := by
  unfold tailWord_5231377
  simp only [CollatzResearch.WordTrace]
  refine ⟨190803994368622051905676385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127202662912414701270450923 190803994368622051905676385)
  ·
    refine ⟨143102995776466538929257289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190803994368622051905676385 143102995776466538929257289)
    ·
      refine ⟨107327246832349904196942967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143102995776466538929257289 107327246832349904196942967)
      ·
        refine ⟨160990870248524856295414451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107327246832349904196942967 160990870248524856295414451)
        ·
          refine ⟨241486305372787284443121677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160990870248524856295414451 241486305372787284443121677)
          ·
            refine ⟨90557364514795231666170629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 241486305372787284443121677 90557364514795231666170629)
            ·
              refine ⟨16979505846524105937406993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90557364514795231666170629 16979505846524105937406993)
              ·
                refine ⟨12734629384893079453055245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16979505846524105937406993 12734629384893079453055245)
                ·
                  refine ⟨4775486019334904794895717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12734629384893079453055245 4775486019334904794895717)
                  ·
                    refine ⟨895403628625294649042947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4775486019334904794895717 895403628625294649042947)
                    ·
                      rfl

theorem cell23_5231377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 4].length) (baseStart_5231377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231377 prefixEnd_5231377 := by exact prefixLift 5231377
  have htrace : WordTrace (prefixWord ++ tailWord_5231377) baseStart_5231377 baseEnd_5231377 := by
    simpa [prefixWord, tailWord_5231377, baseEnd_5231377] using wordTrace_append hprefix tailTrace_5231377
  have hstable : (prefixWord ++ tailWord_5231377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231377).length < 2 ^ (prefixWord ++ tailWord_5231377).sum := by decide
  have hdescent : baseEnd_5231377 < baseStart_5231377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231420 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 2, 9]
def baseStart_5231420 : Nat := 118140960795 + 5231420 * 2 ^ 59
def prefixEnd_5231420 : Nat := 4983230072969 + 3 ^ 40 * 5231420 * 2
def baseEnd_5231420 : Nat := 895410988514675759630381

theorem tailTrace_5231420 : CollatzResearch.WordTrace tailWord_5231420 prefixEnd_5231420 895410988514675759630381 := by
  unfold tailWord_5231420
  simp only [CollatzResearch.WordTrace]
  refine ⟨95402781353733135124745857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127203708471644180166327809 95402781353733135124745857)
  ·
    refine ⟨71552086015299851343559393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95402781353733135124745857 71552086015299851343559393)
    ·
      refine ⟨53664064511474888507669545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71552086015299851343559393 53664064511474888507669545)
      ·
        refine ⟨40248048383606166380752159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53664064511474888507669545 40248048383606166380752159)
        ·
          refine ⟨60372072575409249571128239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40248048383606166380752159 60372072575409249571128239)
          ·
            refine ⟨90558108863113874356692359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60372072575409249571128239 90558108863113874356692359)
            ·
              refine ⟨135837163294670811535038539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90558108863113874356692359 135837163294670811535038539)
              ·
                refine ⟨203755744942006217302557809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135837163294670811535038539 203755744942006217302557809)
                ·
                  refine ⟨152816808706504662976918357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203755744942006217302557809 152816808706504662976918357)
                  ·
                    refine ⟨895410988514675759630381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 152816808706504662976918357 895410988514675759630381)
                    ·
                      rfl

theorem cell23_5231420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_5231420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231420 prefixEnd_5231420 := by exact prefixLift 5231420
  have htrace : WordTrace (prefixWord ++ tailWord_5231420) baseStart_5231420 baseEnd_5231420 := by
    simpa [prefixWord, tailWord_5231420, baseEnd_5231420] using wordTrace_append hprefix tailTrace_5231420
  have hstable : (prefixWord ++ tailWord_5231420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231420).length < 2 ^ (prefixWord ++ tailWord_5231420).sum := by decide
  have hdescent : baseEnd_5231420 < baseStart_5231420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231467 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 4, 4]
def baseStart_5231467 : Nat := 118140960795 + 5231467 * 2 ^ 59
def prefixEnd_5231467 : Nat := 4983230072969 + 3 ^ 40 * 5231467 * 2
def baseEnd_5231467 : Nat := 895419033044929531667809

theorem tailTrace_5231467 : CollatzResearch.WordTrace tailWord_5231467 prefixEnd_5231467 895419033044929531667809 := by
  unfold tailWord_5231467
  simp only [CollatzResearch.WordTrace]
  refine ⟨190807276938295997276452655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127204851292197331517635103 190807276938295997276452655)
  ·
    refine ⟨286210915407443995914678983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190807276938295997276452655 286210915407443995914678983)
    ·
      refine ⟨429316373111165993872018475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286210915407443995914678983 429316373111165993872018475)
      ·
        refine ⟨643974559666748990808027713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429316373111165993872018475 643974559666748990808027713)
        ·
          refine ⟨482980919750061743106020785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 643974559666748990808027713 482980919750061743106020785)
          ·
            refine ⟨362235689812546307329515589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 482980919750061743106020785 362235689812546307329515589)
            ·
              refine ⟨67919191839852432624284173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 362235689812546307329515589 67919191839852432624284173)
              ·
                refine ⟨25469696939944662234106565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67919191839852432624284173 25469696939944662234106565)
                ·
                  refine ⟨4775568176239624168894981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25469696939944662234106565 4775568176239624168894981)
                  ·
                    refine ⟨895419033044929531667809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4775568176239624168894981 895419033044929531667809)
                    ·
                      rfl

theorem cell23_5231467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 4].length) (baseStart_5231467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231467 prefixEnd_5231467 := by exact prefixLift 5231467
  have htrace : WordTrace (prefixWord ++ tailWord_5231467) baseStart_5231467 baseEnd_5231467 := by
    simpa [prefixWord, tailWord_5231467, baseEnd_5231467] using wordTrace_append hprefix tailTrace_5231467
  have hstable : (prefixWord ++ tailWord_5231467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231467).length < 2 ^ (prefixWord ++ tailWord_5231467).sum := by decide
  have hdescent : baseEnd_5231467 < baseStart_5231467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231480 : List Nat := [2, 1, 2, 1, 1, 1, 1, 14]
def baseStart_5231480 : Nat := 118140960795 + 5231480 * 2 ^ 59
def prefixEnd_5231480 : Nat := 4983230072969 + 3 ^ 40 * 5231480 * 2
def baseEnd_5231480 : Nat := 99491250903085075708921

theorem tailTrace_5231480 : CollatzResearch.WordTrace tailWord_5231480 prefixEnd_5231480 99491250903085075708921 := by
  unfold tailWord_5231480
  simp only [CollatzResearch.WordTrace]
  refine ⟨95403875543624450248337947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127205167391499266997783929 95403875543624450248337947)
  ·
    refine ⟨143105813315436675372506921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95403875543624450248337947 143105813315436675372506921)
    ·
      refine ⟨107329359986577506529380191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143105813315436675372506921 107329359986577506529380191)
      ·
        refine ⟨160994039979866259794070287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107329359986577506529380191 160994039979866259794070287)
        ·
          refine ⟨241491059969799389691105431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160994039979866259794070287 241491059969799389691105431)
          ·
            refine ⟨362236589954699084536658147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241491059969799389691105431 362236589954699084536658147)
            ·
              refine ⟨543354884932048626804987221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362236589954699084536658147 543354884932048626804987221)
              ·
                refine ⟨99491250903085075708921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 543354884932048626804987221 99491250903085075708921)
                ·
                  rfl

theorem cell23_5231480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 14].length) (baseStart_5231480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231480 prefixEnd_5231480 := by exact prefixLift 5231480
  have htrace : WordTrace (prefixWord ++ tailWord_5231480) baseStart_5231480 baseEnd_5231480 := by
    simpa [prefixWord, tailWord_5231480, baseEnd_5231480] using wordTrace_append hprefix tailTrace_5231480
  have hstable : (prefixWord ++ tailWord_5231480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231480).length < 2 ^ (prefixWord ++ tailWord_5231480).sum := by decide
  have hdescent : baseEnd_5231480 < baseStart_5231480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231487 : List Nat := [1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 4]
def baseStart_5231487 : Nat := 118140960795 + 5231487 * 2 ^ 59
def prefixEnd_5231487 : Nat := 4983230072969 + 3 ^ 40 * 5231487 * 2
def baseEnd_5231487 : Nat := 2686267368747878516753335

theorem tailTrace_5231487 : CollatzResearch.WordTrace tailWord_5231487 prefixEnd_5231487 2686267368747878516753335 := by
  unfold tailWord_5231487
  simp only [CollatzResearch.WordTrace]
  refine ⟨190808006398223540692180715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127205337598815693794787143 190808006398223540692180715)
  ·
    refine ⟨286212009597335311038271073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190808006398223540692180715 286212009597335311038271073)
    ·
      refine ⟨214659007198001483278703305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286212009597335311038271073 214659007198001483278703305)
      ·
        refine ⟨160994255398501112459027479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214659007198001483278703305 160994255398501112459027479)
        ·
          refine ⟨241491383097751668688541219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160994255398501112459027479 241491383097751668688541219)
          ·
            refine ⟨362237074646627503032811829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241491383097751668688541219 362237074646627503032811829)
            ·
              refine ⟨33959725748121328409326109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 362237074646627503032811829 33959725748121328409326109)
              ·
                refine ⟨12734897155545498153497291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33959725748121328409326109 12734897155545498153497291)
                ·
                  refine ⟨19102345733318247230245937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12734897155545498153497291 19102345733318247230245937)
                  ·
                    refine ⟨14326759299988685422684453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19102345733318247230245937 14326759299988685422684453)
                    ·
                      refine ⟨2686267368747878516753335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14326759299988685422684453 2686267368747878516753335)
                      ·
                        rfl

theorem cell23_5231487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_5231487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231487 prefixEnd_5231487 := by exact prefixLift 5231487
  have htrace : WordTrace (prefixWord ++ tailWord_5231487) baseStart_5231487 baseEnd_5231487 := by
    simpa [prefixWord, tailWord_5231487, baseEnd_5231487] using wordTrace_append hprefix tailTrace_5231487
  have hstable : (prefixWord ++ tailWord_5231487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231487).length < 2 ^ (prefixWord ++ tailWord_5231487).sum := by decide
  have hdescent : baseEnd_5231487 < baseStart_5231487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231491 : List Nat := [1, 1, 1, 3, 4, 1, 3, 2, 3, 2, 2]
def baseStart_5231491 : Nat := 118140960795 + 5231491 * 2 ^ 59
def prefixEnd_5231491 : Nat := 4983230072969 + 3 ^ 40 * 5231491 * 2
def baseEnd_5231491 : Nat := 2686269422670496501103317

theorem tailTrace_5231491 : CollatzResearch.WordTrace tailWord_5231491 prefixEnd_5231491 2686269422670496501103317 := by
  unfold tailWord_5231491
  simp only [CollatzResearch.WordTrace]
  refine ⟨190808152290209049375326327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127205434860139366250217551 190808152290209049375326327)
  ·
    refine ⟨286212228435313574062989491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190808152290209049375326327 286212228435313574062989491)
    ·
      refine ⟨429318342652970361094484237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286212228435313574062989491 429318342652970361094484237)
      ·
        refine ⟨160994378494863885410431589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 429318342652970361094484237 160994378494863885410431589)
        ·
          refine ⟨30186445967786978514455923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160994378494863885410431589 30186445967786978514455923)
          ·
            refine ⟨45279668951680467771683885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30186445967786978514455923 45279668951680467771683885)
            ·
              refine ⟨16979875856880175414381457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45279668951680467771683885 16979875856880175414381457)
              ·
                refine ⟨12734906892660131560786093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16979875856880175414381457 12734906892660131560786093)
                ·
                  refine ⟨4775590084747549335294785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12734906892660131560786093 4775590084747549335294785)
                  ·
                    refine ⟨3581692563560662001471089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4775590084747549335294785 3581692563560662001471089)
                    ·
                      refine ⟨2686269422670496501103317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3581692563560662001471089 2686269422670496501103317)
                      ·
                        rfl

theorem cell23_5231491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 2, 2].length) (baseStart_5231491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231491 prefixEnd_5231491 := by exact prefixLift 5231491
  have htrace : WordTrace (prefixWord ++ tailWord_5231491) baseStart_5231491 baseEnd_5231491 := by
    simpa [prefixWord, tailWord_5231491, baseEnd_5231491] using wordTrace_append hprefix tailTrace_5231491
  have hstable : (prefixWord ++ tailWord_5231491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231491).length < 2 ^ (prefixWord ++ tailWord_5231491).sum := by decide
  have hdescent : baseEnd_5231491 < baseStart_5231491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231507 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 3]
def baseStart_5231507 : Nat := 118140960795 + 5231507 * 2 ^ 59
def prefixEnd_5231507 : Nat := 4983230072969 + 3 ^ 40 * 5231507 * 2
def baseEnd_5231507 : Nat := 2686277638360968438503243

theorem tailTrace_5231507 : CollatzResearch.WordTrace tailWord_5231507 prefixEnd_5231507 2686277638360968438503243 := by
  unfold tailWord_5231507
  simp only [CollatzResearch.WordTrace]
  refine ⟨190808735858151084107908775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127205823905434056071939183 190808735858151084107908775)
  ·
    refine ⟨286213103787226626161863163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190808735858151084107908775 286213103787226626161863163)
    ·
      refine ⟨429319655680839939242794745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286213103787226626161863163 429319655680839939242794745)
      ·
        refine ⟨321989741760629954432096059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429319655680839939242794745 321989741760629954432096059)
        ·
          refine ⟨482984612640944931648144089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321989741760629954432096059 482984612640944931648144089)
          ·
            refine ⟨362238459480708698736108067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 482984612640944931648144089 362238459480708698736108067)
            ·
              refine ⟨543357689221063048104162101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362238459480708698736108067 543357689221063048104162101)
              ·
                refine ⟨50939783364474660759765197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 543357689221063048104162101 50939783364474660759765197)
                ·
                  refine ⟨19102418761677997784911949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50939783364474660759765197 19102418761677997784911949)
                  ·
                    refine ⟨7163407035629249169341981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19102418761677997784911949 7163407035629249169341981)
                    ·
                      refine ⟨2686277638360968438503243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7163407035629249169341981 2686277638360968438503243)
                      ·
                        rfl

theorem cell23_5231507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 3].length) (baseStart_5231507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231507 prefixEnd_5231507 := by exact prefixLift 5231507
  have htrace : WordTrace (prefixWord ++ tailWord_5231507) baseStart_5231507 baseEnd_5231507 := by
    simpa [prefixWord, tailWord_5231507, baseEnd_5231507] using wordTrace_append hprefix tailTrace_5231507
  have hstable : (prefixWord ++ tailWord_5231507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231507).length < 2 ^ (prefixWord ++ tailWord_5231507).sum := by decide
  have hdescent : baseEnd_5231507 < baseStart_5231507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231542 : List Nat := [5, 1, 4, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_5231542 : Nat := 118140960795 + 5231542 * 2 ^ 59
def prefixEnd_5231542 : Nat := 4983230072969 + 3 ^ 40 * 5231542 * 2
def baseEnd_5231542 : Nat := 2686295610183875801565583

theorem tailTrace_5231542 : CollatzResearch.WordTrace tailWord_5231542 prefixEnd_5231542 2686295610183875801565583 := by
  unfold tailWord_5231542
  simp only [CollatzResearch.WordTrace]
  refine ⟨11925625775814017817839555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127206674942016190056955253 11925625775814017817839555)
  ·
    refine ⟨17888438663721026726759333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11925625775814017817839555 17888438663721026726759333)
    ·
      refine ⟨3354082249447692511267375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17888438663721026726759333 3354082249447692511267375)
      ·
        refine ⟨5031123374171538766901063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3354082249447692511267375 5031123374171538766901063)
        ·
          refine ⟨7546685061257308150351595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5031123374171538766901063 7546685061257308150351595)
          ·
            refine ⟨11320027591885962225527393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7546685061257308150351595 11320027591885962225527393)
            ·
              refine ⟨8490020693914471669145545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11320027591885962225527393 8490020693914471669145545)
              ·
                refine ⟨6367515520435853751859159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8490020693914471669145545 6367515520435853751859159)
                ·
                  refine ⟨9551273280653780627788739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6367515520435853751859159 9551273280653780627788739)
                  ·
                    refine ⟨14326909920980670941683109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9551273280653780627788739 14326909920980670941683109)
                    ·
                      refine ⟨2686295610183875801565583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14326909920980670941683109 2686295610183875801565583)
                      ·
                        rfl

theorem cell23_5231542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_5231542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231542 prefixEnd_5231542 := by exact prefixLift 5231542
  have htrace : WordTrace (prefixWord ++ tailWord_5231542) baseStart_5231542 baseEnd_5231542 := by
    simpa [prefixWord, tailWord_5231542, baseEnd_5231542] using wordTrace_append hprefix tailTrace_5231542
  have hstable : (prefixWord ++ tailWord_5231542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231542).length < 2 ^ (prefixWord ++ tailWord_5231542).sum := by decide
  have hdescent : baseEnd_5231542 < baseStart_5231542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231565 : List Nat := [1, 6, 3, 1, 2, 1, 9]
def baseStart_5231565 : Nat := 118140960795 + 5231565 * 2 ^ 59
def prefixEnd_5231565 : Nat := 4983230072969 + 3 ^ 40 * 5231565 * 2
def baseEnd_5231565 : Nat := 33164289138752212488617

theorem tailTrace_5231565 : CollatzResearch.WordTrace tailWord_5231565 prefixEnd_5231565 33164289138752212488617 := by
  unfold tailWord_5231565
  simp only [CollatzResearch.WordTrace]
  refine ⟨190810851291940960013520149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127207234194627306675680099 190810851291940960013520149)
  ·
    refine ⟨8944258654309732500633757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 190810851291940960013520149 8944258654309732500633757)
    ·
      refine ⟨3354096995366149687737659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8944258654309732500633757 3354096995366149687737659)
      ·
        refine ⟨5031145493049224531606489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3354096995366149687737659 5031145493049224531606489)
        ·
          refine ⟨3773359119786918398704867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5031145493049224531606489 3773359119786918398704867)
          ·
            refine ⟨5660038679680377598057301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3773359119786918398704867 5660038679680377598057301)
            ·
              refine ⟨33164289138752212488617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5660038679680377598057301 33164289138752212488617)
              ·
                rfl

theorem cell23_5231565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 9].length) (baseStart_5231565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231565 prefixEnd_5231565 := by exact prefixLift 5231565
  have htrace : WordTrace (prefixWord ++ tailWord_5231565) baseStart_5231565 baseEnd_5231565 := by
    simpa [prefixWord, tailWord_5231565, baseEnd_5231565] using wordTrace_append hprefix tailTrace_5231565
  have hstable : (prefixWord ++ tailWord_5231565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231565).length < 2 ^ (prefixWord ++ tailWord_5231565).sum := by decide
  have hdescent : baseEnd_5231565 < baseStart_5231565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231567 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 5]
def baseStart_5231567 : Nat := 118140960795 + 5231567 * 2 ^ 59
def prefixEnd_5231567 : Nat := 4983230072969 + 3 ^ 40 * 5231567 * 2
def baseEnd_5231567 : Nat := 2686308447200238203752967

theorem tailTrace_5231567 : CollatzResearch.WordTrace tailWord_5231567 prefixEnd_5231567 2686308447200238203752967 := by
  unfold tailWord_5231567
  simp only [CollatzResearch.WordTrace]
  refine ⟨190810924237933714355092955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127207282825289142903395303 190810924237933714355092955)
  ·
    refine ⟨286216386356900571532639433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190810924237933714355092955 286216386356900571532639433)
    ·
      refine ⟨214662289767675428649479575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286216386356900571532639433 214662289767675428649479575)
      ·
        refine ⟨321993434651513142974219363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214662289767675428649479575 321993434651513142974219363)
        ·
          refine ⟨482990151977269714461329045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321993434651513142974219363 482990151977269714461329045)
          ·
            refine ⟨22640163373934517865374799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 482990151977269714461329045 22640163373934517865374799)
            ·
              refine ⟨33960245060901776798062199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22640163373934517865374799 33960245060901776798062199)
              ·
                refine ⟨50940367591352665197093299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33960245060901776798062199 50940367591352665197093299)
                ·
                  refine ⟨76410551387028997795639949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50940367591352665197093299 76410551387028997795639949)
                  ·
                    refine ⟨28653956770135874173364981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76410551387028997795639949 28653956770135874173364981)
                    ·
                      refine ⟨2686308447200238203752967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28653956770135874173364981 2686308447200238203752967)
                      ·
                        rfl

theorem cell23_5231567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 5].length) (baseStart_5231567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231567 prefixEnd_5231567 := by exact prefixLift 5231567
  have htrace : WordTrace (prefixWord ++ tailWord_5231567) baseStart_5231567 baseEnd_5231567 := by
    simpa [prefixWord, tailWord_5231567, baseEnd_5231567] using wordTrace_append hprefix tailTrace_5231567
  have hstable : (prefixWord ++ tailWord_5231567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231567).length < 2 ^ (prefixWord ++ tailWord_5231567).sum := by decide
  have hdescent : baseEnd_5231567 < baseStart_5231567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231602 : List Nat := [3, 2, 1, 5, 1, 2, 1, 2, 1, 3, 2]
def baseStart_5231602 : Nat := 118140960795 + 5231602 * 2 ^ 59
def prefixEnd_5231602 : Nat := 4983230072969 + 3 ^ 40 * 5231602 * 2
def baseEnd_5231602 : Nat := 2686326419023145566815307

theorem tailTrace_5231602 : CollatzResearch.WordTrace tailWord_5231602 prefixEnd_5231602 2686326419023145566815307 := by
  unfold tailWord_5231602
  simp only [CollatzResearch.WordTrace]
  refine ⟨47703050198201728833154265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127208133861871276888411373 47703050198201728833154265)
  ·
    refine ⟨35777287648651296624865699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47703050198201728833154265 35777287648651296624865699)
    ·
      refine ⟨53665931472976944937298549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35777287648651296624865699 53665931472976944937298549)
      ·
        refine ⟨5031181075591588587871739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53665931472976944937298549 5031181075591588587871739)
        ·
          refine ⟨7546771613387382881807609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5031181075591588587871739 7546771613387382881807609)
          ·
            refine ⟨5660078710040537161355707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7546771613387382881807609 5660078710040537161355707)
            ·
              refine ⟨8490118065060805742033561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5660078710040537161355707 8490118065060805742033561)
              ·
                refine ⟨6367588548795604306525171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8490118065060805742033561 6367588548795604306525171)
                ·
                  refine ⟨9551382823193406459787757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6367588548795604306525171 9551382823193406459787757)
                  ·
                    refine ⟨3581768558697527422420409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9551382823193406459787757 3581768558697527422420409)
                    ·
                      refine ⟨2686326419023145566815307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3581768558697527422420409 2686326419023145566815307)
                      ·
                        rfl

theorem cell23_5231602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_5231602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231602 prefixEnd_5231602 := by exact prefixLift 5231602
  have htrace : WordTrace (prefixWord ++ tailWord_5231602) baseStart_5231602 baseEnd_5231602 := by
    simpa [prefixWord, tailWord_5231602, baseEnd_5231602] using wordTrace_append hprefix tailTrace_5231602
  have hstable : (prefixWord ++ tailWord_5231602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231602).length < 2 ^ (prefixWord ++ tailWord_5231602).sum := by decide
  have hdescent : baseEnd_5231602 < baseStart_5231602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231648 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 2, 3, 3]
def baseStart_5231648 : Nat := 118140960795 + 5231648 * 2 ^ 59
def prefixEnd_5231648 : Nat := 4983230072969 + 3 ^ 40 * 5231648 * 2
def baseEnd_5231648 : Nat := 2686350039133252386840095

theorem tailTrace_5231648 : CollatzResearch.WordTrace tailWord_5231648 prefixEnd_5231648 2686350039133252386840095 := by
  unfold tailWord_5231648
  simp only [CollatzResearch.WordTrace]
  refine ⟨95406939275320132594395799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127209252367093510125861065 95406939275320132594395799)
  ·
    refine ⟨143110408912980198891593699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95406939275320132594395799 143110408912980198891593699)
    ·
      refine ⟨214665613369470298337390549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143110408912980198891593699 214665613369470298337390549)
      ·
        refine ⟨5031225313346960117282591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 214665613369470298337390549 5031225313346960117282591)
        ·
          refine ⟨7546837970020440175923887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5031225313346960117282591 7546837970020440175923887)
          ·
            refine ⟨11320256955030660263885831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7546837970020440175923887 11320256955030660263885831)
            ·
              refine ⟨16980385432545990395828747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11320256955030660263885831 16980385432545990395828747)
              ·
                refine ⟨25470578148818985593743121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16980385432545990395828747 25470578148818985593743121)
                ·
                  refine ⟨19102933611614239195307341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25470578148818985593743121 19102933611614239195307341)
                  ·
                    refine ⟨7163600104355339698240253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19102933611614239195307341 7163600104355339698240253)
                    ·
                      refine ⟨2686350039133252386840095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7163600104355339698240253 2686350039133252386840095)
                      ·
                        rfl

theorem cell23_5231648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_5231648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231648 prefixEnd_5231648 := by exact prefixLift 5231648
  have htrace : WordTrace (prefixWord ++ tailWord_5231648) baseStart_5231648 baseEnd_5231648 := by
    simpa [prefixWord, tailWord_5231648, baseEnd_5231648] using wordTrace_append hprefix tailTrace_5231648
  have hstable : (prefixWord ++ tailWord_5231648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231648).length < 2 ^ (prefixWord ++ tailWord_5231648).sum := by decide
  have hdescent : baseEnd_5231648 < baseStart_5231648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231668 : List Nat := [2, 5, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_5231668 : Nat := 118140960795 + 5231668 * 2 ^ 59
def prefixEnd_5231668 : Nat := 4983230072969 + 3 ^ 40 * 5231668 * 2
def baseEnd_5231668 : Nat := 895453436248780769530001

theorem tailTrace_5231668 : CollatzResearch.WordTrace tailWord_5231668 prefixEnd_5231668 895453436248780769530001 := by
  unfold tailWord_5231668
  simp only [CollatzResearch.WordTrace]
  refine ⟨95407304005283904302259829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127209738673711872403013105 95407304005283904302259829)
  ·
    refine ⟨8944434750495366028336859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95407304005283904302259829 8944434750495366028336859)
    ·
      refine ⟨13416652125743049042505289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8944434750495366028336859 13416652125743049042505289)
      ·
        refine ⟨10062489094307286781878967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13416652125743049042505289 10062489094307286781878967)
        ·
          refine ⟨15093733641460930172818451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10062489094307286781878967 15093733641460930172818451)
          ·
            refine ⟨22640600462191395259227677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15093733641460930172818451 22640600462191395259227677)
            ·
              refine ⟨8490225173321773222210379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22640600462191395259227677 8490225173321773222210379)
              ·
                refine ⟨12735337759982659833315569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8490225173321773222210379 12735337759982659833315569)
                ·
                  refine ⟨9551503319986994874986677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12735337759982659833315569 9551503319986994874986677)
                  ·
                    refine ⟨895453436248780769530001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9551503319986994874986677 895453436248780769530001)
                    ·
                      rfl

theorem cell23_5231668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_5231668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231668 prefixEnd_5231668 := by exact prefixLift 5231668
  have htrace : WordTrace (prefixWord ++ tailWord_5231668) baseStart_5231668 baseEnd_5231668 := by
    simpa [prefixWord, tailWord_5231668, baseEnd_5231668] using wordTrace_append hprefix tailTrace_5231668
  have hstable : (prefixWord ++ tailWord_5231668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231668).length < 2 ^ (prefixWord ++ tailWord_5231668).sum := by decide
  have hdescent : baseEnd_5231668 < baseStart_5231668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231694 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 8]
def baseStart_5231694 : Nat := 118140960795 + 5231694 * 2 ^ 59
def prefixEnd_5231694 : Nat := 4983230072969 + 3 ^ 40 * 5231694 * 2
def baseEnd_5231694 : Nat := 298485962138151022984987

theorem tailTrace_5231694 : CollatzResearch.WordTrace tailWord_5231694 prefixEnd_5231694 298485962138151022984987 := by
  unfold tailWord_5231694
  simp only [CollatzResearch.WordTrace]
  refine ⟨23851944538559201880620767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127210370872315743363310757 23851944538559201880620767)
  ·
    refine ⟨35777916807838802820931151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23851944538559201880620767 35777916807838802820931151)
    ·
      refine ⟨53666875211758204231396727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35777916807838802820931151 53666875211758204231396727)
      ·
        refine ⟨80500312817637306347095091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53666875211758204231396727 80500312817637306347095091)
        ·
          refine ⟨120750469226455959520642637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80500312817637306347095091 120750469226455959520642637)
          ·
            refine ⟨45281425959920984820240989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120750469226455959520642637 45281425959920984820240989)
            ·
              refine ⟨16980534734970369307590371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45281425959920984820240989 16980534734970369307590371)
              ·
                refine ⟨25470802102455553961385557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16980534734970369307590371 25470802102455553961385557)
                ·
                  refine ⟨298485962138151022984987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25470802102455553961385557 298485962138151022984987)
                  ·
                    rfl

theorem cell23_5231694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_5231694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231694 prefixEnd_5231694 := by exact prefixLift 5231694
  have htrace : WordTrace (prefixWord ++ tailWord_5231694) baseStart_5231694 baseEnd_5231694 := by
    simpa [prefixWord, tailWord_5231694, baseEnd_5231694] using wordTrace_append hprefix tailTrace_5231694
  have hstable : (prefixWord ++ tailWord_5231694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231694).length < 2 ^ (prefixWord ++ tailWord_5231694).sum := by decide
  have hdescent : baseEnd_5231694 < baseStart_5231694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231698 : List Nat := [3, 2, 2, 1, 3, 2, 2, 1, 3, 4]
def baseStart_5231698 : Nat := 118140960795 + 5231698 * 2 ^ 59
def prefixEnd_5231698 : Nat := 4983230072969 + 3 ^ 40 * 5231698 * 2
def baseEnd_5231698 : Nat := 895458571055325730404955

theorem tailTrace_5231698 : CollatzResearch.WordTrace tailWord_5231698 prefixEnd_5231698 895458571055325730404955 := by
  unfold tailWord_5231698
  simp only [CollatzResearch.WordTrace]
  refine ⟨47703925550114780932027937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127210468133639415818741165 47703925550114780932027937)
  ·
    refine ⟨35777944162586085699020953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47703925550114780932027937 35777944162586085699020953)
    ·
      refine ⟨26833458121939564274265715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35777944162586085699020953 26833458121939564274265715)
      ·
        refine ⟨40250187182909346411398573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26833458121939564274265715 40250187182909346411398573)
        ·
          refine ⟨15093820193591004904274465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40250187182909346411398573 15093820193591004904274465)
          ·
            refine ⟨11320365145193253678205849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15093820193591004904274465 11320365145193253678205849)
            ·
              refine ⟨8490273858894940258654387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11320365145193253678205849 8490273858894940258654387)
              ·
                refine ⟨12735410788342410387981581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8490273858894940258654387 12735410788342410387981581)
                ·
                  refine ⟨4775779045628403895493093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12735410788342410387981581 4775779045628403895493093)
                  ·
                    refine ⟨895458571055325730404955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4775779045628403895493093 895458571055325730404955)
                    ·
                      rfl

theorem cell23_5231698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_5231698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231698 prefixEnd_5231698 := by exact prefixLift 5231698
  have htrace : WordTrace (prefixWord ++ tailWord_5231698) baseStart_5231698 baseEnd_5231698 := by
    simpa [prefixWord, tailWord_5231698, baseEnd_5231698] using wordTrace_append hprefix tailTrace_5231698
  have hstable : (prefixWord ++ tailWord_5231698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231698).length < 2 ^ (prefixWord ++ tailWord_5231698).sum := by decide
  have hdescent : baseEnd_5231698 < baseStart_5231698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231711 : List Nat := [1, 1, 2, 3, 1, 1, 7, 1, 6]
def baseStart_5231711 : Nat := 118140960795 + 5231711 * 2 ^ 59
def prefixEnd_5231711 : Nat := 4983230072969 + 3 ^ 40 * 5231711 * 2
def baseEnd_5231711 : Nat := 298486932046053960039145

theorem tailTrace_5231711 : CollatzResearch.WordTrace tailWord_5231711 prefixEnd_5231711 298486932046053960039145 := by
  unfold tailWord_5231711
  simp only [CollatzResearch.WordTrace]
  refine ⟨190816176349412026948334987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127210784232941351298889991 190816176349412026948334987)
  ·
    refine ⟨286224264524118040422502481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190816176349412026948334987 286224264524118040422502481)
    ·
      refine ⟨214668198393088530316876861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286224264524118040422502481 214668198393088530316876861)
      ·
        refine ⟨80500574397408198868828823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214668198393088530316876861 80500574397408198868828823)
        ·
          refine ⟨120750861596112298303243235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80500574397408198868828823 120750861596112298303243235)
          ·
            refine ⟨181126292394168447454864853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120750861596112298303243235 181126292394168447454864853)
            ·
              refine ⟨4245147477988322987223395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 181126292394168447454864853 4245147477988322987223395)
              ·
                refine ⟨6367721216982484480835093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4245147477988322987223395 6367721216982484480835093)
                ·
                  refine ⟨298486932046053960039145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6367721216982484480835093 298486932046053960039145)
                  ·
                    rfl

theorem cell23_5231711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 6].length) (baseStart_5231711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231711 prefixEnd_5231711 := by exact prefixLift 5231711
  have htrace : WordTrace (prefixWord ++ tailWord_5231711) baseStart_5231711 baseEnd_5231711 := by
    simpa [prefixWord, tailWord_5231711, baseEnd_5231711] using wordTrace_append hprefix tailTrace_5231711
  have hstable : (prefixWord ++ tailWord_5231711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231711).length < 2 ^ (prefixWord ++ tailWord_5231711).sum := by decide
  have hdescent : baseEnd_5231711 < baseStart_5231711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231731 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 8, 3, 2]
def baseStart_5231731 : Nat := 118140960795 + 5231731 * 2 ^ 59
def prefixEnd_5231731 : Nat := 4983230072969 + 3 ^ 40 * 5231731 * 2
def baseEnd_5231731 : Nat := 2686392658027575562102213

theorem tailTrace_5231731 : CollatzResearch.WordTrace tailWord_5231731 prefixEnd_5231731 2686392658027575562102213 := by
  unfold tailWord_5231731
  simp only [CollatzResearch.WordTrace]
  refine ⟨190816905809339570364063047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127211270539559713576042031 190816905809339570364063047)
  ·
    refine ⟨286225358714009355546094571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190816905809339570364063047 286225358714009355546094571)
    ·
      refine ⟨429338038071014033319141857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286225358714009355546094571 429338038071014033319141857)
      ·
        refine ⟨322003528553260524989356393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429338038071014033319141857 322003528553260524989356393)
        ·
          refine ⟨241502646414945393742017295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322003528553260524989356393 241502646414945393742017295)
          ·
            refine ⟨362253969622418090613025943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241502646414945393742017295 362253969622418090613025943)
            ·
              refine ⟨543380954433627135919538915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362253969622418090613025943 543380954433627135919538915)
              ·
                refine ⟨815071431650440703879308373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543380954433627135919538915 815071431650440703879308373)
                ·
                  refine ⟨9551618339653601998585645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 815071431650440703879308373 9551618339653601998585645)
                  ·
                    refine ⟨3581856877370100749469617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9551618339653601998585645 3581856877370100749469617)
                    ·
                      refine ⟨2686392658027575562102213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3581856877370100749469617 2686392658027575562102213)
                      ·
                        rfl

theorem cell23_5231731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 3, 2].length) (baseStart_5231731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231731 prefixEnd_5231731 := by exact prefixLift 5231731
  have htrace : WordTrace (prefixWord ++ tailWord_5231731) baseStart_5231731 baseEnd_5231731 := by
    simpa [prefixWord, tailWord_5231731, baseEnd_5231731] using wordTrace_append hprefix tailTrace_5231731
  have hstable : (prefixWord ++ tailWord_5231731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231731).length < 2 ^ (prefixWord ++ tailWord_5231731).sum := by decide
  have hdescent : baseEnd_5231731 < baseStart_5231731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231741 : List Nat := [1, 4, 1, 1, 3, 1, 1, 5, 1, 5]
def baseStart_5231741 : Nat := 118140960795 + 5231741 * 2 ^ 59
def prefixEnd_5231741 : Nat := 4983230072969 + 3 ^ 40 * 5231741 * 2
def baseEnd_5231741 : Nat := 895465930944706840992389

theorem tailTrace_5231741 : CollatzResearch.WordTrace tailWord_5231741 prefixEnd_5231741 895465930944706840992389 := by
  unfold tailWord_5231741
  simp only [CollatzResearch.WordTrace]
  refine ⟨190817270539303342071927077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127211513692868894714618051 190817270539303342071927077)
  ·
    refine ⟨35778238226119376638486327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190817270539303342071927077 35778238226119376638486327)
    ·
      refine ⟨53667357339179064957729491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35778238226119376638486327 53667357339179064957729491)
      ·
        refine ⟨80501036008768597436594237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53667357339179064957729491 80501036008768597436594237)
        ·
          refine ⟨30187888503288224038722839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80501036008768597436594237 30187888503288224038722839)
          ·
            refine ⟨45281832754932336058084259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30187888503288224038722839 45281832754932336058084259)
            ·
              refine ⟨67922749132398504087126389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45281832754932336058084259 67922749132398504087126389)
              ·
                refine ⟨6367757731162359758168099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67922749132398504087126389 6367757731162359758168099)
                ·
                  refine ⟨9551636596743539637252149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6367757731162359758168099 9551636596743539637252149)
                  ·
                    refine ⟨895465930944706840992389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9551636596743539637252149 895465930944706840992389)
                    ·
                      rfl

theorem cell23_5231741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_5231741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231741 prefixEnd_5231741 := by exact prefixLift 5231741
  have htrace : WordTrace (prefixWord ++ tailWord_5231741) baseStart_5231741 baseEnd_5231741 := by
    simpa [prefixWord, tailWord_5231741, baseEnd_5231741] using wordTrace_append hprefix tailTrace_5231741
  have hstable : (prefixWord ++ tailWord_5231741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231741).length < 2 ^ (prefixWord ++ tailWord_5231741).sum := by decide
  have hdescent : baseEnd_5231741 < baseStart_5231741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
