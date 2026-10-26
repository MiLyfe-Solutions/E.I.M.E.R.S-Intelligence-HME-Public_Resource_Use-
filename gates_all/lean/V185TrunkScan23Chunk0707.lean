import V185TrunkScan23Chunk0706

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4180529 : List Nat := [1, 2, 2, 3, 1, 1, 4, 2, 1, 3, 3]
def baseStart_4180529 : Nat := 118140960795 + 4180529 * 2 ^ 59
def prefixEnd_4180529 : Nat := 4983230072969 + 3 ^ 40 * 4180529 * 2
def baseEnd_4180529 : Nat := 2146620767059979394761603

theorem tailTrace_4180529 : CollatzResearch.WordTrace tailWord_4180529 prefixEnd_4180529 2146620767059979394761603 := by
  unfold tailWord_4180529
  simp only [CollatzResearch.WordTrace]
  refine ⟨152476419071664885355656641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101650946047776590237104427 152476419071664885355656641)
  ·
    refine ⟨114357314303748664016742481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152476419071664885355656641 114357314303748664016742481)
    ·
      refine ⟨85767985727811498012556861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114357314303748664016742481 85767985727811498012556861)
      ·
        refine ⟨32162994647929311754708823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85767985727811498012556861 32162994647929311754708823)
        ·
          refine ⟨48244491971893967632063235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32162994647929311754708823 48244491971893967632063235)
          ·
            refine ⟨72366737957840951448094853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48244491971893967632063235 72366737957840951448094853)
            ·
              refine ⟨13568763367095178396517785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72366737957840951448094853 13568763367095178396517785)
              ·
                refine ⟨10176572525321383797388339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13568763367095178396517785 10176572525321383797388339)
                ·
                  refine ⟨15264858787982075696082509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10176572525321383797388339 15264858787982075696082509)
                  ·
                    refine ⟨5724322045493278386030941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15264858787982075696082509 5724322045493278386030941)
                    ·
                      refine ⟨2146620767059979394761603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5724322045493278386030941 2146620767059979394761603)
                      ·
                        rfl

theorem cell23_4180529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_4180529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180529 prefixEnd_4180529 := by exact prefixLift 4180529
  have htrace : WordTrace (prefixWord ++ tailWord_4180529) baseStart_4180529 baseEnd_4180529 := by
    simpa [prefixWord, tailWord_4180529, baseEnd_4180529] using wordTrace_append hprefix tailTrace_4180529
  have hstable : (prefixWord ++ tailWord_4180529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180529).length < 2 ^ (prefixWord ++ tailWord_4180529).sum := by decide
  have hdescent : baseEnd_4180529 < baseStart_4180529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180552 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 1, 5, 4]
def baseStart_4180552 : Nat := 118140960795 + 4180552 * 2 ^ 59
def prefixEnd_4180552 : Nat := 4983230072969 + 3 ^ 40 * 4180552 * 2
def baseEnd_4180552 : Nat := 2146632577115032804773997

theorem tailTrace_4180552 : CollatzResearch.WordTrace tailWord_4180552 prefixEnd_4180552 2146632577115032804773997 := by
  unfold tailWord_4180552
  simp only [CollatzResearch.WordTrace]
  refine ⟨76238628975290780141871955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101651505300387706855829273 76238628975290780141871955)
  ·
    refine ⟨114357943462936170212807933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76238628975290780141871955 114357943462936170212807933)
    ·
      refine ⟨42884228798601063829802975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114357943462936170212807933 42884228798601063829802975)
      ·
        refine ⟨64326343197901595744704463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42884228798601063829802975 64326343197901595744704463)
        ·
          refine ⟨96489514796852393617056695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64326343197901595744704463 96489514796852393617056695)
          ·
            refine ⟨144734272195278590425585043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96489514796852393617056695 144734272195278590425585043)
            ·
              refine ⟨217101408292917885638377565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144734272195278590425585043 217101408292917885638377565)
              ·
                refine ⟨81413028109844207114391587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217101408292917885638377565 81413028109844207114391587)
                ·
                  refine ⟨122119542164766310671587381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81413028109844207114391587 122119542164766310671587381)
                  ·
                    refine ⟨11448707077946841625461317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 122119542164766310671587381 11448707077946841625461317)
                    ·
                      refine ⟨2146632577115032804773997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11448707077946841625461317 2146632577115032804773997)
                      ·
                        rfl

theorem cell23_4180552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_4180552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180552 prefixEnd_4180552 := by exact prefixLift 4180552
  have htrace : WordTrace (prefixWord ++ tailWord_4180552) baseStart_4180552 baseEnd_4180552 := by
    simpa [prefixWord, tailWord_4180552, baseEnd_4180552] using wordTrace_append hprefix tailTrace_4180552
  have hstable : (prefixWord ++ tailWord_4180552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180552).length < 2 ^ (prefixWord ++ tailWord_4180552).sum := by decide
  have hdescent : baseEnd_4180552 < baseStart_4180552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180586 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 3, 4, 2]
def baseStart_4180586 : Nat := 118140960795 + 4180586 * 2 ^ 59
def prefixEnd_4180586 : Nat := 4983230072969 + 3 ^ 40 * 4180586 * 2
def baseEnd_4180586 : Nat := 2146650035457285671748841

theorem tailTrace_4180586 : CollatzResearch.WordTrace tailWord_4180586 prefixEnd_4180586 2146650035457285671748841 := by
  unfold tailWord_4180586
  simp only [CollatzResearch.WordTrace]
  refine ⟨38119624508114596022620403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101652332021638922726987741 38119624508114596022620403)
  ·
    refine ⟨57179436762171894033930605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38119624508114596022620403 57179436762171894033930605)
    ·
      refine ⟨21442288785814460262723977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57179436762171894033930605 21442288785814460262723977)
      ·
        refine ⟨16081716589360845197042983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21442288785814460262723977 16081716589360845197042983)
        ·
          refine ⟨24122574884041267795564475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16081716589360845197042983 24122574884041267795564475)
          ·
            refine ⟨36183862326061901693346713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24122574884041267795564475 36183862326061901693346713)
            ·
              refine ⟨27137896744546426270010035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36183862326061901693346713 27137896744546426270010035)
              ·
                refine ⟨40706845116819639405015053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27137896744546426270010035 40706845116819639405015053)
                ·
                  refine ⟨15265066918807364776880645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40706845116819639405015053 15265066918807364776880645)
                  ·
                    refine ⟨2862200047276380895665121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15265066918807364776880645 2862200047276380895665121)
                    ·
                      refine ⟨2146650035457285671748841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2862200047276380895665121 2146650035457285671748841)
                      ·
                        rfl

theorem cell23_4180586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_4180586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180586 prefixEnd_4180586 := by exact prefixLift 4180586
  have htrace : WordTrace (prefixWord ++ tailWord_4180586) baseStart_4180586 baseEnd_4180586 := by
    simpa [prefixWord, tailWord_4180586, baseEnd_4180586] using wordTrace_append hprefix tailTrace_4180586
  have hstable : (prefixWord ++ tailWord_4180586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180586).length < 2 ^ (prefixWord ++ tailWord_4180586).sum := by decide
  have hdescent : baseEnd_4180586 < baseStart_4180586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180589 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_4180589 : Nat := 118140960795 + 4180589 * 2 ^ 59
def prefixEnd_4180589 : Nat := 4983230072969 + 3 ^ 40 * 4180589 * 2
def baseEnd_4180589 : Nat := 2146651575899249160011327

theorem tailTrace_4180589 : CollatzResearch.WordTrace tailWord_4180589 prefixEnd_4180589 2146651575899249160011327 := by
  unfold tailWord_4180589
  simp only [CollatzResearch.WordTrace]
  refine ⟨152478607451447515602840821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101652404967631677068560547 152478607451447515602840821)
  ·
    refine ⟨14294869448573204587766327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152478607451447515602840821 14294869448573204587766327)
    ·
      refine ⟨21442304172859806881649491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14294869448573204587766327 21442304172859806881649491)
      ·
        refine ⟨32163456259289710322474237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21442304172859806881649491 32163456259289710322474237)
        ·
          refine ⟨12061296097233641370927839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32163456259289710322474237 12061296097233641370927839)
          ·
            refine ⟨18091944145850462056391759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12061296097233641370927839 18091944145850462056391759)
            ·
              refine ⟨27137916218775693084587639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18091944145850462056391759 27137916218775693084587639)
              ·
                refine ⟨40706874328163539626881459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27137916218775693084587639 40706874328163539626881459)
                ·
                  refine ⟨61060311492245309440322189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40706874328163539626881459 61060311492245309440322189)
                  ·
                    refine ⟨22897616809591991040120821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61060311492245309440322189 22897616809591991040120821)
                    ·
                      refine ⟨2146651575899249160011327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22897616809591991040120821 2146651575899249160011327)
                      ·
                        rfl

theorem cell23_4180589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_4180589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180589 prefixEnd_4180589 := by exact prefixLift 4180589
  have htrace : WordTrace (prefixWord ++ tailWord_4180589) baseStart_4180589 baseEnd_4180589 := by
    simpa [prefixWord, tailWord_4180589, baseEnd_4180589] using wordTrace_append hprefix tailTrace_4180589
  have hstable : (prefixWord ++ tailWord_4180589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180589).length < 2 ^ (prefixWord ++ tailWord_4180589).sum := by decide
  have hdescent : baseEnd_4180589 < baseStart_4180589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180686 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 5, 4]
def baseStart_4180686 : Nat := 118140960795 + 4180686 * 2 ^ 59
def prefixEnd_4180686 : Nat := 4983230072969 + 3 ^ 40 * 4180686 * 2
def baseEnd_4180686 : Nat := 715567127840911760166127

theorem tailTrace_4180686 : CollatzResearch.WordTrace tailWord_4180686 prefixEnd_4180686 715567127840911760166127 := by
  unfold tailWord_4180686
  simp only [CollatzResearch.WordTrace]
  refine ⟨19060268166512012646140239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101654763554730734112747941 19060268166512012646140239)
  ·
    refine ⟨28590402249768018969210359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19060268166512012646140239 28590402249768018969210359)
    ·
      refine ⟨42885603374652028453815539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28590402249768018969210359 42885603374652028453815539)
      ·
        refine ⟨64328405061978042680723309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42885603374652028453815539 64328405061978042680723309)
        ·
          refine ⟨24123151898241766005271241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64328405061978042680723309 24123151898241766005271241)
          ·
            refine ⟨18092363923681324503953431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24123151898241766005271241 18092363923681324503953431)
            ·
              refine ⟨27138545885521986755930147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18092363923681324503953431 27138545885521986755930147)
              ·
                refine ⟨40707818828282980133895221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27138545885521986755930147 40707818828282980133895221)
                ·
                  refine ⟨3816358015151529387552677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40707818828282980133895221 3816358015151529387552677)
                  ·
                    refine ⟨715567127840911760166127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3816358015151529387552677 715567127840911760166127)
                    ·
                      rfl

theorem cell23_4180686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_4180686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180686 prefixEnd_4180686 := by exact prefixLift 4180686
  have htrace : WordTrace (prefixWord ++ tailWord_4180686) baseStart_4180686 baseEnd_4180686 := by
    simpa [prefixWord, tailWord_4180686, baseEnd_4180686] using wordTrace_append hprefix tailTrace_4180686
  have hstable : (prefixWord ++ tailWord_4180686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180686).length < 2 ^ (prefixWord ++ tailWord_4180686).sum := by decide
  have hdescent : baseEnd_4180686 < baseStart_4180686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180690 : List Nat := [3, 2, 2, 2, 4, 1, 1, 1, 2, 5]
def baseStart_4180690 : Nat := 118140960795 + 4180690 * 2 ^ 59
def prefixEnd_4180690 : Nat := 4983230072969 + 3 ^ 40 * 4180690 * 2
def baseEnd_4180690 : Nat := 715567812481784421616121

theorem tailTrace_4180690 : CollatzResearch.WordTrace tailWord_4180690 prefixEnd_4180690 715567812481784421616121 := by
  unfold tailWord_4180690
  simp only [CollatzResearch.WordTrace]
  refine ⟨38120572806020402463066881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101654860816054406568178349 38120572806020402463066881)
  ·
    refine ⟨28590429604515301847300161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38120572806020402463066881 28590429604515301847300161)
    ·
      refine ⟨21442822203386476385475121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28590429604515301847300161 21442822203386476385475121)
      ·
        refine ⟨16082116652539857289106341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21442822203386476385475121 16082116652539857289106341)
        ·
          refine ⟨3015396872351223241707439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16082116652539857289106341 3015396872351223241707439)
          ·
            refine ⟨4523095308526834862561159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3015396872351223241707439 4523095308526834862561159)
            ·
              refine ⟨6784642962790252293841739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4523095308526834862561159 6784642962790252293841739)
              ·
                refine ⟨10176964444185378440762609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6784642962790252293841739 10176964444185378440762609)
                ·
                  refine ⟨7632723333139033830571957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10176964444185378440762609 7632723333139033830571957)
                  ·
                    refine ⟨715567812481784421616121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7632723333139033830571957 715567812481784421616121)
                    ·
                      rfl

theorem cell23_4180690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_4180690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180690 prefixEnd_4180690 := by exact prefixLift 4180690
  have htrace : WordTrace (prefixWord ++ tailWord_4180690) baseStart_4180690 baseEnd_4180690 := by
    simpa [prefixWord, tailWord_4180690, baseEnd_4180690] using wordTrace_append hprefix tailTrace_4180690
  have hstable : (prefixWord ++ tailWord_4180690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180690).length < 2 ^ (prefixWord ++ tailWord_4180690).sum := by decide
  have hdescent : baseEnd_4180690 < baseStart_4180690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180693 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 1, 3, 4]
def baseStart_4180693 : Nat := 118140960795 + 4180693 * 2 ^ 59
def prefixEnd_4180693 : Nat := 4983230072969 + 3 ^ 40 * 4180693 * 2
def baseEnd_4180693 : Nat := 2146704977887316753110849

theorem tailTrace_4180693 : CollatzResearch.WordTrace tailWord_4180693 prefixEnd_4180693 2146704977887316753110849 := by
  unfold tailWord_4180693
  simp only [CollatzResearch.WordTrace]
  refine ⟨152482400643070741364626733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101654933762047160909751155 152482400643070741364626733)
  ·
    refine ⟨57180900241151528011735025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152482400643070741364626733 57180900241151528011735025)
    ·
      refine ⟨42885675180863646008801269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57180900241151528011735025 42885675180863646008801269)
      ·
        refine ⟨4020532048205966813325119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42885675180863646008801269 4020532048205966813325119)
        ·
          refine ⟨6030798072308950219987679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4020532048205966813325119 6030798072308950219987679)
          ·
            refine ⟨9046197108463425329981519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6030798072308950219987679 9046197108463425329981519)
            ·
              refine ⟨13569295662695137994972279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9046197108463425329981519 13569295662695137994972279)
              ·
                refine ⟨20353943494042706992458419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13569295662695137994972279 20353943494042706992458419)
                ·
                  refine ⟨30530915241064060488687629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20353943494042706992458419 30530915241064060488687629)
                  ·
                    refine ⟨11449093215399022683257861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30530915241064060488687629 11449093215399022683257861)
                    ·
                      refine ⟨2146704977887316753110849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11449093215399022683257861 2146704977887316753110849)
                      ·
                        rfl

theorem cell23_4180693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_4180693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180693 prefixEnd_4180693 := by exact prefixLift 4180693
  have htrace : WordTrace (prefixWord ++ tailWord_4180693) baseStart_4180693 baseEnd_4180693 := by
    simpa [prefixWord, tailWord_4180693, baseEnd_4180693] using wordTrace_append hprefix tailTrace_4180693
  have hstable : (prefixWord ++ tailWord_4180693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180693).length < 2 ^ (prefixWord ++ tailWord_4180693).sum := by decide
  have hdescent : baseEnd_4180693 < baseStart_4180693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180696 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 1, 4, 3]
def baseStart_4180696 : Nat := 118140960795 + 4180696 * 2 ^ 59
def prefixEnd_4180696 : Nat := 4983230072969 + 3 ^ 40 * 4180696 * 2
def baseEnd_4180696 : Nat := 2146706518329280241373335

theorem tailTrace_4180696 : CollatzResearch.WordTrace tailWord_4180696 prefixEnd_4180696 2146706518329280241373335 := by
  unfold tailWord_4180696
  simp only [CollatzResearch.WordTrace]
  refine ⟨76241255031029936438492971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101655006708039915251323961 76241255031029936438492971)
  ·
    refine ⟨114361882546544904657739457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76241255031029936438492971 114361882546544904657739457)
    ·
      refine ⟨85771411909908678493304593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114361882546544904657739457 85771411909908678493304593)
      ·
        refine ⟨64328558932431508869978445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85771411909908678493304593 64328558932431508869978445)
        ·
          refine ⟨24123209599661815826241917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64328558932431508869978445 24123209599661815826241917)
          ·
            refine ⟨9046203599873180934840719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24123209599661815826241917 9046203599873180934840719)
            ·
              refine ⟨13569305399809771402261079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9046203599873180934840719 13569305399809771402261079)
              ·
                refine ⟨20353958099714657103391619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13569305399809771402261079 20353958099714657103391619)
                ·
                  refine ⟨30530937149571985655087429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20353958099714657103391619 30530937149571985655087429)
                  ·
                    refine ⟨5724550715544747310328893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30530937149571985655087429 5724550715544747310328893)
                    ·
                      refine ⟨2146706518329280241373335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5724550715544747310328893 2146706518329280241373335)
                      ·
                        rfl

theorem cell23_4180696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_4180696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180696 prefixEnd_4180696 := by exact prefixLift 4180696
  have htrace : WordTrace (prefixWord ++ tailWord_4180696) baseStart_4180696 baseEnd_4180696 := by
    simpa [prefixWord, tailWord_4180696, baseEnd_4180696] using wordTrace_append hprefix tailTrace_4180696
  have hstable : (prefixWord ++ tailWord_4180696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180696).length < 2 ^ (prefixWord ++ tailWord_4180696).sum := by decide
  have hdescent : baseEnd_4180696 < baseStart_4180696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180703 : List Nat := [1, 1, 2, 3, 2, 3, 1, 5, 1, 4]
def baseStart_4180703 : Nat := 118140960795 + 4180703 * 2 ^ 59
def prefixEnd_4180703 : Nat := 4983230072969 + 3 ^ 40 * 4180703 * 2
def baseEnd_4180703 : Nat := 715570037564620571328601

theorem tailTrace_4180703 : CollatzResearch.WordTrace tailWord_4180703 prefixEnd_4180703 715570037564620571328601 := by
  unfold tailWord_4180703
  simp only [CollatzResearch.WordTrace]
  refine ⟨152482765373034513072490763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101655176915356342048327175 152482765373034513072490763)
  ·
    refine ⟨228724148059551769608736145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152482765373034513072490763 228724148059551769608736145)
    ·
      refine ⟨171543111044663827206552109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228724148059551769608736145 171543111044663827206552109)
      ·
        refine ⟨64328666641748935202457041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171543111044663827206552109 64328666641748935202457041)
        ·
          refine ⟨48246499981311701401842781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64328666641748935202457041 48246499981311701401842781)
          ·
            refine ⟨18092437492991888025691043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48246499981311701401842781 18092437492991888025691043)
            ·
              refine ⟨27138656239487832038536565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18092437492991888025691043 27138656239487832038536565)
              ·
                refine ⟨2544249022451984253612803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27138656239487832038536565 2544249022451984253612803)
                ·
                  refine ⟨3816373533677976380419205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2544249022451984253612803 3816373533677976380419205)
                  ·
                    refine ⟨715570037564620571328601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3816373533677976380419205 715570037564620571328601)
                    ·
                      rfl

theorem cell23_4180703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 1, 4].length) (baseStart_4180703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180703 prefixEnd_4180703 := by exact prefixLift 4180703
  have htrace : WordTrace (prefixWord ++ tailWord_4180703) baseStart_4180703 baseEnd_4180703 := by
    simpa [prefixWord, tailWord_4180703, baseEnd_4180703] using wordTrace_append hprefix tailTrace_4180703
  have hstable : (prefixWord ++ tailWord_4180703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180703).length < 2 ^ (prefixWord ++ tailWord_4180703).sum := by decide
  have hdescent : baseEnd_4180703 < baseStart_4180703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180719 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 6]
def baseStart_4180719 : Nat := 118140960795 + 4180719 * 2 ^ 59
def prefixEnd_4180719 : Nat := 4983230072969 + 3 ^ 40 * 4180719 * 2
def baseEnd_4180719 : Nat := 2146718328384333651385729

theorem tailTrace_4180719 : CollatzResearch.WordTrace tailWord_4180719 prefixEnd_4180719 2146718328384333651385729 := by
  unfold tailWord_4180719
  simp only [CollatzResearch.WordTrace]
  refine ⟨152483348940976547805073211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101655565960651031870048807 152483348940976547805073211)
  ·
    refine ⟨228725023411464821707609817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152483348940976547805073211 228725023411464821707609817)
    ·
      refine ⟨171543767558598616280707363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228725023411464821707609817 171543767558598616280707363)
      ·
        refine ⟨257315651337897924421061045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171543767558598616280707363 257315651337897924421061045)
        ·
          refine ⟨24123342312927930414474473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257315651337897924421061045 24123342312927930414474473)
          ·
            refine ⟨18092506734695947810855855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24123342312927930414474473 18092506734695947810855855)
            ·
              refine ⟨27138760102043921716283783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18092506734695947810855855 27138760102043921716283783)
              ·
                refine ⟨40708140153065882574425675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27138760102043921716283783 40708140153065882574425675)
                ·
                  refine ⟨61062210229598823861638513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40708140153065882574425675 61062210229598823861638513)
                  ·
                    refine ⟨45796657672199117896228885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61062210229598823861638513 45796657672199117896228885)
                    ·
                      refine ⟨2146718328384333651385729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45796657672199117896228885 2146718328384333651385729)
                      ·
                        rfl

theorem cell23_4180719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 6].length) (baseStart_4180719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180719 prefixEnd_4180719 := by exact prefixLift 4180719
  have htrace : WordTrace (prefixWord ++ tailWord_4180719) baseStart_4180719 baseEnd_4180719 := by
    simpa [prefixWord, tailWord_4180719, baseEnd_4180719] using wordTrace_append hprefix tailTrace_4180719
  have hstable : (prefixWord ++ tailWord_4180719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180719).length < 2 ^ (prefixWord ++ tailWord_4180719).sum := by decide
  have hdescent : baseEnd_4180719 < baseStart_4180719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180729 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 5, 5]
def baseStart_4180729 : Nat := 118140960795 + 4180729 * 2 ^ 59
def prefixEnd_4180729 : Nat := 4983230072969 + 3 ^ 40 * 4180729 * 2
def baseEnd_4180729 : Nat := 715574487730292870753561

theorem tailTrace_4180729 : CollatzResearch.WordTrace tailWord_4180729 prefixEnd_4180729 715574487730292870753561 := by
  unfold tailWord_4180729
  simp only [CollatzResearch.WordTrace]
  refine ⟨152483713670940319512937241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101655809113960213008624827 152483713670940319512937241)
  ·
    refine ⟨114362785253205239634702931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152483713670940319512937241 114362785253205239634702931)
    ·
      refine ⟨171544177879807859452054397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114362785253205239634702931 171544177879807859452054397)
      ·
        refine ⟨64329066704927947294520399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171544177879807859452054397 64329066704927947294520399)
        ·
          refine ⟨96493600057391920941780599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64329066704927947294520399 96493600057391920941780599)
          ·
            refine ⟨144740400086087881412670899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96493600057391920941780599 144740400086087881412670899)
            ·
              refine ⟨217110600129131822119006349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144740400086087881412670899 217110600129131822119006349)
              ·
                refine ⟨81416475048424433294627381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217110600129131822119006349 81416475048424433294627381)
                ·
                  refine ⟨7632794535789790621371317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81416475048424433294627381 7632794535789790621371317)
                  ·
                    refine ⟨715574487730292870753561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7632794535789790621371317 715574487730292870753561)
                    ·
                      rfl

theorem cell23_4180729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 5].length) (baseStart_4180729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180729 prefixEnd_4180729 := by exact prefixLift 4180729
  have htrace : WordTrace (prefixWord ++ tailWord_4180729) baseStart_4180729 baseEnd_4180729 := by
    simpa [prefixWord, tailWord_4180729, baseEnd_4180729] using wordTrace_append hprefix tailTrace_4180729
  have hstable : (prefixWord ++ tailWord_4180729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180729).length < 2 ^ (prefixWord ++ tailWord_4180729).sum := by decide
  have hdescent : baseEnd_4180729 < baseStart_4180729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180754 : List Nat := [3, 2, 4, 1, 2, 2, 1, 3, 1, 4]
def baseStart_4180754 : Nat := 118140960795 + 4180754 * 2 ^ 59
def prefixEnd_4180754 : Nat := 4983230072969 + 3 ^ 40 * 4180754 * 2
def baseEnd_4180754 : Nat := 715578766735747004816023

theorem tailTrace_4180754 : CollatzResearch.WordTrace tailWord_4180754 prefixEnd_4180754 715578766735747004816023 := by
  unfold tailWord_4180754
  simp only [CollatzResearch.WordTrace]
  refine ⟨38121156373962437195649329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101656416997233165855064877 38121156373962437195649329)
  ·
    refine ⟨28590867280471827896736997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38121156373962437195649329 28590867280471827896736997)
    ·
      refine ⟨5360787615088467730638187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28590867280471827896736997 5360787615088467730638187)
      ·
        refine ⟨8041181422632701595957281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5360787615088467730638187 8041181422632701595957281)
        ·
          refine ⟨6030886066974526196967961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8041181422632701595957281 6030886066974526196967961)
          ·
            refine ⟨4523164550230894647725971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6030886066974526196967961 4523164550230894647725971)
            ·
              refine ⟨6784746825346341971588957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4523164550230894647725971 6784746825346341971588957)
              ·
                refine ⟨2544280059504878239345859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6784746825346341971588957 2544280059504878239345859)
                ·
                  refine ⟨3816420089257317359018789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2544280059504878239345859 3816420089257317359018789)
                  ·
                    refine ⟨715578766735747004816023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3816420089257317359018789 715578766735747004816023)
                    ·
                      rfl

theorem cell23_4180754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_4180754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180754 prefixEnd_4180754 := by exact prefixLift 4180754
  have htrace : WordTrace (prefixWord ++ tailWord_4180754) baseStart_4180754 baseEnd_4180754 := by
    simpa [prefixWord, tailWord_4180754, baseEnd_4180754] using wordTrace_append hprefix tailTrace_4180754
  have hstable : (prefixWord ++ tailWord_4180754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180754).length < 2 ^ (prefixWord ++ tailWord_4180754).sum := by decide
  have hdescent : baseEnd_4180754 < baseStart_4180754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180770 : List Nat := [3, 3, 1, 1, 2, 3, 1, 2, 2, 3, 2]
def baseStart_4180770 : Nat := 118140960795 + 4180770 * 2 ^ 59
def prefixEnd_4180770 : Nat := 4983230072969 + 3 ^ 40 * 4180770 * 2
def baseEnd_4180770 : Nat := 2146744515897712951847995

theorem tailTrace_4180770 : CollatzResearch.WordTrace tailWord_4180770 prefixEnd_4180770 2146744515897712951847995 := by
  unfold tailWord_4180770
  simp only [CollatzResearch.WordTrace]
  refine ⟨38121302265947945878794941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101656806042527855676786509 38121302265947945878794941)
  ·
    refine ⟨14295488349730479704548103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38121302265947945878794941 14295488349730479704548103)
    ·
      refine ⟨21443232524595719556822155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14295488349730479704548103 21443232524595719556822155)
      ·
        refine ⟨32164848786893579335233233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21443232524595719556822155 32164848786893579335233233)
        ·
          refine ⟨24123636590170184501424925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32164848786893579335233233 24123636590170184501424925)
          ·
            refine ⟨9046363721313819188034347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24123636590170184501424925 9046363721313819188034347)
            ·
              refine ⟨13569545581970728782051521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9046363721313819188034347 13569545581970728782051521)
              ·
                refine ⟨10177159186478046586538641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13569545581970728782051521 10177159186478046586538641)
                ·
                  refine ⟨7632869389858534939903981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10177159186478046586538641 7632869389858534939903981)
                  ·
                    refine ⟨2862326021196950602463993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7632869389858534939903981 2862326021196950602463993)
                    ·
                      refine ⟨2146744515897712951847995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2862326021196950602463993 2146744515897712951847995)
                      ·
                        rfl

theorem cell23_4180770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_4180770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180770 prefixEnd_4180770 := by exact prefixLift 4180770
  have htrace : WordTrace (prefixWord ++ tailWord_4180770) baseStart_4180770 baseEnd_4180770 := by
    simpa [prefixWord, tailWord_4180770, baseEnd_4180770] using wordTrace_append hprefix tailTrace_4180770
  have hstable : (prefixWord ++ tailWord_4180770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180770).length < 2 ^ (prefixWord ++ tailWord_4180770).sum := by decide
  have hdescent : baseEnd_4180770 < baseStart_4180770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180779 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 6]
def baseStart_4180779 : Nat := 118140960795 + 4180779 * 2 ^ 59
def prefixEnd_4180779 : Nat := 4983230072969 + 3 ^ 40 * 4180779 * 2
def baseEnd_4180779 : Nat := 2146749137223603416635453

theorem tailTrace_4180779 : CollatzResearch.WordTrace tailWord_4180779 prefixEnd_4180779 2146749137223603416635453 := by
  unfold tailWord_4180779
  simp only [CollatzResearch.WordTrace]
  refine ⟨152485537320759178052257391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101657024880506118701504927 152485537320759178052257391)
  ·
    refine ⟨228728305981138767078386087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152485537320759178052257391 228728305981138767078386087)
    ·
      refine ⟨343092458971708150617579131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228728305981138767078386087 343092458971708150617579131)
      ·
        refine ⟨514638688457562225926368697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343092458971708150617579131 514638688457562225926368697)
        ·
          refine ⟨385979016343171669444776523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514638688457562225926368697 385979016343171669444776523)
          ·
            refine ⟨578968524514757504167164785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385979016343171669444776523 578968524514757504167164785)
            ·
              refine ⟨434226393386068128125373589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 578968524514757504167164785 434226393386068128125373589)
              ·
                refine ⟨20354362189971943505876887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 434226393386068128125373589 20354362189971943505876887)
                ·
                  refine ⟨30531543284957915258815331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20354362189971943505876887 30531543284957915258815331)
                  ·
                    refine ⟨45797314927436872888222997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30531543284957915258815331 45797314927436872888222997)
                    ·
                      refine ⟨2146749137223603416635453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45797314927436872888222997 2146749137223603416635453)
                      ·
                        rfl

theorem cell23_4180779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 6].length) (baseStart_4180779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180779 prefixEnd_4180779 := by exact prefixLift 4180779
  have htrace : WordTrace (prefixWord ++ tailWord_4180779) baseStart_4180779 baseEnd_4180779 := by
    simpa [prefixWord, tailWord_4180779, baseEnd_4180779] using wordTrace_append hprefix tailTrace_4180779
  have hstable : (prefixWord ++ tailWord_4180779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180779).length < 2 ^ (prefixWord ++ tailWord_4180779).sum := by decide
  have hdescent : baseEnd_4180779 < baseStart_4180779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180786 : List Nat := [3, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5]
def baseStart_4180786 : Nat := 118140960795 + 4180786 * 2 ^ 59
def prefixEnd_4180786 : Nat := 4983230072969 + 3 ^ 40 * 4180786 * 2
def baseEnd_4180786 : Nat := 2146752731588184889247921

theorem tailTrace_4180786 : CollatzResearch.WordTrace tailWord_4180786 prefixEnd_4180786 2146752731588184889247921 := by
  unfold tailWord_4180786
  simp only [CollatzResearch.WordTrace]
  refine ⟨38121448157933454561940553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101657195087822545498508141 38121448157933454561940553)
  ·
    refine ⟨28591086118450090921455415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38121448157933454561940553 28591086118450090921455415)
    ·
      refine ⟨42886629177675136382183123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28591086118450090921455415 42886629177675136382183123)
      ·
        refine ⟨64329943766512704573274685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42886629177675136382183123 64329943766512704573274685)
        ·
          refine ⟨24123728912442264214978007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64329943766512704573274685 24123728912442264214978007)
          ·
            refine ⟨36185593368663396322467011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24123728912442264214978007 36185593368663396322467011)
            ·
              refine ⟨54278390052995094483700517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36185593368663396322467011 54278390052995094483700517)
              ·
                refine ⟨10177198134936580215693847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54278390052995094483700517 10177198134936580215693847)
                ·
                  refine ⟨15265797202404870323540771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10177198134936580215693847 15265797202404870323540771)
                  ·
                    refine ⟨22898695803607305485311157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15265797202404870323540771 22898695803607305485311157)
                    ·
                      refine ⟨2146752731588184889247921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22898695803607305485311157 2146752731588184889247921)
                      ·
                        rfl

theorem cell23_4180786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_4180786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180786 prefixEnd_4180786 := by exact prefixLift 4180786
  have htrace : WordTrace (prefixWord ++ tailWord_4180786) baseStart_4180786 baseEnd_4180786 := by
    simpa [prefixWord, tailWord_4180786, baseEnd_4180786] using wordTrace_append hprefix tailTrace_4180786
  have hstable : (prefixWord ++ tailWord_4180786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180786).length < 2 ^ (prefixWord ++ tailWord_4180786).sum := by decide
  have hdescent : baseEnd_4180786 < baseStart_4180786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180796 : List Nat := [2, 2, 2, 2, 1, 1, 1, 5, 1, 2, 4]
def baseStart_4180796 : Nat := 118140960795 + 4180796 * 2 ^ 59
def prefixEnd_4180796 : Nat := 4983230072969 + 3 ^ 40 * 4180796 * 2
def baseEnd_4180796 : Nat := 2146757866394729850122875

theorem tailTrace_4180796 : CollatzResearch.WordTrace tailWord_4180796 prefixEnd_4180796 2146757866394729850122875 := by
  unfold tailWord_4180796
  simp only [CollatzResearch.WordTrace]
  refine ⟨76243078680848794977813121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101657438241131726637084161 76243078680848794977813121)
  ·
    refine ⟨57182309010636596233359841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76243078680848794977813121 57182309010636596233359841)
    ·
      refine ⟨42886731757977447175019881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57182309010636596233359841 42886731757977447175019881)
      ·
        refine ⟨32165048818483085381264911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42886731757977447175019881 32165048818483085381264911)
        ·
          refine ⟨48247573227724628071897367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32165048818483085381264911 48247573227724628071897367)
          ·
            refine ⟨72371359841586942107846051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48247573227724628071897367 72371359841586942107846051)
            ·
              refine ⟨108557039762380413161769077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72371359841586942107846051 108557039762380413161769077)
              ·
                refine ⟨10177222477723163733915851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108557039762380413161769077 10177222477723163733915851)
                ·
                  refine ⟨15265833716584745600873777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10177222477723163733915851 15265833716584745600873777)
                  ·
                    refine ⟨11449375287438559200655333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15265833716584745600873777 11449375287438559200655333)
                    ·
                      refine ⟨2146757866394729850122875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11449375287438559200655333 2146757866394729850122875)
                      ·
                        rfl

theorem cell23_4180796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_4180796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180796 prefixEnd_4180796 := by exact prefixLift 4180796
  have htrace : WordTrace (prefixWord ++ tailWord_4180796) baseStart_4180796 baseEnd_4180796 := by
    simpa [prefixWord, tailWord_4180796, baseEnd_4180796] using wordTrace_append hprefix tailTrace_4180796
  have hstable : (prefixWord ++ tailWord_4180796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180796).length < 2 ^ (prefixWord ++ tailWord_4180796).sum := by decide
  have hdescent : baseEnd_4180796 < baseStart_4180796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180797 : List Nat := [1, 4, 1, 4, 3, 1, 1, 2, 1, 5]
def baseStart_4180797 : Nat := 118140960795 + 4180797 * 2 ^ 59
def prefixEnd_4180797 : Nat := 4983230072969 + 3 ^ 40 * 4180797 * 2
def baseEnd_4180797 : Nat := 715586126625128115403457

theorem tailTrace_4180797 : CollatzResearch.WordTrace tailWord_4180797 prefixEnd_4180797 715586126625128115403457 := by
  unfold tailWord_4180797
  simp only [CollatzResearch.WordTrace]
  refine ⟨152486193834693967126412645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101657462556462644750941763 152486193834693967126412645)
  ·
    refine ⟨28591161344005118836202371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152486193834693967126412645 28591161344005118836202371)
    ·
      refine ⟨42886742016007678254303557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28591161344005118836202371 42886742016007678254303557)
      ·
        refine ⟨8041264128001439672681917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42886742016007678254303557 8041264128001439672681917)
        ·
          refine ⟨3015474048000539877255719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8041264128001439672681917 3015474048000539877255719)
          ·
            refine ⟨4523211072000809815883579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3015474048000539877255719 4523211072000809815883579)
            ·
              refine ⟨6784816608001214723825369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4523211072000809815883579 6784816608001214723825369)
              ·
                refine ⟨5088612456000911042869027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6784816608001214723825369 5088612456000911042869027)
                ·
                  refine ⟨7632918684001366564303541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5088612456000911042869027 7632918684001366564303541)
                  ·
                    refine ⟨715586126625128115403457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7632918684001366564303541 715586126625128115403457)
                    ·
                      rfl

theorem cell23_4180797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_4180797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180797 prefixEnd_4180797 := by exact prefixLift 4180797
  have htrace : WordTrace (prefixWord ++ tailWord_4180797) baseStart_4180797 baseEnd_4180797 := by
    simpa [prefixWord, tailWord_4180797, baseEnd_4180797] using wordTrace_append hprefix tailTrace_4180797
  have hstable : (prefixWord ++ tailWord_4180797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180797).length < 2 ^ (prefixWord ++ tailWord_4180797).sum := by decide
  have hdescent : baseEnd_4180797 < baseStart_4180797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180804 : List Nat := [2, 3, 4, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_4180804 : Nat := 118140960795 + 4180804 * 2 ^ 59
def prefixEnd_4180804 : Nat := 4983230072969 + 3 ^ 40 * 4180804 * 2
def baseEnd_4180804 : Nat := 2146761974239965818822839

theorem tailTrace_4180804 : CollatzResearch.WordTrace tailWord_4180804 prefixEnd_4180804 2146761974239965818822839 := by
  unfold tailWord_4180804
  simp only [CollatzResearch.WordTrace]
  refine ⟨76243224572834303660958733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101657632763779071547944977 76243224572834303660958733)
  ·
    refine ⟨28591209214812863872859525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76243224572834303660958733 28591209214812863872859525)
    ·
      refine ⟨5360851727777411976161161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28591209214812863872859525 5360851727777411976161161)
      ·
        refine ⟨4020638795833058982120871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5360851727777411976161161 4020638795833058982120871)
        ·
          refine ⟨6030958193749588473181307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4020638795833058982120871 6030958193749588473181307)
          ·
            refine ⟨9046437290624382709771961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6030958193749588473181307 9046437290624382709771961)
            ·
              refine ⟨6784827967968287032328971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9046437290624382709771961 6784827967968287032328971)
              ·
                refine ⟨10177241951952430548493457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6784827967968287032328971 10177241951952430548493457)
                ·
                  refine ⟨7632931463964322911370093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10177241951952430548493457 7632931463964322911370093)
                  ·
                    refine ⟨2862349298986621091763785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7632931463964322911370093 2862349298986621091763785)
                    ·
                      refine ⟨2146761974239965818822839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2862349298986621091763785 2146761974239965818822839)
                      ·
                        rfl

theorem cell23_4180804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_4180804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180804 prefixEnd_4180804 := by exact prefixLift 4180804
  have htrace : WordTrace (prefixWord ++ tailWord_4180804) baseStart_4180804 baseEnd_4180804 := by
    simpa [prefixWord, tailWord_4180804, baseEnd_4180804] using wordTrace_append hprefix tailTrace_4180804
  have hstable : (prefixWord ++ tailWord_4180804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180804).length < 2 ^ (prefixWord ++ tailWord_4180804).sum := by decide
  have hdescent : baseEnd_4180804 < baseStart_4180804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180816 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 3]
def baseStart_4180816 : Nat := 118140960795 + 4180816 * 2 ^ 59
def prefixEnd_4180816 : Nat := 4983230072969 + 3 ^ 40 * 4180816 * 2
def baseEnd_4180816 : Nat := 2146768136007819771872783

theorem tailTrace_4180816 : CollatzResearch.WordTrace tailWord_4180816 prefixEnd_4180816 2146768136007819771872783 := by
  unfold tailWord_4180816
  simp only [CollatzResearch.WordTrace]
  refine ⟨76243443410812566685677151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101657924547750088914236201 76243443410812566685677151)
  ·
    refine ⟨114365165116218850028515727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76243443410812566685677151 114365165116218850028515727)
    ·
      refine ⟨171547747674328275042773591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114365165116218850028515727 171547747674328275042773591)
      ·
        refine ⟨257321621511492412564160387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171547747674328275042773591 257321621511492412564160387)
        ·
          refine ⟨385982432267238618846240581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257321621511492412564160387 385982432267238618846240581)
          ·
            refine ⟨72371706050107241033670109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 385982432267238618846240581 72371706050107241033670109)
            ·
              refine ⟨27139389768790215387626291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72371706050107241033670109 27139389768790215387626291)
              ·
                refine ⟨40709084653185323081439437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27139389768790215387626291 40709084653185323081439437)
                ·
                  refine ⟨15265906744944496155539789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40709084653185323081439437 15265906744944496155539789)
                  ·
                    refine ⟨5724715029354186058327421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15265906744944496155539789 5724715029354186058327421)
                    ·
                      refine ⟨2146768136007819771872783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5724715029354186058327421 2146768136007819771872783)
                      ·
                        rfl

theorem cell23_4180816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 3].length) (baseStart_4180816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180816 prefixEnd_4180816 := by exact prefixLift 4180816
  have htrace : WordTrace (prefixWord ++ tailWord_4180816) baseStart_4180816 baseEnd_4180816 := by
    simpa [prefixWord, tailWord_4180816, baseEnd_4180816] using wordTrace_append hprefix tailTrace_4180816
  have hstable : (prefixWord ++ tailWord_4180816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180816).length < 2 ^ (prefixWord ++ tailWord_4180816).sum := by decide
  have hdescent : baseEnd_4180816 < baseStart_4180816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180819 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 4, 7]
def baseStart_4180819 : Nat := 118140960795 + 4180819 * 2 ^ 59
def prefixEnd_4180819 : Nat := 4983230072969 + 3 ^ 40 * 4180819 * 2
def baseEnd_4180819 : Nat := 715589892149927753378423

theorem tailTrace_4180819 : CollatzResearch.WordTrace tailWord_4180819 prefixEnd_4180819 715589892149927753378423 := by
  unfold tailWord_4180819
  simp only [CollatzResearch.WordTrace]
  refine ⟨152486996240614264883713511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101657997493742843255809007 152486996240614264883713511)
  ·
    refine ⟨228730494360921397325570267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152486996240614264883713511 228730494360921397325570267)
    ·
      refine ⟨343095741541382095988355401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228730494360921397325570267 343095741541382095988355401)
      ·
        refine ⟨257321806156036571991266551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343095741541382095988355401 257321806156036571991266551)
        ·
          refine ⟨385982709234054857986899827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257321806156036571991266551 385982709234054857986899827)
          ·
            refine ⟨578974063851082286980349741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385982709234054857986899827 578974063851082286980349741)
            ·
              refine ⟨217115273944155857617631153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 578974063851082286980349741 217115273944155857617631153)
              ·
                refine ⟨162836455458116893213223365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217115273944155857617631153 162836455458116893213223365)
                ·
                  refine ⟨30531835398396917477479381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162836455458116893213223365 30531835398396917477479381)
                  ·
                    refine ⟨715589892149927753378423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30531835398396917477479381 715589892149927753378423)
                    ·
                      rfl

theorem cell23_4180819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 7].length) (baseStart_4180819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180819 prefixEnd_4180819 := by exact prefixLift 4180819
  have htrace : WordTrace (prefixWord ++ tailWord_4180819) baseStart_4180819 baseEnd_4180819 := by
    simpa [prefixWord, tailWord_4180819, baseEnd_4180819] using wordTrace_append hprefix tailTrace_4180819
  have hstable : (prefixWord ++ tailWord_4180819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180819).length < 2 ^ (prefixWord ++ tailWord_4180819).sum := by decide
  have hdescent : baseEnd_4180819 < baseStart_4180819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180820 : List Nat := [2, 4, 1, 1, 4, 2, 1, 1, 1, 1, 5]
def baseStart_4180820 : Nat := 118140960795 + 4180820 * 2 ^ 59
def prefixEnd_4180820 : Nat := 4983230072969 + 3 ^ 40 * 4180820 * 2
def baseEnd_4180820 : Nat := 2146770189930437756222765

theorem tailTrace_4180820 : CollatzResearch.WordTrace tailWord_4180820 prefixEnd_4180820 2146770189930437756222765 := by
  unfold tailWord_4180820
  simp only [CollatzResearch.WordTrace]
  refine ⟨76243516356805321027249957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101658021809073761369666609 76243516356805321027249957)
  ·
    refine ⟨14295659316900997692609367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76243516356805321027249957 14295659316900997692609367)
    ·
      refine ⟨21443488975351496538914051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14295659316900997692609367 21443488975351496538914051)
      ·
        refine ⟨32165233463027244808371077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21443488975351496538914051 32165233463027244808371077)
        ·
          refine ⟨6030981274317608401569577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32165233463027244808371077 6030981274317608401569577)
          ·
            refine ⟨4523235955738206301177183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6030981274317608401569577 4523235955738206301177183)
            ·
              refine ⟨6784853933607309451765775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4523235955738206301177183 6784853933607309451765775)
              ·
                refine ⟨10177280900410964177648663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6784853933607309451765775 10177280900410964177648663)
                ·
                  refine ⟨15265921350616446266472995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10177280900410964177648663 15265921350616446266472995)
                  ·
                    refine ⟨22898882025924669399709493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15265921350616446266472995 22898882025924669399709493)
                    ·
                      refine ⟨2146770189930437756222765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22898882025924669399709493 2146770189930437756222765)
                      ·
                        rfl

theorem cell23_4180820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_4180820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180820 prefixEnd_4180820 := by exact prefixLift 4180820
  have htrace : WordTrace (prefixWord ++ tailWord_4180820) baseStart_4180820 baseEnd_4180820 := by
    simpa [prefixWord, tailWord_4180820, baseEnd_4180820] using wordTrace_append hprefix tailTrace_4180820
  have hstable : (prefixWord ++ tailWord_4180820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180820).length < 2 ^ (prefixWord ++ tailWord_4180820).sum := by decide
  have hdescent : baseEnd_4180820 < baseStart_4180820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180836 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 2, 7]
def baseStart_4180836 : Nat := 118140960795 + 4180836 * 2 ^ 59
def prefixEnd_4180836 : Nat := 4983230072969 + 3 ^ 40 * 4180836 * 2
def baseEnd_4180836 : Nat := 715592801873636564540897

theorem tailTrace_4180836 : CollatzResearch.WordTrace tailWord_4180836 prefixEnd_4180836 715592801873636564540897 := by
  unfold tailWord_4180836
  simp only [CollatzResearch.WordTrace]
  refine ⟨76243808140776338393541181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101658410854368451191388241 76243808140776338393541181)
  ·
    refine ⟨28591428052791126897577943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76243808140776338393541181 28591428052791126897577943)
    ·
      refine ⟨42887142079186690346366915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28591428052791126897577943 42887142079186690346366915)
      ·
        refine ⟨64330713118780035519550373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42887142079186690346366915 64330713118780035519550373)
        ·
          refine ⟨12062008709771256659915695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64330713118780035519550373 12062008709771256659915695)
          ·
            refine ⟨18093013064656884989873543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12062008709771256659915695 18093013064656884989873543)
            ·
              refine ⟨27139519596985327484810315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18093013064656884989873543 27139519596985327484810315)
              ·
                refine ⟨40709279395477991227215473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27139519596985327484810315 40709279395477991227215473)
                ·
                  refine ⟨30531959546608493420411605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40709279395477991227215473 30531959546608493420411605)
                  ·
                    refine ⟨715592801873636564540897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30531959546608493420411605 715592801873636564540897)
                    ·
                      rfl

theorem cell23_4180836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_4180836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180836 prefixEnd_4180836 := by exact prefixLift 4180836
  have htrace : WordTrace (prefixWord ++ tailWord_4180836) baseStart_4180836 baseEnd_4180836 := by
    simpa [prefixWord, tailWord_4180836, baseEnd_4180836] using wordTrace_append hprefix tailTrace_4180836
  have hstable : (prefixWord ++ tailWord_4180836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180836).length < 2 ^ (prefixWord ++ tailWord_4180836).sum := by decide
  have hdescent : baseEnd_4180836 < baseStart_4180836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180843 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 3, 3, 2]
def baseStart_4180843 : Nat := 118140960795 + 4180843 * 2 ^ 59
def prefixEnd_4180843 : Nat := 4983230072969 + 3 ^ 40 * 4180843 * 2
def baseEnd_4180843 : Nat := 2146781999985491166235159

theorem tailTrace_4180843 : CollatzResearch.WordTrace tailWord_4180843 prefixEnd_4180843 2146781999985491166235159 := by
  unfold tailWord_4180843
  simp only [CollatzResearch.WordTrace]
  refine ⟨152487871592527316982587183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101658581061684877988391455 152487871592527316982587183)
  ·
    refine ⟨228731807388790975473880775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152487871592527316982587183 228731807388790975473880775)
    ·
      refine ⟨343097711083186463210821163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228731807388790975473880775 343097711083186463210821163)
      ·
        refine ⟨514646566624779694816231745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343097711083186463210821163 514646566624779694816231745)
        ·
          refine ⟨385984924968584771112173809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514646566624779694816231745 385984924968584771112173809)
          ·
            refine ⟨289488693726438578334130357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385984924968584771112173809 289488693726438578334130357)
            ·
              refine ⟨27139565036853616718824721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 289488693726438578334130357 27139565036853616718824721)
              ·
                refine ⟨20354673777640212539118541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27139565036853616718824721 20354673777640212539118541)
                ·
                  refine ⟨7633002666615079702169453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20354673777640212539118541 7633002666615079702169453)
                  ·
                    refine ⟨2862375999980654888313545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7633002666615079702169453 2862375999980654888313545)
                    ·
                      refine ⟨2146781999985491166235159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2862375999980654888313545 2146781999985491166235159)
                      ·
                        rfl

theorem cell23_4180843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 3, 2].length) (baseStart_4180843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180843 prefixEnd_4180843 := by exact prefixLift 4180843
  have htrace : WordTrace (prefixWord ++ tailWord_4180843) baseStart_4180843 baseEnd_4180843 := by
    simpa [prefixWord, tailWord_4180843, baseEnd_4180843] using wordTrace_append hprefix tailTrace_4180843
  have hstable : (prefixWord ++ tailWord_4180843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180843).length < 2 ^ (prefixWord ++ tailWord_4180843).sum := by decide
  have hdescent : baseEnd_4180843 < baseStart_4180843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180850 : List Nat := [3, 2, 1, 2, 1, 1, 4, 3, 2, 1, 3]
def baseStart_4180850 : Nat := 118140960795 + 4180850 * 2 ^ 59
def prefixEnd_4180850 : Nat := 4983230072969 + 3 ^ 40 * 4180850 * 2
def baseEnd_4180850 : Nat := 2146785594350072638847627

theorem tailTrace_4180850 : CollatzResearch.WordTrace tailWord_4180850 prefixEnd_4180850 2146785594350072638847627 := by
  unfold tailWord_4180850
  simp only [CollatzResearch.WordTrace]
  refine ⟨38122031725875489294523001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101658751269001304785394669 38122031725875489294523001)
  ·
    refine ⟨28591523794406616970892251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38122031725875489294523001 28591523794406616970892251)
    ·
      refine ⟨42887285691609925456338377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28591523794406616970892251 42887285691609925456338377)
      ·
        refine ⟨32165464268707444092253783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42887285691609925456338377 32165464268707444092253783)
        ·
          refine ⟨48248196403061166138380675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32165464268707444092253783 48248196403061166138380675)
          ·
            refine ⟨72372294604591749207571013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48248196403061166138380675 72372294604591749207571013)
            ·
              refine ⟨13569805238360952976419565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72372294604591749207571013 13569805238360952976419565)
              ·
                refine ⟨5088676964385357366157337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13569805238360952976419565 5088676964385357366157337)
                ·
                  refine ⟨3816507723289018024618003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5088676964385357366157337 3816507723289018024618003)
                  ·
                    refine ⟨5724761584933527036927005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3816507723289018024618003 5724761584933527036927005)
                    ·
                      refine ⟨2146785594350072638847627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5724761584933527036927005 2146785594350072638847627)
                      ·
                        rfl

theorem cell23_4180850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_4180850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180850 prefixEnd_4180850 := by exact prefixLift 4180850
  have htrace : WordTrace (prefixWord ++ tailWord_4180850) baseStart_4180850 baseEnd_4180850 := by
    simpa [prefixWord, tailWord_4180850, baseEnd_4180850] using wordTrace_append hprefix tailTrace_4180850
  have hstable : (prefixWord ++ tailWord_4180850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180850).length < 2 ^ (prefixWord ++ tailWord_4180850).sum := by decide
  have hdescent : baseEnd_4180850 < baseStart_4180850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180876 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 2, 1, 5]
def baseStart_4180876 : Nat := 118140960795 + 4180876 * 2 ^ 59
def prefixEnd_4180876 : Nat := 4983230072969 + 3 ^ 40 * 4180876 * 2
def baseEnd_4180876 : Nat := 2146798944847089537122507

theorem tailTrace_4180876 : CollatzResearch.WordTrace tailWord_4180876 prefixEnd_4180876 2146798944847089537122507 := by
  unfold tailWord_4180876
  simp only [CollatzResearch.WordTrace]
  refine ⟨76244537600703881809269241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101659383467605175745692321 76244537600703881809269241)
  ·
    refine ⟨57183403200527911356951931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76244537600703881809269241 57183403200527911356951931)
    ·
      refine ⟨85775104800791867035427897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57183403200527911356951931 85775104800791867035427897)
      ·
        refine ⟨64331328600593900276570923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85775104800791867035427897 64331328600593900276570923)
        ·
          refine ⟨96496992900890850414856385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64331328600593900276570923 96496992900890850414856385)
          ·
            refine ⟨72372744675668137811142289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96496992900890850414856385 72372744675668137811142289)
            ·
              refine ⟨54279558506751103358356717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72372744675668137811142289 54279558506751103358356717)
              ·
                refine ⟨20354834440031663759383769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54279558506751103358356717 20354834440031663759383769)
                ·
                  refine ⟨15266125830023747819537827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20354834440031663759383769 15266125830023747819537827)
                  ·
                    refine ⟨22899188745035621729306741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15266125830023747819537827 22899188745035621729306741)
                    ·
                      refine ⟨2146798944847089537122507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22899188745035621729306741 2146798944847089537122507)
                      ·
                        rfl

theorem cell23_4180876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_4180876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180876 prefixEnd_4180876 := by exact prefixLift 4180876
  have htrace : WordTrace (prefixWord ++ tailWord_4180876) baseStart_4180876 baseEnd_4180876 := by
    simpa [prefixWord, tailWord_4180876, baseEnd_4180876] using wordTrace_append hprefix tailTrace_4180876
  have hstable : (prefixWord ++ tailWord_4180876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180876).length < 2 ^ (prefixWord ++ tailWord_4180876).sum := by decide
  have hdescent : baseEnd_4180876 < baseStart_4180876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180896 : List Nat := [2, 1, 1, 4, 1, 1, 3, 3, 7]
def baseStart_4180896 : Nat := 118140960795 + 4180896 * 2 ^ 59
def prefixEnd_4180896 : Nat := 4983230072969 + 3 ^ 40 * 4180896 * 2
def baseEnd_4180896 : Nat := 238534357162242162096935

theorem tailTrace_4180896 : CollatzResearch.WordTrace tailWord_4180896 prefixEnd_4180896 238534357162242162096935 := by
  unfold tailWord_4180896
  simp only [CollatzResearch.WordTrace]
  refine ⟨76244902330667653517133271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101659869774223538022844361 76244902330667653517133271)
  ·
    refine ⟨114367353496001480275699907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76244902330667653517133271 114367353496001480275699907)
    ·
      refine ⟨171551030244002220413549861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114367353496001480275699907 171551030244002220413549861)
      ·
        refine ⟨32165818170750416327540599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171551030244002220413549861 32165818170750416327540599)
        ·
          refine ⟨48248727256125624491310899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32165818170750416327540599 48248727256125624491310899)
          ·
            refine ⟨72373090884188436736966349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48248727256125624491310899 72373090884188436736966349)
            ·
              refine ⟨27139909081570663776362381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72373090884188436736966349 27139909081570663776362381)
              ·
                refine ⟨10177465905588998916135893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27139909081570663776362381 10177465905588998916135893)
                ·
                  refine ⟨238534357162242162096935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10177465905588998916135893 238534357162242162096935)
                  ·
                    rfl

theorem cell23_4180896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 7].length) (baseStart_4180896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180896 prefixEnd_4180896 := by exact prefixLift 4180896
  have htrace : WordTrace (prefixWord ++ tailWord_4180896) baseStart_4180896 baseEnd_4180896 := by
    simpa [prefixWord, tailWord_4180896, baseEnd_4180896] using wordTrace_append hprefix tailTrace_4180896
  have hstable : (prefixWord ++ tailWord_4180896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180896).length < 2 ^ (prefixWord ++ tailWord_4180896).sum := by decide
  have hdescent : baseEnd_4180896 < baseStart_4180896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180943 : List Nat := [1, 1, 2, 1, 1, 7, 1, 2, 2, 5]
def baseStart_4180943 : Nat := 118140960795 + 4180943 * 2 ^ 59
def prefixEnd_4180943 : Nat := 4983230072969 + 3 ^ 40 * 4180943 * 2
def baseEnd_4180943 : Nat := 715611116016980258328233

theorem tailTrace_4180943 : CollatzResearch.WordTrace tailWord_4180943 prefixEnd_4180943 715611116016980258328233 := by
  unfold tailWord_4180943
  simp only [CollatzResearch.WordTrace]
  refine ⟨152491518892165034061227483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101661012594776689374151655 152491518892165034061227483)
  ·
    refine ⟨228737278338247551091841225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152491518892165034061227483 228737278338247551091841225)
    ·
      refine ⟨171552958753685663318880919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228737278338247551091841225 171552958753685663318880919)
      ·
        refine ⟨257329438130528494978321379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171552958753685663318880919 257329438130528494978321379)
        ·
          refine ⟨385994157195792742467482069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257329438130528494978321379 385994157195792742467482069)
          ·
            refine ⟨9046738059276392401581611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 385994157195792742467482069 9046738059276392401581611)
            ·
              refine ⟨13570107088914588602372417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9046738059276392401581611 13570107088914588602372417)
              ·
                refine ⟨10177580316685941451779313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13570107088914588602372417 10177580316685941451779313)
                ·
                  refine ⟨7633185237514456088834485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10177580316685941451779313 7633185237514456088834485)
                  ·
                    refine ⟨715611116016980258328233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7633185237514456088834485 715611116016980258328233)
                    ·
                      rfl

theorem cell23_4180943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 5].length) (baseStart_4180943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180943 prefixEnd_4180943 := by exact prefixLift 4180943
  have htrace : WordTrace (prefixWord ++ tailWord_4180943) baseStart_4180943 baseEnd_4180943 := by
    simpa [prefixWord, tailWord_4180943, baseEnd_4180943] using wordTrace_append hprefix tailTrace_4180943
  have hstable : (prefixWord ++ tailWord_4180943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180943).length < 2 ^ (prefixWord ++ tailWord_4180943).sum := by decide
  have hdescent : baseEnd_4180943 < baseStart_4180943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180953 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 1, 2, 5]
def baseStart_4180953 : Nat := 118140960795 + 4180953 * 2 ^ 59
def prefixEnd_4180953 : Nat := 4983230072969 + 3 ^ 40 * 4180953 * 2
def baseEnd_4180953 : Nat := 2146838482857485735859653

theorem tailTrace_4180953 : CollatzResearch.WordTrace tailWord_4180953 prefixEnd_4180953 2146838482857485735859653 := by
  unfold tailWord_4180953
  simp only [CollatzResearch.WordTrace]
  refine ⟨152491883622128805769091513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101661255748085870512727675 152491883622128805769091513)
  ·
    refine ⟨114368912716596604326818635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152491883622128805769091513 114368912716596604326818635)
    ·
      refine ⟨171553369074894906490227953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114368912716596604326818635 171553369074894906490227953)
      ·
        refine ⟨128665026806171179867670965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171553369074894906490227953 128665026806171179867670965)
        ·
          refine ⟨12062346263078548112594153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128665026806171179867670965 12062346263078548112594153)
          ·
            refine ⟨9046759697308911084445615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12062346263078548112594153 9046759697308911084445615)
            ·
              refine ⟨13570139545963366626668423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9046759697308911084445615 13570139545963366626668423)
              ·
                refine ⟨20355209318945049940002635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13570139545963366626668423 20355209318945049940002635)
                ·
                  refine ⟨30532813978417574910003953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20355209318945049940002635 30532813978417574910003953)
                  ·
                    refine ⟨22899610483813181182502965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30532813978417574910003953 22899610483813181182502965)
                    ·
                      refine ⟨2146838482857485735859653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22899610483813181182502965 2146838482857485735859653)
                      ·
                        rfl

theorem cell23_4180953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_4180953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180953 prefixEnd_4180953 := by exact prefixLift 4180953
  have htrace : WordTrace (prefixWord ++ tailWord_4180953) baseStart_4180953 baseEnd_4180953 := by
    simpa [prefixWord, tailWord_4180953, baseEnd_4180953] using wordTrace_append hprefix tailTrace_4180953
  have hstable : (prefixWord ++ tailWord_4180953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180953).length < 2 ^ (prefixWord ++ tailWord_4180953).sum := by decide
  have hdescent : baseEnd_4180953 < baseStart_4180953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180963 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 4]
def baseStart_4180963 : Nat := 118140960795 + 4180963 * 2 ^ 59
def prefixEnd_4180963 : Nat := 4983230072969 + 3 ^ 40 * 4180963 * 2
def baseEnd_4180963 : Nat := 2146843617664030696734607

theorem tailTrace_4180963 : CollatzResearch.WordTrace tailWord_4180963 prefixEnd_4180963 2146843617664030696734607 := by
  unfold tailWord_4180963
  simp only [CollatzResearch.WordTrace]
  refine ⟨152492248352092577476955543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101661498901395051651303695 152492248352092577476955543)
  ·
    refine ⟨228738372528138866215433315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152492248352092577476955543 228738372528138866215433315)
    ·
      refine ⟨343107558792208299323149973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228738372528138866215433315 343107558792208299323149973)
      ·
        refine ⟨16083166818384764030772655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 343107558792208299323149973 16083166818384764030772655)
        ·
          refine ⟨24124750227577146046158983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16083166818384764030772655 24124750227577146046158983)
          ·
            refine ⟨36187125341365719069238475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24124750227577146046158983 36187125341365719069238475)
            ·
              refine ⟨54280688012048578603857713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36187125341365719069238475 54280688012048578603857713)
              ·
                refine ⟨40710516009036433952893285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54280688012048578603857713 40710516009036433952893285)
                ·
                  refine ⟨7633221751694331366167491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40710516009036433952893285 7633221751694331366167491)
                  ·
                    refine ⟨11449832627541497049251237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7633221751694331366167491 11449832627541497049251237)
                    ·
                      refine ⟨2146843617664030696734607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11449832627541497049251237 2146843617664030696734607)
                      ·
                        rfl

theorem cell23_4180963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_4180963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180963 prefixEnd_4180963 := by exact prefixLift 4180963
  have htrace : WordTrace (prefixWord ++ tailWord_4180963) baseStart_4180963 baseEnd_4180963 := by
    simpa [prefixWord, tailWord_4180963, baseEnd_4180963] using wordTrace_append hprefix tailTrace_4180963
  have hstable : (prefixWord ++ tailWord_4180963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180963).length < 2 ^ (prefixWord ++ tailWord_4180963).sum := by decide
  have hdescent : baseEnd_4180963 < baseStart_4180963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180976 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 6]
def baseStart_4180976 : Nat := 118140960795 + 4180976 * 2 ^ 59
def prefixEnd_4180976 : Nat := 4983230072969 + 3 ^ 40 * 4180976 * 2
def baseEnd_4180976 : Nat := 2146850292912539145872047

theorem tailTrace_4180976 : CollatzResearch.WordTrace tailWord_4180976 prefixEnd_4180976 2146850292912539145872047 := by
  unfold tailWord_4180976
  simp only [CollatzResearch.WordTrace]
  refine ⟨76246361250522740348589391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101661815000696987131452521 76246361250522740348589391)
  ·
    refine ⟨114369541875784110522884087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76246361250522740348589391 114369541875784110522884087)
    ·
      refine ⟨171554312813676165784326131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114369541875784110522884087 171554312813676165784326131)
      ·
        refine ⟨257331469220514248676489197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171554312813676165784326131 257331469220514248676489197)
        ·
          refine ⟨96499300957692843253683449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257331469220514248676489197 96499300957692843253683449)
          ·
            refine ⟨72374475718269632440262587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96499300957692843253683449 72374475718269632440262587)
            ·
              refine ⟨108561713577404448660393881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72374475718269632440262587 108561713577404448660393881)
              ·
                refine ⟨81421285183053336495295411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108561713577404448660393881 81421285183053336495295411)
                ·
                  refine ⟨122131927774580004742943117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81421285183053336495295411 122131927774580004742943117)
                  ·
                    refine ⟨45799472915467501778603669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122131927774580004742943117 45799472915467501778603669)
                    ·
                      refine ⟨2146850292912539145872047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45799472915467501778603669 2146850292912539145872047)
                      ·
                        rfl

theorem cell23_4180976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_4180976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180976 prefixEnd_4180976 := by exact prefixLift 4180976
  have htrace : WordTrace (prefixWord ++ tailWord_4180976) baseStart_4180976 baseEnd_4180976 := by
    simpa [prefixWord, tailWord_4180976, baseEnd_4180976] using wordTrace_append hprefix tailTrace_4180976
  have hstable : (prefixWord ++ tailWord_4180976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180976).length < 2 ^ (prefixWord ++ tailWord_4180976).sum := by decide
  have hdescent : baseEnd_4180976 < baseStart_4180976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180986 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 10]
def baseStart_4180986 : Nat := 118140960795 + 4180986 * 2 ^ 59
def prefixEnd_4180986 : Nat := 4983230072969 + 3 ^ 40 * 4180986 * 2
def baseEnd_4180986 : Nat := 238539491968787122971889

theorem tailTrace_4180986 : CollatzResearch.WordTrace tailWord_4180986 prefixEnd_4180986 238539491968787122971889 := by
  unfold tailWord_4180986
  simp only [CollatzResearch.WordTrace]
  refine ⟨38123271807752313101260703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101662058154006168270028541 38123271807752313101260703)
  ·
    refine ⟨57184907711628469651891055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38123271807752313101260703 57184907711628469651891055)
    ·
      refine ⟨85777361567442704477836583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57184907711628469651891055 85777361567442704477836583)
      ·
        refine ⟨128666042351164056716754875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85777361567442704477836583 128666042351164056716754875)
        ·
          refine ⟨192999063526746085075132313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128666042351164056716754875 192999063526746085075132313)
          ·
            refine ⟨144749297645059563806349235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192999063526746085075132313 144749297645059563806349235)
            ·
              refine ⟨217123946467589345709523853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144749297645059563806349235 217123946467589345709523853)
              ·
                refine ⟨81421479925346004641071445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217123946467589345709523853 81421479925346004641071445)
                ·
                  refine ⟨238539491968787122971889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 81421479925346004641071445 238539491968787122971889)
                  ·
                    rfl

theorem cell23_4180986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 10].length) (baseStart_4180986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4180986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4180986 prefixEnd_4180986 := by exact prefixLift 4180986
  have htrace : WordTrace (prefixWord ++ tailWord_4180986) baseStart_4180986 baseEnd_4180986 := by
    simpa [prefixWord, tailWord_4180986, baseEnd_4180986] using wordTrace_append hprefix tailTrace_4180986
  have hstable : (prefixWord ++ tailWord_4180986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180986).length < 2 ^ (prefixWord ++ tailWord_4180986).sum := by decide
  have hdescent : baseEnd_4180986 < baseStart_4180986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181000 : List Nat := [2, 1, 3, 2, 1, 3, 2, 2, 2, 2, 3]
def baseStart_4181000 : Nat := 118140960795 + 4181000 * 2 ^ 59
def prefixEnd_4181000 : Nat := 4983230072969 + 3 ^ 40 * 4181000 * 2
def baseEnd_4181000 : Nat := 2146862616448247051971937

theorem tailTrace_4181000 : CollatzResearch.WordTrace tailWord_4181000 prefixEnd_4181000 2146862616448247051971937 := by
  unfold tailWord_4181000
  simp only [CollatzResearch.WordTrace]
  refine ⟨76246798926479266398026227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101662398568639021864034969 76246798926479266398026227)
  ·
    refine ⟨114370198389718899597039341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76246798926479266398026227 114370198389718899597039341)
    ·
      refine ⟨42888824396144587348889753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114370198389718899597039341 42888824396144587348889753)
      ·
        refine ⟨32166618297108440511667315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42888824396144587348889753 32166618297108440511667315)
        ·
          refine ⟨48249927445662660767500973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32166618297108440511667315 48249927445662660767500973)
          ·
            refine ⟨18093722792123497787812865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48249927445662660767500973 18093722792123497787812865)
            ·
              refine ⟨13570292094092623340859649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18093722792123497787812865 13570292094092623340859649)
              ·
                refine ⟨10177719070569467505644737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13570292094092623340859649 10177719070569467505644737)
                ·
                  refine ⟨7633289302927100629233553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10177719070569467505644737 7633289302927100629233553)
                  ·
                    refine ⟨5724966977195325471925165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7633289302927100629233553 5724966977195325471925165)
                    ·
                      refine ⟨2146862616448247051971937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5724966977195325471925165 2146862616448247051971937)
                      ·
                        rfl

theorem cell23_4181000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_4181000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181000 prefixEnd_4181000 := by exact prefixLift 4181000
  have htrace : WordTrace (prefixWord ++ tailWord_4181000) baseStart_4181000 baseEnd_4181000 := by
    simpa [prefixWord, tailWord_4181000, baseEnd_4181000] using wordTrace_append hprefix tailTrace_4181000
  have hstable : (prefixWord ++ tailWord_4181000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181000).length < 2 ^ (prefixWord ++ tailWord_4181000).sum := by decide
  have hdescent : baseEnd_4181000 < baseStart_4181000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181003 : List Nat := [1, 1, 1, 1, 6, 2, 1, 4, 6]
def baseStart_4181003 : Nat := 118140960795 + 4181003 * 2 ^ 59
def prefixEnd_4181003 : Nat := 4983230072969 + 3 ^ 40 * 4181003 * 2
def baseEnd_4181003 : Nat := 238540461876690060026047

theorem tailTrace_4181003 : CollatzResearch.WordTrace tailWord_4181003 prefixEnd_4181003 238540461876690060026047 := by
  unfold tailWord_4181003
  simp only [CollatzResearch.WordTrace]
  refine ⟨152493707271947664308411663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101662471514631776205607775 152493707271947664308411663)
  ·
    refine ⟨228740560907921496462617495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152493707271947664308411663 228740560907921496462617495)
    ·
      refine ⟨343110841361882244693926243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228740560907921496462617495 343110841361882244693926243)
      ·
        refine ⟨514666262042823367040889365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343110841361882244693926243 514666262042823367040889365)
        ·
          refine ⟨24124981033257345330041689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 514666262042823367040889365 24124981033257345330041689)
          ·
            refine ⟨18093735774943008997531267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24124981033257345330041689 18093735774943008997531267)
            ·
              refine ⟨27140603662414513496296901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18093735774943008997531267 27140603662414513496296901)
              ·
                refine ⟨5088863186702721280555669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27140603662414513496296901 5088863186702721280555669)
                ·
                  refine ⟨238540461876690060026047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5088863186702721280555669 238540461876690060026047)
                  ·
                    rfl

theorem cell23_4181003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 6].length) (baseStart_4181003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181003 prefixEnd_4181003 := by exact prefixLift 4181003
  have htrace : WordTrace (prefixWord ++ tailWord_4181003) baseStart_4181003 baseEnd_4181003 := by
    simpa [prefixWord, tailWord_4181003, baseEnd_4181003] using wordTrace_append hprefix tailTrace_4181003
  have hstable : (prefixWord ++ tailWord_4181003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181003).length < 2 ^ (prefixWord ++ tailWord_4181003).sum := by decide
  have hdescent : baseEnd_4181003 < baseStart_4181003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181034 : List Nat := [3, 1, 4, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_4181034 : Nat := 118140960795 + 4181034 * 2 ^ 59
def prefixEnd_4181034 : Nat := 4983230072969 + 3 ^ 40 * 4181034 * 2
def baseEnd_4181034 : Nat := 2146880074790499918946781

theorem tailTrace_4181034 : CollatzResearch.WordTrace tailWord_4181034 prefixEnd_4181034 2146880074790499918946781 := by
  unfold tailWord_4181034
  simp only [CollatzResearch.WordTrace]
  refine ⟨38123709483708839150697539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101663225289890237735193437 38123709483708839150697539)
  ·
    refine ⟨57185564225563258726046309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38123709483708839150697539 57185564225563258726046309)
    ·
      refine ⟨10722293292293111011133683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57185564225563258726046309 10722293292293111011133683)
      ·
        refine ⟨16083439938439666516700525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10722293292293111011133683 16083439938439666516700525)
        ·
          refine ⟨6031289976914874943762697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16083439938439666516700525 6031289976914874943762697)
          ·
            refine ⟨4523467482686156207822023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6031289976914874943762697 4523467482686156207822023)
            ·
              refine ⟨6785201224029234311733035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4523467482686156207822023 6785201224029234311733035)
              ·
                refine ⟨10177801836043851467599553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6785201224029234311733035 10177801836043851467599553)
                ·
                  refine ⟨7633351377032888600699665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10177801836043851467599553 7633351377032888600699665)
                  ·
                    refine ⟨5725013532774666450524749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7633351377032888600699665 5725013532774666450524749)
                    ·
                      refine ⟨2146880074790499918946781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5725013532774666450524749 2146880074790499918946781)
                      ·
                        rfl

theorem cell23_4181034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_4181034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181034 prefixEnd_4181034 := by exact prefixLift 4181034
  have htrace : WordTrace (prefixWord ++ tailWord_4181034) baseStart_4181034 baseEnd_4181034 := by
    simpa [prefixWord, tailWord_4181034, baseEnd_4181034] using wordTrace_append hprefix tailTrace_4181034
  have hstable : (prefixWord ++ tailWord_4181034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181034).length < 2 ^ (prefixWord ++ tailWord_4181034).sum := by decide
  have hdescent : baseEnd_4181034 < baseStart_4181034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181040 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 1, 5, 2]
def baseStart_4181040 : Nat := 118140960795 + 4181040 * 2 ^ 59
def prefixEnd_4181040 : Nat := 4983230072969 + 3 ^ 40 * 4181040 * 2
def baseEnd_4181040 : Nat := 2146883155674426895471753

theorem tailTrace_4181040 : CollatzResearch.WordTrace tailWord_4181040 prefixEnd_4181040 2146883155674426895471753 := by
  unfold tailWord_4181040
  simp only [CollatzResearch.WordTrace]
  refine ⟨76247528386406809813754287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101663371181875746418339049 76247528386406809813754287)
  ·
    refine ⟨114371292579610214720631431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76247528386406809813754287 114371292579610214720631431)
    ·
      refine ⟨171556938869415322080947147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114371292579610214720631431 171556938869415322080947147)
      ·
        refine ⟨257335408304122983121420721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171556938869415322080947147 257335408304122983121420721)
        ·
          refine ⟨193001556228092237341065541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257335408304122983121420721 193001556228092237341065541)
          ·
            refine ⟨36187791792767294501449789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193001556228092237341065541 36187791792767294501449789)
            ·
              refine ⟨13570421922287735438043671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36187791792767294501449789 13570421922287735438043671)
              ·
                refine ⟨20355632883431603157065507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13570421922287735438043671 20355632883431603157065507)
                ·
                  refine ⟨30533449325147404735598261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20355632883431603157065507 30533449325147404735598261)
                  ·
                    refine ⟨2862510874232569193962337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30533449325147404735598261 2862510874232569193962337)
                    ·
                      refine ⟨2146883155674426895471753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2862510874232569193962337 2146883155674426895471753)
                      ·
                        rfl

theorem cell23_4181040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 1, 5, 2].length) (baseStart_4181040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181040 prefixEnd_4181040 := by exact prefixLift 4181040
  have htrace : WordTrace (prefixWord ++ tailWord_4181040) baseStart_4181040 baseEnd_4181040 := by
    simpa [prefixWord, tailWord_4181040, baseEnd_4181040] using wordTrace_append hprefix tailTrace_4181040
  have hstable : (prefixWord ++ tailWord_4181040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181040).length < 2 ^ (prefixWord ++ tailWord_4181040).sum := by decide
  have hdescent : baseEnd_4181040 < baseStart_4181040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181073 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 3, 1, 5]
def baseStart_4181073 : Nat := 118140960795 + 4181073 * 2 ^ 59
def prefixEnd_4181073 : Nat := 4983230072969 + 3 ^ 40 * 4181073 * 2
def baseEnd_4181073 : Nat := 2146900100536025266359101

theorem tailTrace_4181073 : CollatzResearch.WordTrace tailWord_4181073 prefixEnd_4181073 2146900100536025266359101 := by
  unfold tailWord_4181073
  simp only [CollatzResearch.WordTrace]
  refine ⟨152496260381694066263459873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101664173587796044175639915 152496260381694066263459873)
  ·
    refine ⟨114372195286270549697594905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152496260381694066263459873 114372195286270549697594905)
    ·
      refine ⟨85779146464702912273196179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114372195286270549697594905 85779146464702912273196179)
      ·
        refine ⟨128668719697054368409794269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85779146464702912273196179 128668719697054368409794269)
        ·
          refine ⟨48250769886395388153672851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128668719697054368409794269 48250769886395388153672851)
          ·
            refine ⟨72376154829593082230509277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48250769886395388153672851 72376154829593082230509277)
            ·
              refine ⟨27141058061097405836440979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72376154829593082230509277 27141058061097405836440979)
              ·
                refine ⟨40711587091646108754661469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27141058061097405836440979 40711587091646108754661469)
                ·
                  refine ⟨15266845159367290782998051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40711587091646108754661469 15266845159367290782998051)
                  ·
                    refine ⟨22900267739050936174497077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15266845159367290782998051 22900267739050936174497077)
                    ·
                      refine ⟨2146900100536025266359101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22900267739050936174497077 2146900100536025266359101)
                      ·
                        rfl

theorem cell23_4181073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_4181073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181073 prefixEnd_4181073 := by exact prefixLift 4181073
  have htrace : WordTrace (prefixWord ++ tailWord_4181073) baseStart_4181073 baseEnd_4181073 := by
    simpa [prefixWord, tailWord_4181073, baseEnd_4181073] using wordTrace_append hprefix tailTrace_4181073
  have hstable : (prefixWord ++ tailWord_4181073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181073).length < 2 ^ (prefixWord ++ tailWord_4181073).sum := by decide
  have hdescent : baseEnd_4181073 < baseStart_4181073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181087 : List Nat := [1, 1, 2, 3, 1, 1, 3, 4, 3, 2, 2]
def baseStart_4181087 : Nat := 118140960795 + 4181087 * 2 ^ 59
def prefixEnd_4181087 : Nat := 4983230072969 + 3 ^ 40 * 4181087 * 2
def baseEnd_4181087 : Nat := 2146907289265188211584037

theorem tailTrace_4181087 : CollatzResearch.WordTrace tailWord_4181087 prefixEnd_4181087 2146907289265188211584037 := by
  unfold tailWord_4181087
  simp only [CollatzResearch.WordTrace]
  refine ⟨152496771003643346654469515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101664514002428897769646343 152496771003643346654469515)
  ·
    refine ⟨228745156505465019981704273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152496771003643346654469515 228745156505465019981704273)
    ·
      refine ⟨171558867379098764986278205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228745156505465019981704273 171558867379098764986278205)
      ·
        refine ⟨64334575267162036869854327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171558867379098764986278205 64334575267162036869854327)
        ·
          refine ⟨96501862900743055304781491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64334575267162036869854327 96501862900743055304781491)
          ·
            refine ⟨144752794351114582957172237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96501862900743055304781491 144752794351114582957172237)
            ·
              refine ⟨54282297881667968608939589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144752794351114582957172237 54282297881667968608939589)
              ·
                refine ⟨10177930852812744114176173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54282297881667968608939589 10177930852812744114176173)
                ·
                  refine ⟨3816724069804779042816065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10177930852812744114176173 3816724069804779042816065)
                  ·
                    refine ⟨2862543052353584282112049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3816724069804779042816065 2862543052353584282112049)
                    ·
                      refine ⟨2146907289265188211584037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2862543052353584282112049 2146907289265188211584037)
                      ·
                        rfl

theorem cell23_4181087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 2, 2].length) (baseStart_4181087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181087 prefixEnd_4181087 := by exact prefixLift 4181087
  have htrace : WordTrace (prefixWord ++ tailWord_4181087) baseStart_4181087 baseEnd_4181087 := by
    simpa [prefixWord, tailWord_4181087, baseEnd_4181087] using wordTrace_append hprefix tailTrace_4181087
  have hstable : (prefixWord ++ tailWord_4181087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181087).length < 2 ^ (prefixWord ++ tailWord_4181087).sum := by decide
  have hdescent : baseEnd_4181087 < baseStart_4181087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181093 : List Nat := [1, 3, 1, 3, 2, 1, 3, 9]
def baseStart_4181093 : Nat := 118140960795 + 4181093 * 2 ^ 59
def prefixEnd_4181093 : Nat := 4983230072969 + 3 ^ 40 * 4181093 * 2
def baseEnd_4181093 : Nat := 79515198894411673633667

theorem tailTrace_4181093 : CollatzResearch.WordTrace tailWord_4181093 prefixEnd_4181093 79515198894411673633667 := by
  unfold tailWord_4181093
  simp only [CollatzResearch.WordTrace]
  refine ⟨152496989841621609679187933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101664659894414406452791955 152496989841621609679187933)
  ·
    refine ⟨57186371190608103629695475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152496989841621609679187933 57186371190608103629695475)
    ·
      refine ⟨85779556785912155444543213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57186371190608103629695475 85779556785912155444543213)
      ·
        refine ⟨32167333794717058291703705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85779556785912155444543213 32167333794717058291703705)
        ·
          refine ⟨24125500346037793718777779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32167333794717058291703705 24125500346037793718777779)
          ·
            refine ⟨36188250519056690578166669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24125500346037793718777779 36188250519056690578166669)
            ·
              refine ⟨13570593944646258966812501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36188250519056690578166669 13570593944646258966812501)
              ·
                refine ⟨79515198894411673633667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13570593944646258966812501 79515198894411673633667)
                ·
                  rfl

theorem cell23_4181093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 9].length) (baseStart_4181093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181093 prefixEnd_4181093 := by exact prefixLift 4181093
  have htrace : WordTrace (prefixWord ++ tailWord_4181093) baseStart_4181093 baseEnd_4181093 := by
    simpa [prefixWord, tailWord_4181093, baseEnd_4181093] using wordTrace_append hprefix tailTrace_4181093
  have hstable : (prefixWord ++ tailWord_4181093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181093).length < 2 ^ (prefixWord ++ tailWord_4181093).sum := by decide
  have hdescent : baseEnd_4181093 < baseStart_4181093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181121 : List Nat := [1, 2, 4, 2, 2, 3, 1, 1, 3, 2, 2]
def baseStart_4181121 : Nat := 118140960795 + 4181121 * 2 ^ 59
def prefixEnd_4181121 : Nat := 4983230072969 + 3 ^ 40 * 4181121 * 2
def baseEnd_4181121 : Nat := 2146924747607441078558881

theorem tailTrace_4181121 : CollatzResearch.WordTrace tailWord_4181121 prefixEnd_4181121 2146924747607441078558881 := by
  unfold tailWord_4181121
  simp only [CollatzResearch.WordTrace]
  refine ⟨152498011085520170461207217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101665340723680113640804811 152498011085520170461207217)
  ·
    refine ⟨114373508314140127845905413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152498011085520170461207217 114373508314140127845905413)
    ·
      refine ⟨21445032808901273971107265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114373508314140127845905413 21445032808901273971107265)
      ·
        refine ⟨16083774606675955478330449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21445032808901273971107265 16083774606675955478330449)
        ·
          refine ⟨12062830955006966608747837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16083774606675955478330449 12062830955006966608747837)
          ·
            refine ⟨4523561608127612478280439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12062830955006966608747837 4523561608127612478280439)
            ·
              refine ⟨6785342412191418717420659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4523561608127612478280439 6785342412191418717420659)
              ·
                refine ⟨10178013618287128076130989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6785342412191418717420659 10178013618287128076130989)
                ·
                  refine ⟨3816755106857673028549121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10178013618287128076130989 3816755106857673028549121)
                  ·
                    refine ⟨2862566330143254771411841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3816755106857673028549121 2862566330143254771411841)
                    ·
                      refine ⟨2146924747607441078558881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2862566330143254771411841 2146924747607441078558881)
                      ·
                        rfl

theorem cell23_4181121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_4181121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181121 prefixEnd_4181121 := by exact prefixLift 4181121
  have htrace : WordTrace (prefixWord ++ tailWord_4181121) baseStart_4181121 baseEnd_4181121 := by
    simpa [prefixWord, tailWord_4181121, baseEnd_4181121] using wordTrace_append hprefix tailTrace_4181121
  have hstable : (prefixWord ++ tailWord_4181121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181121).length < 2 ^ (prefixWord ++ tailWord_4181121).sum := by decide
  have hdescent : baseEnd_4181121 < baseStart_4181121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181123 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 2, 7]
def baseStart_4181123 : Nat := 118140960795 + 4181123 * 2 ^ 59
def prefixEnd_4181123 : Nat := 4983230072969 + 3 ^ 40 * 4181123 * 2
def baseEnd_4181123 : Nat := 715641924856250023577957

theorem tailTrace_4181123 : CollatzResearch.WordTrace tailWord_4181123 prefixEnd_4181123 715641924856250023577957 := by
  unfold tailWord_4181123
  simp only [CollatzResearch.WordTrace]
  refine ⟨152498084031512924802780023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101665389354341949868520015 152498084031512924802780023)
  ·
    refine ⟨228747126047269387204170035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152498084031512924802780023 228747126047269387204170035)
    ·
      refine ⟨343120689070904080806255053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228747126047269387204170035 343120689070904080806255053)
      ·
        refine ⟨128670258401589030302345645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343120689070904080806255053 128670258401589030302345645)
        ·
          refine ⟨48251346900595886363379617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128670258401589030302345645 48251346900595886363379617)
          ·
            refine ⟨36188510175446914772534713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48251346900595886363379617 36188510175446914772534713)
            ·
              refine ⟨27141382631585186079401035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36188510175446914772534713 27141382631585186079401035)
              ·
                refine ⟨40712073947377779119101553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27141382631585186079401035 40712073947377779119101553)
                ·
                  refine ⟨30534055460533334339326165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40712073947377779119101553 30534055460533334339326165)
                  ·
                    refine ⟨715641924856250023577957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30534055460533334339326165 715641924856250023577957)
                    ·
                      rfl

theorem cell23_4181123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 7].length) (baseStart_4181123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181123 prefixEnd_4181123 := by exact prefixLift 4181123
  have htrace : WordTrace (prefixWord ++ tailWord_4181123) baseStart_4181123 baseEnd_4181123 := by
    simpa [prefixWord, tailWord_4181123, baseEnd_4181123] using wordTrace_append hprefix tailTrace_4181123
  have hstable : (prefixWord ++ tailWord_4181123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181123).length < 2 ^ (prefixWord ++ tailWord_4181123).sum := by decide
  have hdescent : baseEnd_4181123 < baseStart_4181123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181154 : List Nat := [3, 3, 1, 3, 2, 1, 1, 2, 1, 3, 3]
def baseStart_4181154 : Nat := 118140960795 + 4181154 * 2 ^ 59
def prefixEnd_4181154 : Nat := 4983230072969 + 3 ^ 40 * 4181154 * 2
def baseEnd_4181154 : Nat := 2146941692469039449446229

theorem tailTrace_4181154 : CollatzResearch.WordTrace tailWord_4181154 prefixEnd_4181154 2146941692469039449446229 := by
  unfold tailWord_4181154
  simp only [CollatzResearch.WordTrace]
  refine ⟨38124803673600154274289629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101666143129600411398105677 38124803673600154274289629)
  ·
    refine ⟨14296801377600057852858611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38124803673600154274289629 14296801377600057852858611)
    ·
      refine ⟨21445202066400086779287917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14296801377600057852858611 21445202066400086779287917)
      ·
        refine ⟨8041950774900032542232969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21445202066400086779287917 8041950774900032542232969)
        ·
          refine ⟨6031463081175024406674727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8041950774900032542232969 6031463081175024406674727)
          ·
            refine ⟨9047194621762536610012091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6031463081175024406674727 9047194621762536610012091)
            ·
              refine ⟨13570791932643804915018137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9047194621762536610012091 13570791932643804915018137)
              ·
                refine ⟨10178093949482853686263603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13570791932643804915018137 10178093949482853686263603)
                ·
                  refine ⟨15267140924224280529395405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10178093949482853686263603 15267140924224280529395405)
                  ·
                    refine ⟨5725177846584105198523277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15267140924224280529395405 5725177846584105198523277)
                    ·
                      refine ⟨2146941692469039449446229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5725177846584105198523277 2146941692469039449446229)
                      ·
                        rfl

theorem cell23_4181154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_4181154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181154 prefixEnd_4181154 := by exact prefixLift 4181154
  have htrace : WordTrace (prefixWord ++ tailWord_4181154) baseStart_4181154 baseEnd_4181154 := by
    simpa [prefixWord, tailWord_4181154, baseEnd_4181154] using wordTrace_append hprefix tailTrace_4181154
  have hstable : (prefixWord ++ tailWord_4181154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181154).length < 2 ^ (prefixWord ++ tailWord_4181154).sum := by decide
  have hdescent : baseEnd_4181154 < baseStart_4181154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181193 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 7]
def baseStart_4181193 : Nat := 118140960795 + 4181193 * 2 ^ 59
def prefixEnd_4181193 : Nat := 4983230072969 + 3 ^ 40 * 4181193 * 2
def baseEnd_4181193 : Nat := 2146961718214564796858549

theorem tailTrace_4181193 : CollatzResearch.WordTrace tailWord_4181193 prefixEnd_4181193 2146961718214564796858549 := by
  unfold tailWord_4181193
  simp only [CollatzResearch.WordTrace]
  refine ⟨152500637141259326757828233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101667091427506217838552155 152500637141259326757828233)
  ·
    refine ⟨114375477855944495068371175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152500637141259326757828233 114375477855944495068371175)
    ·
      refine ⟨171563216783916742602556763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114375477855944495068371175 171563216783916742602556763)
      ·
        refine ⟨257344825175875113903835145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171563216783916742602556763 257344825175875113903835145)
        ·
          refine ⟨193008618881906335427876359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257344825175875113903835145 193008618881906335427876359)
          ·
            refine ⟨289512928322859503141814539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193008618881906335427876359 289512928322859503141814539)
            ·
              refine ⟨434269392484289254712721809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289512928322859503141814539 434269392484289254712721809)
              ·
                refine ⟨325702044363216941034541357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 434269392484289254712721809 325702044363216941034541357)
                ·
                  refine ⟨122138266636206352887953009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325702044363216941034541357 122138266636206352887953009)
                  ·
                    refine ⟨91603699977154764665964757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122138266636206352887953009 91603699977154764665964757)
                    ·
                      refine ⟨2146961718214564796858549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91603699977154764665964757 2146961718214564796858549)
                      ·
                        rfl

theorem cell23_4181193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_4181193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181193 prefixEnd_4181193 := by exact prefixLift 4181193
  have htrace : WordTrace (prefixWord ++ tailWord_4181193) baseStart_4181193 baseEnd_4181193 := by
    simpa [prefixWord, tailWord_4181193, baseEnd_4181193] using wordTrace_append hprefix tailTrace_4181193
  have hstable : (prefixWord ++ tailWord_4181193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181193).length < 2 ^ (prefixWord ++ tailWord_4181193).sum := by decide
  have hdescent : baseEnd_4181193 < baseStart_4181193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181194 : List Nat := [3, 1, 2, 1, 3, 3, 2, 1, 1, 4, 2]
def baseStart_4181194 : Nat := 118140960795 + 4181194 * 2 ^ 59
def prefixEnd_4181194 : Nat := 4983230072969 + 3 ^ 40 * 4181194 * 2
def baseEnd_4181194 : Nat := 2146962231695219292946045

theorem tailTrace_4181194 : CollatzResearch.WordTrace tailWord_4181194 prefixEnd_4181194 2146962231695219292946045 := by
  unfold tailWord_4181194
  simp only [CollatzResearch.WordTrace]
  refine ⟨38125168403563925982153659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101667115742837135952409757 38125168403563925982153659)
  ·
    refine ⟨57187752605345888973230489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38125168403563925982153659 57187752605345888973230489)
    ·
      refine ⟨42890814454009416729922867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57187752605345888973230489 42890814454009416729922867)
      ·
        refine ⟨64336221681014125094884301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42890814454009416729922867 64336221681014125094884301)
        ·
          refine ⟨24126083130380296910581613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64336221681014125094884301 24126083130380296910581613)
          ·
            refine ⟨9047281173892611341468105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24126083130380296910581613 9047281173892611341468105)
            ·
              refine ⟨6785460880419458506101079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9047281173892611341468105 6785460880419458506101079)
              ·
                refine ⟨10178191320629187759151619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6785460880419458506101079 10178191320629187759151619)
                ·
                  refine ⟨15267286980943781638727429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10178191320629187759151619 15267286980943781638727429)
                  ·
                    refine ⟨2862616308926959057261393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15267286980943781638727429 2862616308926959057261393)
                    ·
                      refine ⟨2146962231695219292946045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2862616308926959057261393 2146962231695219292946045)
                      ·
                        rfl

theorem cell23_4181194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 1, 4, 2].length) (baseStart_4181194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181194 prefixEnd_4181194 := by exact prefixLift 4181194
  have htrace : WordTrace (prefixWord ++ tailWord_4181194) baseStart_4181194 baseEnd_4181194 := by
    simpa [prefixWord, tailWord_4181194, baseEnd_4181194] using wordTrace_append hprefix tailTrace_4181194
  have hstable : (prefixWord ++ tailWord_4181194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181194).length < 2 ^ (prefixWord ++ tailWord_4181194).sum := by decide
  have hdescent : baseEnd_4181194 < baseStart_4181194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181203 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 8]
def baseStart_4181203 : Nat := 118140960795 + 4181203 * 2 ^ 59
def prefixEnd_4181203 : Nat := 4983230072969 + 3 ^ 40 * 4181203 * 2
def baseEnd_4181203 : Nat := 2146966853021109757733503

theorem tailTrace_4181203 : CollatzResearch.WordTrace tailWord_4181203 prefixEnd_4181203 2146966853021109757733503 := by
  unfold tailWord_4181203
  simp only [CollatzResearch.WordTrace]
  refine ⟨152501001871223098465692263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101667334580815398977128175 152501001871223098465692263)
  ·
    refine ⟨228751502806834647698538395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152501001871223098465692263 228751502806834647698538395)
    ·
      refine ⟨343127254210251971547807593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228751502806834647698538395 343127254210251971547807593)
      ·
        refine ⟨257345440657688978660855695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343127254210251971547807593 257345440657688978660855695)
        ·
          refine ⟨386018160986533467991283543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257345440657688978660855695 386018160986533467991283543)
          ·
            refine ⟨579027241479800201986925315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386018160986533467991283543 579027241479800201986925315)
            ·
              refine ⟨868540862219700302980387973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579027241479800201986925315 868540862219700302980387973)
              ·
                refine ⟨162851411666193806808822745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 868540862219700302980387973 162851411666193806808822745)
                ·
                  refine ⟨122138558749645355106617059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162851411666193806808822745 122138558749645355106617059)
                  ·
                    refine ⟨183207838124468032659925589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 122138558749645355106617059 183207838124468032659925589)
                    ·
                      refine ⟨2146966853021109757733503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 183207838124468032659925589 2146966853021109757733503)
                      ·
                        rfl

theorem cell23_4181203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_4181203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181203 prefixEnd_4181203 := by exact prefixLift 4181203
  have htrace : WordTrace (prefixWord ++ tailWord_4181203) baseStart_4181203 baseEnd_4181203 := by
    simpa [prefixWord, tailWord_4181203, baseEnd_4181203] using wordTrace_append hprefix tailTrace_4181203
  have hstable : (prefixWord ++ tailWord_4181203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181203).length < 2 ^ (prefixWord ++ tailWord_4181203).sum := by decide
  have hdescent : baseEnd_4181203 < baseStart_4181203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181210 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3]
def baseStart_4181210 : Nat := 118140960795 + 4181210 * 2 ^ 59
def prefixEnd_4181210 : Nat := 4983230072969 + 3 ^ 40 * 4181210 * 2
def baseEnd_4181210 : Nat := 2146970447385691230345971

theorem tailTrace_4181210 : CollatzResearch.WordTrace tailWord_4181210 prefixEnd_4181210 2146970447385691230345971 := by
  unfold tailWord_4181210
  simp only [CollatzResearch.WordTrace]
  refine ⟨38125314295549434665299271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101667504788131825774131389 38125314295549434665299271)
  ·
    refine ⟨57187971443324151997948907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38125314295549434665299271 57187971443324151997948907)
    ·
      refine ⟨85781957164986227996923361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57187971443324151997948907 85781957164986227996923361)
      ·
        refine ⟨64336467873739670997692521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85781957164986227996923361 64336467873739670997692521)
        ·
          refine ⟨48252350905304753248269391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64336467873739670997692521 48252350905304753248269391)
          ·
            refine ⟨72378526357957129872404087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48252350905304753248269391 72378526357957129872404087)
            ·
              refine ⟨108567789536935694808606131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72378526357957129872404087 108567789536935694808606131)
              ·
                refine ⟨162851684305403542212909197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108567789536935694808606131 162851684305403542212909197)
                ·
                  refine ⟨61069381614526328329840949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162851684305403542212909197 61069381614526328329840949)
                  ·
                    refine ⟨5725254526361843280922589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61069381614526328329840949 5725254526361843280922589)
                    ·
                      refine ⟨2146970447385691230345971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5725254526361843280922589 2146970447385691230345971)
                      ·
                        rfl

theorem cell23_4181210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_4181210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181210 prefixEnd_4181210 := by exact prefixLift 4181210
  have htrace : WordTrace (prefixWord ++ tailWord_4181210) baseStart_4181210 baseEnd_4181210 := by
    simpa [prefixWord, tailWord_4181210, baseEnd_4181210] using wordTrace_append hprefix tailTrace_4181210
  have hstable : (prefixWord ++ tailWord_4181210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181210).length < 2 ^ (prefixWord ++ tailWord_4181210).sum := by decide
  have hdescent : baseEnd_4181210 < baseStart_4181210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181217 : List Nat := [1, 2, 3, 1, 3, 2, 1, 5, 5]
def baseStart_4181217 : Nat := 118140960795 + 4181217 * 2 ^ 59
def prefixEnd_4181217 : Nat := 4983230072969 + 3 ^ 40 * 4181217 * 2
def baseEnd_4181217 : Nat := 238552671305585855884271

theorem tailTrace_4181217 : CollatzResearch.WordTrace tailWord_4181217 prefixEnd_4181217 238552671305585855884271 := by
  unfold tailWord_4181217
  simp only [CollatzResearch.WordTrace]
  refine ⟨152501512493172378856701905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101667674995448252571134603 152501512493172378856701905)
  ·
    refine ⟨114376134369879284142526429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152501512493172378856701905 114376134369879284142526429)
    ·
      refine ⟨42891050388704731553447411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114376134369879284142526429 42891050388704731553447411)
      ·
        refine ⟨64336575583057097330171117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42891050388704731553447411 64336575583057097330171117)
        ·
          refine ⟨24126215843646411498814169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64336575583057097330171117 24126215843646411498814169)
          ·
            refine ⟨18094661882734808624110627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24126215843646411498814169 18094661882734808624110627)
            ·
              refine ⟨27141992824102212936165941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18094661882734808624110627 27141992824102212936165941)
              ·
                refine ⟨2544561827259582462765557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27141992824102212936165941 2544561827259582462765557)
                ·
                  refine ⟨238552671305585855884271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2544561827259582462765557 238552671305585855884271)
                  ·
                    rfl

theorem cell23_4181217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 5].length) (baseStart_4181217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181217 prefixEnd_4181217 := by exact prefixLift 4181217
  have htrace : WordTrace (prefixWord ++ tailWord_4181217) baseStart_4181217 baseEnd_4181217 := by
    simpa [prefixWord, tailWord_4181217, baseEnd_4181217] using wordTrace_append hprefix tailTrace_4181217
  have hstable : (prefixWord ++ tailWord_4181217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181217).length < 2 ^ (prefixWord ++ tailWord_4181217).sum := by decide
  have hdescent : baseEnd_4181217 < baseStart_4181217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181327 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 5, 5, 2]
def baseStart_4181327 : Nat := 118140960795 + 4181327 * 2 ^ 59
def prefixEnd_4181327 : Nat := 4983230072969 + 3 ^ 40 * 4181327 * 2
def baseEnd_4181327 : Nat := 2147030524622267272582933

theorem tailTrace_4181327 : CollatzResearch.WordTrace tailWord_4181327 prefixEnd_4181327 2147030524622267272582933 := by
  unfold tailWord_4181327
  simp only [CollatzResearch.WordTrace]
  refine ⟨152505524522773867643206235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101670349681849245095470823 152505524522773867643206235)
  ·
    refine ⟨228758286784160801464809353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152505524522773867643206235 228758286784160801464809353)
    ·
      refine ⟨171568715088120601098607015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228758286784160801464809353 171568715088120601098607015)
      ·
        refine ⟨257353072632180901647910523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171568715088120601098607015 257353072632180901647910523)
        ·
          refine ⟨386029608948271352471865785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257353072632180901647910523 386029608948271352471865785)
          ·
            refine ⟨289522206711203514353899339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386029608948271352471865785 289522206711203514353899339)
            ·
              refine ⟨434283310066805271530849009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289522206711203514353899339 434283310066805271530849009)
              ·
                refine ⟨325712482550103953648136757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 434283310066805271530849009 325712482550103953648136757)
                ·
                  refine ⟨30535545239072245654512821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 325712482550103953648136757 30535545239072245654512821)
                  ·
                    refine ⟨2862707366163023030110577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30535545239072245654512821 2862707366163023030110577)
                    ·
                      refine ⟨2147030524622267272582933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2862707366163023030110577 2147030524622267272582933)
                      ·
                        rfl

theorem cell23_4181327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 5, 2].length) (baseStart_4181327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181327 prefixEnd_4181327 := by exact prefixLift 4181327
  have htrace : WordTrace (prefixWord ++ tailWord_4181327) baseStart_4181327 baseEnd_4181327 := by
    simpa [prefixWord, tailWord_4181327, baseEnd_4181327] using wordTrace_append hprefix tailTrace_4181327
  have hstable : (prefixWord ++ tailWord_4181327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181327).length < 2 ^ (prefixWord ++ tailWord_4181327).sum := by decide
  have hdescent : baseEnd_4181327 < baseStart_4181327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181337 : List Nat := [1, 2, 1, 2, 2, 2, 2, 5, 1, 5]
def baseStart_4181337 : Nat := 118140960795 + 4181337 * 2 ^ 59
def prefixEnd_4181337 : Nat := 4983230072969 + 3 ^ 40 * 4181337 * 2
def baseEnd_4181337 : Nat := 715678553142937411152629

theorem tailTrace_4181337 : CollatzResearch.WordTrace tailWord_4181337 prefixEnd_4181337 715678553142937411152629 := by
  unfold tailWord_4181337
  simp only [CollatzResearch.WordTrace]
  refine ⟨152505889252737639351070265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101670592835158426234046843 152505889252737639351070265)
  ·
    refine ⟨114379416939553229513302699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152505889252737639351070265 114379416939553229513302699)
    ·
      refine ⟨171569125409329844269954049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114379416939553229513302699 171569125409329844269954049)
      ·
        refine ⟨128676844056997383202465537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171569125409329844269954049 128676844056997383202465537)
        ·
          refine ⟨96507633042748037401849153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128676844056997383202465537 96507633042748037401849153)
          ·
            refine ⟨72380724782061028051386865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96507633042748037401849153 72380724782061028051386865)
            ·
              refine ⟨54285543586545771038540149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72380724782061028051386865 54285543586545771038540149)
              ·
                refine ⟨5089269711238666034863139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54285543586545771038540149 5089269711238666034863139)
                ·
                  refine ⟨7633904566857999052294709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5089269711238666034863139 7633904566857999052294709)
                  ·
                    refine ⟨715678553142937411152629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7633904566857999052294709 715678553142937411152629)
                    ·
                      rfl

theorem cell23_4181337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 5].length) (baseStart_4181337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181337 prefixEnd_4181337 := by exact prefixLift 4181337
  have htrace : WordTrace (prefixWord ++ tailWord_4181337) baseStart_4181337 baseEnd_4181337 := by
    simpa [prefixWord, tailWord_4181337, baseEnd_4181337] using wordTrace_append hprefix tailTrace_4181337
  have hstable : (prefixWord ++ tailWord_4181337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181337).length < 2 ^ (prefixWord ++ tailWord_4181337).sum := by decide
  have hdescent : baseEnd_4181337 < baseStart_4181337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181367 : List Nat := [1, 1, 3, 1, 1, 2, 6, 1, 1, 6]
def baseStart_4181367 : Nat := 118140960795 + 4181367 * 2 ^ 59
def prefixEnd_4181367 : Nat := 4983230072969 + 3 ^ 40 * 4181367 * 2
def baseEnd_4181367 : Nat := 715683687949482372027583

theorem tailTrace_4181367 : CollatzResearch.WordTrace tailWord_4181367 prefixEnd_4181367 715683687949482372027583 := by
  unfold tailWord_4181367
  simp only [CollatzResearch.WordTrace]
  refine ⟨152506983442628954474662355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101671322295085969649774903 152506983442628954474662355)
  ·
    refine ⟨228760475163943431711993533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152506983442628954474662355 228760475163943431711993533)
    ·
      refine ⟨85785178186478786891997575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228760475163943431711993533 85785178186478786891997575)
      ·
        refine ⟨128677767279718180337996363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85785178186478786891997575 128677767279718180337996363)
        ·
          refine ⟨193016650919577270506994545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128677767279718180337996363 193016650919577270506994545)
          ·
            refine ⟨144762488189682952880245909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193016650919577270506994545 144762488189682952880245909)
            ·
              refine ⟨6785741633891388416261527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144762488189682952880245909 6785741633891388416261527)
              ·
                refine ⟨10178612450837082624392291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6785741633891388416261527 10178612450837082624392291)
                ·
                  refine ⟨15267918676255623936588437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10178612450837082624392291 15267918676255623936588437)
                  ·
                    refine ⟨715683687949482372027583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15267918676255623936588437 715683687949482372027583)
                    ·
                      rfl

theorem cell23_4181367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 6].length) (baseStart_4181367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181367 prefixEnd_4181367 := by exact prefixLift 4181367
  have htrace : WordTrace (prefixWord ++ tailWord_4181367) baseStart_4181367 baseEnd_4181367 := by
    simpa [prefixWord, tailWord_4181367, baseEnd_4181367] using wordTrace_append hprefix tailTrace_4181367
  have hstable : (prefixWord ++ tailWord_4181367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181367).length < 2 ^ (prefixWord ++ tailWord_4181367).sum := by decide
  have hdescent : baseEnd_4181367 < baseStart_4181367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181378 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_4181378 : Nat := 118140960795 + 4181378 * 2 ^ 59
def prefixEnd_4181378 : Nat := 4983230072969 + 3 ^ 40 * 4181378 * 2
def baseEnd_4181378 : Nat := 2147056712135646573045199

theorem tailTrace_4181378 : CollatzResearch.WordTrace tailWord_4181378 prefixEnd_4181378 2147056712135646573045199 := by
  unfold tailWord_4181378
  simp only [CollatzResearch.WordTrace]
  refine ⟨38126846161397275838328197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101671589763726068902208525 38126846161397275838328197)
  ·
    refine ⟨7148783655261989219686537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38126846161397275838328197 7148783655261989219686537)
    ·
      refine ⟨5361587741446491914764903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7148783655261989219686537 5361587741446491914764903)
      ·
        refine ⟨8042381612169737872147355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5361587741446491914764903 8042381612169737872147355)
        ·
          refine ⟨12063572418254606808221033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8042381612169737872147355 12063572418254606808221033)
          ·
            refine ⟨9047679313690955106165775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12063572418254606808221033 9047679313690955106165775)
            ·
              refine ⟨13571518970536432659248663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9047679313690955106165775 13571518970536432659248663)
              ·
                refine ⟨20357278455804648988872995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13571518970536432659248663 20357278455804648988872995)
                ·
                  refine ⟨30535917683706973483309493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20357278455804648988872995 30535917683706973483309493)
                  ·
                    refine ⟨2862742282847528764060265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30535917683706973483309493 2862742282847528764060265)
                    ·
                      refine ⟨2147056712135646573045199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2862742282847528764060265 2147056712135646573045199)
                      ·
                        rfl

theorem cell23_4181378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_4181378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181378 prefixEnd_4181378 := by exact prefixLift 4181378
  have htrace : WordTrace (prefixWord ++ tailWord_4181378) baseStart_4181378 baseEnd_4181378 := by
    simpa [prefixWord, tailWord_4181378, baseEnd_4181378] using wordTrace_append hprefix tailTrace_4181378
  have hstable : (prefixWord ++ tailWord_4181378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181378).length < 2 ^ (prefixWord ++ tailWord_4181378).sum := by decide
  have hdescent : baseEnd_4181378 < baseStart_4181378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181387 : List Nat := [1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 4]
def baseStart_4181387 : Nat := 118140960795 + 4181387 * 2 ^ 59
def prefixEnd_4181387 : Nat := 4983230072969 + 3 ^ 40 * 4181387 * 2
def baseEnd_4181387 : Nat := 2147061333461537037832657

theorem tailTrace_4181387 : CollatzResearch.WordTrace tailWord_4181387 prefixEnd_4181387 2147061333461537037832657 := by
  unfold tailWord_4181387
  simp only [CollatzResearch.WordTrace]
  refine ⟨152507712902556497890390415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101671808601704331926926943 152507712902556497890390415)
  ·
    refine ⟨228761569353834746835585623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152507712902556497890390415 228761569353834746835585623)
    ·
      refine ⟨343142354030752120253378435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228761569353834746835585623 343142354030752120253378435)
      ·
        refine ⟨514713531046128180380067653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343142354030752120253378435 514713531046128180380067653)
        ·
          refine ⟨96508787071149033821262685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 514713531046128180380067653 96508787071149033821262685)
          ·
            refine ⟨36190795151680887682973507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96508787071149033821262685 36190795151680887682973507)
            ·
              refine ⟨54286192727521331524460261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36190795151680887682973507 54286192727521331524460261)
              ·
                refine ⟨10178661136410249660836299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54286192727521331524460261 10178661136410249660836299)
                ·
                  refine ⟨15267991704615374491254449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10178661136410249660836299 15267991704615374491254449)
                  ·
                    refine ⟨11450993778461530868440837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15267991704615374491254449 11450993778461530868440837)
                    ·
                      refine ⟨2147061333461537037832657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11450993778461530868440837 2147061333461537037832657)
                      ·
                        rfl

theorem cell23_4181387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 4].length) (baseStart_4181387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181387 prefixEnd_4181387 := by exact prefixLift 4181387
  have htrace : WordTrace (prefixWord ++ tailWord_4181387) baseStart_4181387 baseEnd_4181387 := by
    simpa [prefixWord, tailWord_4181387, baseEnd_4181387] using wordTrace_append hprefix tailTrace_4181387
  have hstable : (prefixWord ++ tailWord_4181387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181387).length < 2 ^ (prefixWord ++ tailWord_4181387).sum := by decide
  have hdescent : baseEnd_4181387 < baseStart_4181387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181401 : List Nat := [1, 2, 1, 2, 1, 7, 1, 2, 2, 4]
def baseStart_4181401 : Nat := 118140960795 + 4181401 * 2 ^ 59
def prefixEnd_4181401 : Nat := 4983230072969 + 3 ^ 40 * 4181401 * 2
def baseEnd_4181401 : Nat := 715689507396899994352531

theorem tailTrace_4181401 : CollatzResearch.WordTrace tailWord_4181401 prefixEnd_4181401 715689507396899994352531 := by
  unfold tailWord_4181401
  simp only [CollatzResearch.WordTrace]
  refine ⟨152508223524505778281400057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101672149016337185520933371 152508223524505778281400057)
  ·
    refine ⟨114381167643379333711050043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152508223524505778281400057 114381167643379333711050043)
    ·
      refine ⟨171571751465069000566575065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114381167643379333711050043 171571751465069000566575065)
      ·
        refine ⟨128678813598801750424931299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171571751465069000566575065 128678813598801750424931299)
        ·
          refine ⟨193018220398202625637396949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128678813598801750424931299 193018220398202625637396949)
          ·
            refine ⟨4523864540582874038376491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 193018220398202625637396949 4523864540582874038376491)
            ·
              refine ⟨6785796810874311057564737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4523864540582874038376491 6785796810874311057564737)
              ·
                refine ⟨5089347608155733293173553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6785796810874311057564737 5089347608155733293173553)
                ·
                  refine ⟨3817010706116799969880165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5089347608155733293173553 3817010706116799969880165)
                  ·
                    refine ⟨715689507396899994352531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3817010706116799969880165 715689507396899994352531)
                    ·
                      rfl

theorem cell23_4181401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 4].length) (baseStart_4181401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181401 prefixEnd_4181401 := by exact prefixLift 4181401
  have htrace : WordTrace (prefixWord ++ tailWord_4181401) baseStart_4181401 baseEnd_4181401 := by
    simpa [prefixWord, tailWord_4181401, baseEnd_4181401] using wordTrace_append hprefix tailTrace_4181401
  have hstable : (prefixWord ++ tailWord_4181401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181401).length < 2 ^ (prefixWord ++ tailWord_4181401).sum := by decide
  have hdescent : baseEnd_4181401 < baseStart_4181401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181408 : List Nat := [2, 1, 1, 4, 1, 2, 1, 6, 1, 2, 2]
def baseStart_4181408 : Nat := 118140960795 + 4181408 * 2 ^ 59
def prefixEnd_4181408 : Nat := 4983230072969 + 3 ^ 40 * 4181408 * 2
def baseEnd_4181408 : Nat := 2147072116555281455670061

theorem tailTrace_4181408 : CollatzResearch.WordTrace tailWord_4181408 prefixEnd_4181408 2147072116555281455670061 := by
  unfold tailWord_4181408
  simp only [CollatzResearch.WordTrace]
  refine ⟨76254239417740209238452439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101672319223653612317936585 76254239417740209238452439)
  ·
    refine ⟨114381359126610313857678659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76254239417740209238452439 114381359126610313857678659)
    ·
      refine ⟨171572038689915470786517989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114381359126610313857678659 171572038689915470786517989)
      ·
        refine ⟨32169757254359150772472123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171572038689915470786517989 32169757254359150772472123)
        ·
          refine ⟨48254635881538726158708185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32169757254359150772472123 48254635881538726158708185)
          ·
            refine ⟨36190976911154044619031139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48254635881538726158708185 36190976911154044619031139)
            ·
              refine ⟨54286465366731066928546709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36190976911154044619031139 54286465366731066928546709)
              ·
                refine ⟨2544678064065518762275627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54286465366731066928546709 2544678064065518762275627)
                ·
                  refine ⟨3817017096098278143413441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2544678064065518762275627 3817017096098278143413441)
                  ·
                    refine ⟨2862762822073708607560081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3817017096098278143413441 2862762822073708607560081)
                    ·
                      refine ⟨2147072116555281455670061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2862762822073708607560081 2147072116555281455670061)
                      ·
                        rfl

theorem cell23_4181408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_4181408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181408 prefixEnd_4181408 := by exact prefixLift 4181408
  have htrace : WordTrace (prefixWord ++ tailWord_4181408) baseStart_4181408 baseEnd_4181408 := by
    simpa [prefixWord, tailWord_4181408, baseEnd_4181408] using wordTrace_append hprefix tailTrace_4181408
  have hstable : (prefixWord ++ tailWord_4181408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181408).length < 2 ^ (prefixWord ++ tailWord_4181408).sum := by decide
  have hdescent : baseEnd_4181408 < baseStart_4181408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181421 : List Nat := [1, 5, 2, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_4181421 : Nat := 118140960795 + 4181421 * 2 ^ 59
def prefixEnd_4181421 : Nat := 4983230072969 + 3 ^ 40 * 4181421 * 2
def baseEnd_4181421 : Nat := 2147078791803789904807501

theorem tailTrace_4181421 : CollatzResearch.WordTrace tailWord_4181421 prefixEnd_4181421 2147078791803789904807501 := by
  unfold tailWord_4181421
  simp only [CollatzResearch.WordTrace]
  refine ⟨152508952984433321697128117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101672635322955547798085411 152508952984433321697128117)
  ·
    refine ⟨14297714342290623909105761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152508952984433321697128117 14297714342290623909105761)
    ·
      refine ⟨10723285756717967931829321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14297714342290623909105761 10723285756717967931829321)
      ·
        refine ⟨8042464317538475948871991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10723285756717967931829321 8042464317538475948871991)
        ·
          refine ⟨12063696476307713923307987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8042464317538475948871991 12063696476307713923307987)
          ·
            refine ⟨18095544714461570884961981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12063696476307713923307987 18095544714461570884961981)
            ·
              refine ⟨6785829267923089081860743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18095544714461570884961981 6785829267923089081860743)
              ·
                refine ⟨10178743901884633622791115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6785829267923089081860743 10178743901884633622791115)
                ·
                  refine ⟨15268115852826950434186673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10178743901884633622791115 15268115852826950434186673)
                  ·
                    refine ⟨11451086889620212825640005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15268115852826950434186673 11451086889620212825640005)
                    ·
                      refine ⟨2147078791803789904807501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11451086889620212825640005 2147078791803789904807501)
                      ·
                        rfl

theorem cell23_4181421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_4181421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181421 prefixEnd_4181421 := by exact prefixLift 4181421
  have htrace : WordTrace (prefixWord ++ tailWord_4181421) baseStart_4181421 baseEnd_4181421 := by
    simpa [prefixWord, tailWord_4181421, baseEnd_4181421] using wordTrace_append hprefix tailTrace_4181421
  have hstable : (prefixWord ++ tailWord_4181421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181421).length < 2 ^ (prefixWord ++ tailWord_4181421).sum := by decide
  have hdescent : baseEnd_4181421 < baseStart_4181421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181437 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 1, 4, 5]
def baseStart_4181437 : Nat := 118140960795 + 4181437 * 2 ^ 59
def prefixEnd_4181437 : Nat := 4983230072969 + 3 ^ 40 * 4181437 * 2
def baseEnd_4181437 : Nat := 2147087007494261842207427

theorem tailTrace_4181437 : CollatzResearch.WordTrace tailWord_4181437 prefixEnd_4181437 2147087007494261842207427 := by
  unfold tailWord_4181437
  simp only [CollatzResearch.WordTrace]
  refine ⟨152509536552375356429710565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101673024368250237619807043 152509536552375356429710565)
  ·
    refine ⟨28595538103570379330570731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152509536552375356429710565 28595538103570379330570731)
    ·
      refine ⟨42893307155355568995856097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28595538103570379330570731 42893307155355568995856097)
      ·
        refine ⟨32169980366516676746892073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42893307155355568995856097 32169980366516676746892073)
        ·
          refine ⟨24127485274887507560169055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32169980366516676746892073 24127485274887507560169055)
          ·
            refine ⟨36191227912331261340253583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24127485274887507560169055 36191227912331261340253583)
            ·
              refine ⟨54286841868496892010380375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36191227912331261340253583 54286841868496892010380375)
              ·
                refine ⟨81430262802745338015570563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54286841868496892010380375 81430262802745338015570563)
                ·
                  refine ⟨122145394204118007023355845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81430262802745338015570563 122145394204118007023355845)
                  ·
                    refine ⟨22902261413272126316879221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122145394204118007023355845 22902261413272126316879221)
                    ·
                      refine ⟨2147087007494261842207427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22902261413272126316879221 2147087007494261842207427)
                      ·
                        rfl

theorem cell23_4181437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_4181437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181437 prefixEnd_4181437 := by exact prefixLift 4181437
  have htrace : WordTrace (prefixWord ++ tailWord_4181437) baseStart_4181437 baseEnd_4181437 := by
    simpa [prefixWord, tailWord_4181437, baseEnd_4181437] using wordTrace_append hprefix tailTrace_4181437
  have hstable : (prefixWord ++ tailWord_4181437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181437).length < 2 ^ (prefixWord ++ tailWord_4181437).sum := by decide
  have hdescent : baseEnd_4181437 < baseStart_4181437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181451 : List Nat := [1, 1, 1, 1, 3, 3, 4, 3, 1, 3, 2]
def baseStart_4181451 : Nat := 118140960795 + 4181451 * 2 ^ 59
def prefixEnd_4181451 : Nat := 4983230072969 + 3 ^ 40 * 4181451 * 2
def baseEnd_4181451 : Nat := 2147094196223424787432363

theorem tailTrace_4181451 : CollatzResearch.WordTrace tailWord_4181451 prefixEnd_4181451 2147094196223424787432363 := by
  unfold tailWord_4181451
  simp only [CollatzResearch.WordTrace]
  refine ⟨152510047174324636820720207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101673364782883091213813471 152510047174324636820720207)
  ·
    refine ⟨228765070761486955231080311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152510047174324636820720207 228765070761486955231080311)
    ·
      refine ⟨343147606142230432846620467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228765070761486955231080311 343147606142230432846620467)
      ·
        refine ⟨514721409213345649269930701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343147606142230432846620467 514721409213345649269930701)
        ·
          refine ⟨193020528455004618476224013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 514721409213345649269930701 193020528455004618476224013)
          ·
            refine ⟨72382698170626731928584005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193020528455004618476224013 72382698170626731928584005)
            ·
              refine ⟨13571755906992512236609501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72382698170626731928584005 13571755906992512236609501)
              ·
                refine ⟨5089408465122192088728563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13571755906992512236609501 5089408465122192088728563)
                ·
                  refine ⟨7634112697683288133092845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5089408465122192088728563 7634112697683288133092845)
                  ·
                    refine ⟨2862792261631233049909817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7634112697683288133092845 2862792261631233049909817)
                    ·
                      refine ⟨2147094196223424787432363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2862792261631233049909817 2147094196223424787432363)
                      ·
                        rfl

theorem cell23_4181451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 3, 2].length) (baseStart_4181451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181451 prefixEnd_4181451 := by exact prefixLift 4181451
  have htrace : WordTrace (prefixWord ++ tailWord_4181451) baseStart_4181451 baseEnd_4181451 := by
    simpa [prefixWord, tailWord_4181451, baseEnd_4181451] using wordTrace_append hprefix tailTrace_4181451
  have hstable : (prefixWord ++ tailWord_4181451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181451).length < 2 ^ (prefixWord ++ tailWord_4181451).sum := by decide
  have hdescent : baseEnd_4181451 < baseStart_4181451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181467 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 3]
def baseStart_4181467 : Nat := 118140960795 + 4181467 * 2 ^ 59
def prefixEnd_4181467 : Nat := 4983230072969 + 3 ^ 40 * 4181467 * 2
def baseEnd_4181467 : Nat := 2147102411913896724832289

theorem tailTrace_4181467 : CollatzResearch.WordTrace tailWord_4181467 prefixEnd_4181467 2147102411913896724832289 := by
  unfold tailWord_4181467
  simp only [CollatzResearch.WordTrace]
  refine ⟨152510630742266671553302655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101673753828177781035535103 152510630742266671553302655)
  ·
    refine ⟨228765946113400007329953983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152510630742266671553302655 228765946113400007329953983)
    ·
      refine ⟨343148919170100010994930975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228765946113400007329953983 343148919170100010994930975)
      ·
        refine ⟨514723378755150016492396463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343148919170100010994930975 514723378755150016492396463)
        ·
          refine ⟨772085068132725024738594695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514723378755150016492396463 772085068132725024738594695)
          ·
            refine ⟨1158127602199087537107892043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772085068132725024738594695 1158127602199087537107892043)
            ·
              refine ⟨1737191403298631305661838065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158127602199087537107892043 1737191403298631305661838065)
              ·
                refine ⟨1302893552473973479246378549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1737191403298631305661838065 1302893552473973479246378549)
                ·
                  refine ⟨122146270544435013679347989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1302893552473973479246378549 122146270544435013679347989)
                  ·
                    refine ⟨5725606431770391266219437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 122146270544435013679347989 5725606431770391266219437)
                    ·
                      refine ⟨2147102411913896724832289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5725606431770391266219437 2147102411913896724832289)
                      ·
                        rfl

theorem cell23_4181467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 3].length) (baseStart_4181467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181467 prefixEnd_4181467 := by exact prefixLift 4181467
  have htrace : WordTrace (prefixWord ++ tailWord_4181467) baseStart_4181467 baseEnd_4181467 := by
    simpa [prefixWord, tailWord_4181467, baseEnd_4181467] using wordTrace_append hprefix tailTrace_4181467
  have hstable : (prefixWord ++ tailWord_4181467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181467).length < 2 ^ (prefixWord ++ tailWord_4181467).sum := by decide
  have hdescent : baseEnd_4181467 < baseStart_4181467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181475 : List Nat := [1, 1, 1, 6, 2, 3, 2, 1, 2, 1, 3]
def baseStart_4181475 : Nat := 118140960795 + 4181475 * 2 ^ 59
def prefixEnd_4181475 : Nat := 4983230072969 + 3 ^ 40 * 4181475 * 2
def baseEnd_4181475 : Nat := 2147106519759132693532253

theorem tailTrace_4181475 : CollatzResearch.WordTrace tailWord_4181475 prefixEnd_4181475 2147106519759132693532253 := by
  unfold tailWord_4181475
  simp only [CollatzResearch.WordTrace]
  refine ⟨152510922526237688919593879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101673948350825125946395919 152510922526237688919593879)
  ·
    refine ⟨228766383789356533379390819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152510922526237688919593879 228766383789356533379390819)
    ·
      refine ⟨343149575684034800069086229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228766383789356533379390819 343149575684034800069086229)
      ·
        refine ⟨16085136360189131253238417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 343149575684034800069086229 16085136360189131253238417)
        ·
          refine ⟨12063852270141848439928813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16085136360189131253238417 12063852270141848439928813)
          ·
            refine ⟨4523944601303193164973305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12063852270141848439928813 4523944601303193164973305)
            ·
              refine ⟨3392958450977394873729979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4523944601303193164973305 3392958450977394873729979)
              ·
                refine ⟨5089437676466092310594969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3392958450977394873729979 5089437676466092310594969)
                ·
                  refine ⟨3817078257349569232946227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5089437676466092310594969 3817078257349569232946227)
                  ·
                    refine ⟨5725617386024353849419341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3817078257349569232946227 5725617386024353849419341)
                    ·
                      refine ⟨2147106519759132693532253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5725617386024353849419341 2147106519759132693532253)
                      ·
                        rfl

theorem cell23_4181475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_4181475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181475 prefixEnd_4181475 := by exact prefixLift 4181475
  have htrace : WordTrace (prefixWord ++ tailWord_4181475) baseStart_4181475 baseEnd_4181475 := by
    simpa [prefixWord, tailWord_4181475, baseEnd_4181475] using wordTrace_append hprefix tailTrace_4181475
  have hstable : (prefixWord ++ tailWord_4181475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181475).length < 2 ^ (prefixWord ++ tailWord_4181475).sum := by decide
  have hdescent : baseEnd_4181475 < baseStart_4181475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181487 : List Nat := [1, 1, 2, 1, 4, 1, 2, 4, 7]
def baseStart_4181487 : Nat := 118140960795 + 4181487 * 2 ^ 59
def prefixEnd_4181487 : Nat := 4983230072969 + 3 ^ 40 * 4181487 * 2
def baseEnd_4181487 : Nat := 238568075725220738509133

theorem tailTrace_4181487 : CollatzResearch.WordTrace tailWord_4181487 prefixEnd_4181487 238568075725220738509133 := by
  unfold tailWord_4181487
  simp only [CollatzResearch.WordTrace]
  refine ⟨152511360202194214969030715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101674240134796143312687143 152511360202194214969030715)
  ·
    refine ⟨228767040303291322453546073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152511360202194214969030715 228767040303291322453546073)
    ·
      refine ⟨171575280227468491840159555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228767040303291322453546073 171575280227468491840159555)
      ·
        refine ⟨257362920341202737760239333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171575280227468491840159555 257362920341202737760239333)
        ·
          refine ⟨48255547563975513330044875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257362920341202737760239333 48255547563975513330044875)
          ·
            refine ⟨72383321345963269995067313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48255547563975513330044875 72383321345963269995067313)
            ·
              refine ⟨54287491009472452496300485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72383321345963269995067313 54287491009472452496300485)
              ·
                refine ⟨10178904564276084843056341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54287491009472452496300485 10178904564276084843056341)
                ·
                  refine ⟨238568075725220738509133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10178904564276084843056341 238568075725220738509133)
                  ·
                    rfl

theorem cell23_4181487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 7].length) (baseStart_4181487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181487 prefixEnd_4181487 := by exact prefixLift 4181487
  have htrace : WordTrace (prefixWord ++ tailWord_4181487) baseStart_4181487 baseEnd_4181487 := by
    simpa [prefixWord, tailWord_4181487, baseEnd_4181487] using wordTrace_append hprefix tailTrace_4181487
  have hstable : (prefixWord ++ tailWord_4181487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181487).length < 2 ^ (prefixWord ++ tailWord_4181487).sum := by decide
  have hdescent : baseEnd_4181487 < baseStart_4181487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181510 : List Nat := [6, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_4181510 : Nat := 118140960795 + 4181510 * 2 ^ 59
def prefixEnd_4181510 : Nat := 4983230072969 + 3 ^ 40 * 4181510 * 2
def baseEnd_4181510 : Nat := 2147124491582040056594593

theorem tailTrace_4181510 : CollatzResearch.WordTrace tailWord_4181510 prefixEnd_4181510 2147124491582040056594593 := by
  unfold tailWord_4181510
  simp only [CollatzResearch.WordTrace]
  refine ⟨4766006221284715309284937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 101674799387407259931411989 4766006221284715309284937)
  ·
    refine ⟨3574504665963536481963703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4766006221284715309284937 3574504665963536481963703)
    ·
      refine ⟨5361756998945304722945555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3574504665963536481963703 5361756998945304722945555)
      ·
        refine ⟨8042635498417957084418333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5361756998945304722945555 8042635498417957084418333)
        ·
          refine ⟨3015988311906733906656875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8042635498417957084418333 3015988311906733906656875)
          ·
            refine ⟨4523982467860100859985313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3015988311906733906656875 4523982467860100859985313)
            ·
              refine ⟨3392986850895075644988985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4523982467860100859985313 3392986850895075644988985)
              ·
                refine ⟨2544740138171306733741739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3392986850895075644988985 2544740138171306733741739)
                ·
                  refine ⟨3817110207256960100612609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2544740138171306733741739 3817110207256960100612609)
                  ·
                    refine ⟨2862832655442720075459457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3817110207256960100612609 2862832655442720075459457)
                    ·
                      refine ⟨2147124491582040056594593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2862832655442720075459457 2147124491582040056594593)
                      ·
                        rfl

theorem cell23_4181510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_4181510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181510 prefixEnd_4181510 := by exact prefixLift 4181510
  have htrace : WordTrace (prefixWord ++ tailWord_4181510) baseStart_4181510 baseEnd_4181510 := by
    simpa [prefixWord, tailWord_4181510, baseEnd_4181510] using wordTrace_append hprefix tailTrace_4181510
  have hstable : (prefixWord ++ tailWord_4181510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181510).length < 2 ^ (prefixWord ++ tailWord_4181510).sum := by decide
  have hdescent : baseEnd_4181510 < baseStart_4181510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181515 : List Nat := [1, 1, 1, 1, 8, 1, 2, 2, 2, 2, 2]
def baseStart_4181515 : Nat := 118140960795 + 4181515 * 2 ^ 59
def prefixEnd_4181515 : Nat := 4983230072969 + 3 ^ 40 * 4181515 * 2
def baseEnd_4181515 : Nat := 2147127058985312537032069

theorem tailTrace_4181515 : CollatzResearch.WordTrace tailWord_4181515 prefixEnd_4181515 2147127058985312537032069 := by
  unfold tailWord_4181515
  simp only [CollatzResearch.WordTrace]
  refine ⟨152512381446092775751049999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101674920964061850500699999 152512381446092775751049999)
  ·
    refine ⟨228768572169139163626574999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152512381446092775751049999 228768572169139163626574999)
    ·
      refine ⟨343152858253708745439862499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228768572169139163626574999 343152858253708745439862499)
      ·
        refine ⟨514729287380563118159793749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343152858253708745439862499 514729287380563118159793749)
        ·
          refine ⟨6031983836490974040935083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 514729287380563118159793749 6031983836490974040935083)
          ·
            refine ⟨9047975754736461061402625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6031983836490974040935083 9047975754736461061402625)
            ·
              refine ⟨6785981816052345796051969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9047975754736461061402625 6785981816052345796051969)
              ·
                refine ⟨5089486362039259347038977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6785981816052345796051969 5089486362039259347038977)
                ·
                  refine ⟨3817114771529444510279233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5089486362039259347038977 3817114771529444510279233)
                  ·
                    refine ⟨2862836078647083382709425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3817114771529444510279233 2862836078647083382709425)
                    ·
                      refine ⟨2147127058985312537032069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2862836078647083382709425 2147127058985312537032069)
                      ·
                        rfl

theorem cell23_4181515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 2, 2].length) (baseStart_4181515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181515 prefixEnd_4181515 := by exact prefixLift 4181515
  have htrace : WordTrace (prefixWord ++ tailWord_4181515) baseStart_4181515 baseEnd_4181515 := by
    simpa [prefixWord, tailWord_4181515, baseEnd_4181515] using wordTrace_append hprefix tailTrace_4181515
  have hstable : (prefixWord ++ tailWord_4181515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181515).length < 2 ^ (prefixWord ++ tailWord_4181515).sum := by decide
  have hdescent : baseEnd_4181515 < baseStart_4181515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181594 : List Nat := [3, 1, 1, 2, 1, 1, 1, 7, 6]
def baseStart_4181594 : Nat := 118140960795 + 4181594 * 2 ^ 59
def prefixEnd_4181594 : Nat := 4983230072969 + 3 ^ 40 * 4181594 * 2
def baseEnd_4181594 : Nat := 238574180439668636438245

theorem tailTrace_4181594 : CollatzResearch.WordTrace tailWord_4181594 prefixEnd_4181594 238574180439668636438245 := by
  unfold tailWord_4181594
  simp only [CollatzResearch.WordTrace]
  refine ⟨38128815703201643060793959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101676841875204381495450557 38128815703201643060793959)
  ·
    refine ⟨57193223554802464591190939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38128815703201643060793959 57193223554802464591190939)
    ·
      refine ⟨85789835332203696886786409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57193223554802464591190939 85789835332203696886786409)
      ·
        refine ⟨64342376499152772665089807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85789835332203696886786409 64342376499152772665089807)
        ·
          refine ⟨96513564748729158997634711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64342376499152772665089807 96513564748729158997634711)
          ·
            refine ⟨144770347123093738496452067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96513564748729158997634711 144770347123093738496452067)
            ·
              refine ⟨217155520684640607744678101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144770347123093738496452067 217155520684640607744678101)
              ·
                refine ⟨5089582516046264244015893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 217155520684640607744678101 5089582516046264244015893)
                ·
                  refine ⟨238574180439668636438245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5089582516046264244015893 238574180439668636438245)
                  ·
                    rfl

theorem cell23_4181594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 6].length) (baseStart_4181594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181594 prefixEnd_4181594 := by exact prefixLift 4181594
  have htrace : WordTrace (prefixWord ++ tailWord_4181594) baseStart_4181594 baseEnd_4181594 := by
    simpa [prefixWord, tailWord_4181594, baseEnd_4181594] using wordTrace_append hprefix tailTrace_4181594
  have hstable : (prefixWord ++ tailWord_4181594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181594).length < 2 ^ (prefixWord ++ tailWord_4181594).sum := by decide
  have hdescent : baseEnd_4181594 < baseStart_4181594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181665 : List Nat := [1, 2, 3, 3, 2, 2, 2, 1, 2, 3, 2]
def baseStart_4181665 : Nat := 118140960795 + 4181665 * 2 ^ 59
def prefixEnd_4181665 : Nat := 4983230072969 + 3 ^ 40 * 4181665 * 2
def baseEnd_4181665 : Nat := 2147204081083486950156379

theorem tailTrace_4181665 : CollatzResearch.WordTrace tailWord_4181665 prefixEnd_4181665 2147204081083486950156379 := by
  unfold tailWord_4181665
  simp only [CollatzResearch.WordTrace]
  refine ⟨152517852395549351369010449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101678568263699567579340299 152517852395549351369010449)
  ·
    refine ⟨114388389296662013526757837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152517852395549351369010449 114388389296662013526757837)
    ·
      refine ⟨42895645986248255072534189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114388389296662013526757837 42895645986248255072534189)
      ·
        refine ⟨16085867244843095652200321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42895645986248255072534189 16085867244843095652200321)
        ·
          refine ⟨12064400433632321739150241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16085867244843095652200321 12064400433632321739150241)
          ·
            refine ⟨9048300325224241304362681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12064400433632321739150241 9048300325224241304362681)
            ·
              refine ⟨6786225243918180978272011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9048300325224241304362681 6786225243918180978272011)
              ·
                refine ⟨10179337865877271467408017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6786225243918180978272011 10179337865877271467408017)
                ·
                  refine ⟨7634503399407953600556013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10179337865877271467408017 7634503399407953600556013)
                  ·
                    refine ⟨2862938774777982600208505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7634503399407953600556013 2862938774777982600208505)
                    ·
                      refine ⟨2147204081083486950156379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2862938774777982600208505 2147204081083486950156379)
                      ·
                        rfl

theorem cell23_4181665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_4181665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181665 prefixEnd_4181665 := by exact prefixLift 4181665
  have htrace : WordTrace (prefixWord ++ tailWord_4181665) baseStart_4181665 baseEnd_4181665 := by
    simpa [prefixWord, tailWord_4181665, baseEnd_4181665] using wordTrace_append hprefix tailTrace_4181665
  have hstable : (prefixWord ++ tailWord_4181665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181665).length < 2 ^ (prefixWord ++ tailWord_4181665).sum := by decide
  have hdescent : baseEnd_4181665 < baseStart_4181665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181684 : List Nat := [2, 5, 16]
def baseStart_4181684 : Nat := 118140960795 + 4181684 * 2 ^ 59
def prefixEnd_4181684 : Nat := 4983230072969 + 3 ^ 40 * 4181684 * 2
def baseEnd_4181684 : Nat := 327269293890553631431

theorem tailTrace_4181684 : CollatzResearch.WordTrace tailWord_4181684 prefixEnd_4181684 327269293890553631431 := by
  unfold tailWord_4181684
  simp only [CollatzResearch.WordTrace]
  refine ⟨76259272691240258806976053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101679030254987011742634737 76259272691240258806976053)
  ·
    refine ⟨7149306814803774263154005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76259272691240258806976053 7149306814803774263154005)
    ·
      refine ⟨327269293890553631431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 16 7149306814803774263154005 327269293890553631431)
      ·
        rfl

theorem cell23_4181684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 16].length) (baseStart_4181684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181684 prefixEnd_4181684 := by exact prefixLift 4181684
  have htrace : WordTrace (prefixWord ++ tailWord_4181684) baseStart_4181684 baseEnd_4181684 := by
    simpa [prefixWord, tailWord_4181684, baseEnd_4181684] using wordTrace_append hprefix tailTrace_4181684
  have hstable : (prefixWord ++ tailWord_4181684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181684).length < 2 ^ (prefixWord ++ tailWord_4181684).sum := by decide
  have hdescent : baseEnd_4181684 < baseStart_4181684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181729 : List Nat := [1, 2, 3, 1, 5, 1, 2, 3, 1, 2, 2]
def baseStart_4181729 : Nat := 118140960795 + 4181729 * 2 ^ 59
def prefixEnd_4181729 : Nat := 4983230072969 + 3 ^ 40 * 4181729 * 2
def baseEnd_4181729 : Nat := 2147236943845374699756085

theorem tailTrace_4181729 : CollatzResearch.WordTrace tailWord_4181729 prefixEnd_4181729 2147236943845374699756085 := by
  unfold tailWord_4181729
  simp only [CollatzResearch.WordTrace]
  refine ⟨152520186667317490299340241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101680124444878326866226827 152520186667317490299340241)
  ·
    refine ⟨114390140000488117724505181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152520186667317490299340241 114390140000488117724505181)
    ·
      refine ⟨42896302500183044146689443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114390140000488117724505181 42896302500183044146689443)
      ·
        refine ⟨64344453750274566220034165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42896302500183044146689443 64344453750274566220034165)
        ·
          refine ⟨6032292539088240583128203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64344453750274566220034165 6032292539088240583128203)
          ·
            refine ⟨9048438808632360874692305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6032292539088240583128203 9048438808632360874692305)
            ·
              refine ⟨6786329106474270656019229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9048438808632360874692305 6786329106474270656019229)
              ·
                refine ⟨2544873414927851496007211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6786329106474270656019229 2544873414927851496007211)
                ·
                  refine ⟨3817310122391777244010817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2544873414927851496007211 3817310122391777244010817)
                  ·
                    refine ⟨2862982591793832933008113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3817310122391777244010817 2862982591793832933008113)
                    ·
                      refine ⟨2147236943845374699756085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2862982591793832933008113 2147236943845374699756085)
                      ·
                        rfl

theorem cell23_4181729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 1, 2, 2].length) (baseStart_4181729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181729 prefixEnd_4181729 := by exact prefixLift 4181729
  have htrace : WordTrace (prefixWord ++ tailWord_4181729) baseStart_4181729 baseEnd_4181729 := by
    simpa [prefixWord, tailWord_4181729, baseEnd_4181729] using wordTrace_append hprefix tailTrace_4181729
  have hstable : (prefixWord ++ tailWord_4181729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181729).length < 2 ^ (prefixWord ++ tailWord_4181729).sum := by decide
  have hdescent : baseEnd_4181729 < baseStart_4181729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181745 : List Nat := [1, 2, 2, 2, 2, 3, 3, 2, 2, 1, 3]
def baseStart_4181745 : Nat := 118140960795 + 4181745 * 2 ^ 59
def prefixEnd_4181745 : Nat := 4983230072969 + 3 ^ 40 * 4181745 * 2
def baseEnd_4181745 : Nat := 2147245159535846637156011

theorem tailTrace_4181745 : CollatzResearch.WordTrace tailWord_4181745 prefixEnd_4181745 2147245159535846637156011 := by
  unfold tailWord_4181745
  simp only [CollatzResearch.WordTrace]
  refine ⟨152520770235259525031922689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101680513490173016687948459 152520770235259525031922689)
  ·
    refine ⟨114390577676444643773942017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152520770235259525031922689 114390577676444643773942017)
    ·
      refine ⟨85792933257333482830456513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114390577676444643773942017 85792933257333482830456513)
      ·
        refine ⟨64344699943000112122842385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85792933257333482830456513 64344699943000112122842385)
        ·
          refine ⟨48258524957250084092131789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64344699943000112122842385 48258524957250084092131789)
          ·
            refine ⟨18096946858968781534549421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48258524957250084092131789 18096946858968781534549421)
            ·
              refine ⟨6786355072113293075456033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18096946858968781534549421 6786355072113293075456033)
              ·
                refine ⟨5089766304084969806592025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6786355072113293075456033 5089766304084969806592025)
                ·
                  refine ⟨3817324728063727354944019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5089766304084969806592025 3817324728063727354944019)
                  ·
                    refine ⟨5725987092095591032416029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3817324728063727354944019 5725987092095591032416029)
                    ·
                      refine ⟨2147245159535846637156011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5725987092095591032416029 2147245159535846637156011)
                      ·
                        rfl

theorem cell23_4181745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_4181745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181745 prefixEnd_4181745 := by exact prefixLift 4181745
  have htrace : WordTrace (prefixWord ++ tailWord_4181745) baseStart_4181745 baseEnd_4181745 := by
    simpa [prefixWord, tailWord_4181745, baseEnd_4181745] using wordTrace_append hprefix tailTrace_4181745
  have hstable : (prefixWord ++ tailWord_4181745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181745).length < 2 ^ (prefixWord ++ tailWord_4181745).sum := by decide
  have hdescent : baseEnd_4181745 < baseStart_4181745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181761 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 2, 6]
def baseStart_4181761 : Nat := 118140960795 + 4181761 * 2 ^ 59
def prefixEnd_4181761 : Nat := 4983230072969 + 3 ^ 40 * 4181761 * 2
def baseEnd_4181761 : Nat := 715751125075439524851979

theorem tailTrace_4181761 : CollatzResearch.WordTrace tailWord_4181761 prefixEnd_4181761 715751125075439524851979 := by
  unfold tailWord_4181761
  simp only [CollatzResearch.WordTrace]
  refine ⟨152521353803201559764505137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101680902535467706509670091 152521353803201559764505137)
  ·
    refine ⟨114391015352401169823378853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152521353803201559764505137 114391015352401169823378853)
    ·
      refine ⟨21448315378575219341883535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114391015352401169823378853 21448315378575219341883535)
      ·
        refine ⟨32172473067862829012825303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21448315378575219341883535 32172473067862829012825303)
        ·
          refine ⟨48258709601794243519237955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32172473067862829012825303 48258709601794243519237955)
          ·
            refine ⟨72388064402691365278856933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48258709601794243519237955 72388064402691365278856933)
            ·
              refine ⟨13572762075504630989785675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72388064402691365278856933 13572762075504630989785675)
              ·
                refine ⟨20359143113256946484678513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13572762075504630989785675 20359143113256946484678513)
                ·
                  refine ⟨15269357334942709863508885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20359143113256946484678513 15269357334942709863508885)
                  ·
                    refine ⟨715751125075439524851979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15269357334942709863508885 715751125075439524851979)
                    ·
                      rfl

theorem cell23_4181761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_4181761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181761 prefixEnd_4181761 := by exact prefixLift 4181761
  have htrace : WordTrace (prefixWord ++ tailWord_4181761) baseStart_4181761 baseEnd_4181761 := by
    simpa [prefixWord, tailWord_4181761, baseEnd_4181761] using wordTrace_append hprefix tailTrace_4181761
  have hstable : (prefixWord ++ tailWord_4181761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181761).length < 2 ^ (prefixWord ++ tailWord_4181761).sum := by decide
  have hdescent : baseEnd_4181761 < baseStart_4181761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181771 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 3]
def baseStart_4181771 : Nat := 118140960795 + 4181771 * 2 ^ 59
def prefixEnd_4181771 : Nat := 4983230072969 + 3 ^ 40 * 4181771 * 2
def baseEnd_4181771 : Nat := 2147258510032863535430891

theorem tailTrace_4181771 : CollatzResearch.WordTrace tailWord_4181771 prefixEnd_4181771 2147258510032863535430891 := by
  unfold tailWord_4181771
  simp only [CollatzResearch.WordTrace]
  refine ⟨152521718533165331472369167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101681145688776887648246111 152521718533165331472369167)
  ·
    refine ⟨228782577799747997208553751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152521718533165331472369167 228782577799747997208553751)
    ·
      refine ⟨343173866699621995812830627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228782577799747997208553751 343173866699621995812830627)
      ·
        refine ⟨514760800049432993719245941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343173866699621995812830627 514760800049432993719245941)
        ·
          refine ⟨48258825004634343161179307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 514760800049432993719245941 48258825004634343161179307)
          ·
            refine ⟨72388237506951514741768961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48258825004634343161179307 72388237506951514741768961)
            ·
              refine ⟨54291178130213636056326721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72388237506951514741768961 54291178130213636056326721)
              ·
                refine ⟨40718383597660227042245041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54291178130213636056326721 40718383597660227042245041)
                ·
                  refine ⟨30538787698245170281683781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40718383597660227042245041 30538787698245170281683781)
                  ·
                    refine ⟨5726022693420969427815709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30538787698245170281683781 5726022693420969427815709)
                    ·
                      refine ⟨2147258510032863535430891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5726022693420969427815709 2147258510032863535430891)
                      ·
                        rfl

theorem cell23_4181771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 3].length) (baseStart_4181771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181771 prefixEnd_4181771 := by exact prefixLift 4181771
  have htrace : WordTrace (prefixWord ++ tailWord_4181771) baseStart_4181771 baseEnd_4181771 := by
    simpa [prefixWord, tailWord_4181771, baseEnd_4181771] using wordTrace_append hprefix tailTrace_4181771
  have hstable : (prefixWord ++ tailWord_4181771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181771).length < 2 ^ (prefixWord ++ tailWord_4181771).sum := by decide
  have hdescent : baseEnd_4181771 < baseStart_4181771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181780 : List Nat := [2, 4, 4, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_4181780 : Nat := 118140960795 + 4181780 * 2 ^ 59
def prefixEnd_4181780 : Nat := 4983230072969 + 3 ^ 40 * 4181780 * 2
def baseEnd_4181780 : Nat := 2147263131358754000218351

theorem tailTrace_4181780 : CollatzResearch.WordTrace tailWord_4181780 prefixEnd_4181780 2147263131358754000218351 := by
  unfold tailWord_4181780
  simp only [CollatzResearch.WordTrace]
  refine ⟨76261023395066363004723397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101681364526755150672964529 76261023395066363004723397)
  ·
    refine ⟨14298941886574943063385637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76261023395066363004723397 14298941886574943063385637)
    ·
      refine ⟨2681051603732801824384807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14298941886574943063385637 2681051603732801824384807)
      ·
        refine ⟨4021577405599202736577211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2681051603732801824384807 4021577405599202736577211)
        ·
          refine ⟨6032366108398804104865817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4021577405599202736577211 6032366108398804104865817)
          ·
            refine ⟨4524274581299103078649363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6032366108398804104865817 4524274581299103078649363)
            ·
              refine ⟨6786411871948654617974045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4524274581299103078649363 6786411871948654617974045)
              ·
                refine ⟨2544904451980745481740267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6786411871948654617974045 2544904451980745481740267)
                ·
                  refine ⟨3817356677971118222610401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2544904451980745481740267 3817356677971118222610401)
                  ·
                    refine ⟨2863017508478338666957801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3817356677971118222610401 2863017508478338666957801)
                    ·
                      refine ⟨2147263131358754000218351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2863017508478338666957801 2147263131358754000218351)
                      ·
                        rfl

theorem cell23_4181780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_4181780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181780 prefixEnd_4181780 := by exact prefixLift 4181780
  have htrace : WordTrace (prefixWord ++ tailWord_4181780) baseStart_4181780 baseEnd_4181780 := by
    simpa [prefixWord, tailWord_4181780, baseEnd_4181780] using wordTrace_append hprefix tailTrace_4181780
  have hstable : (prefixWord ++ tailWord_4181780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181780).length < 2 ^ (prefixWord ++ tailWord_4181780).sum := by decide
  have hdescent : baseEnd_4181780 < baseStart_4181780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181859 : List Nat := [1, 1, 1, 5, 5, 1, 2, 2, 5]
def baseStart_4181859 : Nat := 118140960795 + 4181859 * 2 ^ 59
def prefixEnd_4181859 : Nat := 4983230072969 + 3 ^ 40 * 4181859 * 2
def baseEnd_4181859 : Nat := 238589299592273243458943

theorem tailTrace_4181859 : CollatzResearch.WordTrace tailWord_4181859 prefixEnd_4181859 238589299592273243458943 := by
  unfold tailWord_4181859
  simp only [CollatzResearch.WordTrace]
  refine ⟨152524928156846522501572631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101683285437897681667715087 152524928156846522501572631)
  ·
    refine ⟨228787392235269783752358947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152524928156846522501572631 228787392235269783752358947)
    ·
      refine ⟨343181088352904675628538421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228787392235269783752358947 343181088352904675628538421)
      ·
        refine ⟨32173227033084813340175477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 343181088352904675628538421 32173227033084813340175477)
        ·
          refine ⟨3016240034351701250641451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32173227033084813340175477 3016240034351701250641451)
          ·
            refine ⟨4524360051527551875962177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3016240034351701250641451 4524360051527551875962177)
            ·
              refine ⟨3393270038645663906971633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4524360051527551875962177 3393270038645663906971633)
              ·
                refine ⟨2544952528984247930228725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3393270038645663906971633 2544952528984247930228725)
                ·
                  refine ⟨238589299592273243458943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2544952528984247930228725 238589299592273243458943)
                  ·
                    rfl

theorem cell23_4181859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 5].length) (baseStart_4181859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181859 prefixEnd_4181859 := by exact prefixLift 4181859
  have htrace : WordTrace (prefixWord ++ tailWord_4181859) baseStart_4181859 baseEnd_4181859 := by
    simpa [prefixWord, tailWord_4181859, baseEnd_4181859] using wordTrace_append hprefix tailTrace_4181859
  have hstable : (prefixWord ++ tailWord_4181859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181859).length < 2 ^ (prefixWord ++ tailWord_4181859).sum := by decide
  have hdescent : baseEnd_4181859 < baseStart_4181859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181861 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 1, 5, 5]
def baseStart_4181861 : Nat := 118140960795 + 4181861 * 2 ^ 59
def prefixEnd_4181861 : Nat := 4983230072969 + 3 ^ 40 * 4181861 * 2
def baseEnd_4181861 : Nat := 2147304723291768183305477

theorem tailTrace_4181861 : CollatzResearch.WordTrace tailWord_4181861 prefixEnd_4181861 2147304723291768183305477 := by
  unfold tailWord_4181861
  simp only [CollatzResearch.WordTrace]
  refine ⟨152525001102839276843145437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101683334068559517895430291 152525001102839276843145437)
  ·
    refine ⟨57196875413564728816179539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152525001102839276843145437 57196875413564728816179539)
    ·
      refine ⟨85795313120347093224269309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57196875413564728816179539 85795313120347093224269309)
      ·
        refine ⟨32173242420130159959100991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85795313120347093224269309 32173242420130159959100991)
        ·
          refine ⟨48259863630195239938651487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32173242420130159959100991 48259863630195239938651487)
          ·
            refine ⟨72389795445292859907977231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48259863630195239938651487 72389795445292859907977231)
            ·
              refine ⟨108584693167939289861965847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72389795445292859907977231 108584693167939289861965847)
              ·
                refine ⟨162877039751908934792948771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108584693167939289861965847 162877039751908934792948771)
                ·
                  refine ⟨244315559627863402189423157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162877039751908934792948771 244315559627863402189423157)
                  ·
                    refine ⟨22904583715112193955258421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 244315559627863402189423157 22904583715112193955258421)
                    ·
                      refine ⟨2147304723291768183305477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22904583715112193955258421 2147304723291768183305477)
                      ·
                        rfl

theorem cell23_4181861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_4181861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181861 prefixEnd_4181861 := by exact prefixLift 4181861
  have htrace : WordTrace (prefixWord ++ tailWord_4181861) baseStart_4181861 baseEnd_4181861 := by
    simpa [prefixWord, tailWord_4181861, baseEnd_4181861] using wordTrace_append hprefix tailTrace_4181861
  have hstable : (prefixWord ++ tailWord_4181861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181861).length < 2 ^ (prefixWord ++ tailWord_4181861).sum := by decide
  have hdescent : baseEnd_4181861 < baseStart_4181861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181871 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 4]
def baseStart_4181871 : Nat := 118140960795 + 4181871 * 2 ^ 59
def prefixEnd_4181871 : Nat := 4983230072969 + 3 ^ 40 * 4181871 * 2
def baseEnd_4181871 : Nat := 2147309858098313144180431

theorem tailTrace_4181871 : CollatzResearch.WordTrace tailWord_4181871 prefixEnd_4181871 2147309858098313144180431 := by
  unfold tailWord_4181871
  simp only [CollatzResearch.WordTrace]
  refine ⟨152525365832803048551009467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101683577221868699034006311 152525365832803048551009467)
  ·
    refine ⟨228788048749204572826514201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152525365832803048551009467 228788048749204572826514201)
    ·
      refine ⟨171591036561903429619885651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228788048749204572826514201 171591036561903429619885651)
      ·
        refine ⟨257386554842855144429828477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171591036561903429619885651 257386554842855144429828477)
        ·
          refine ⟨96519958066070679161185679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257386554842855144429828477 96519958066070679161185679)
          ·
            refine ⟨144779937099106018741778519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96519958066070679161185679 144779937099106018741778519)
            ·
              refine ⟨217169905648659028112667779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144779937099106018741778519 217169905648659028112667779)
              ·
                refine ⟨325754858472988542169001669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217169905648659028112667779 325754858472988542169001669)
                ·
                  refine ⟨61079035963685351656687813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 325754858472988542169001669 61079035963685351656687813)
                  ·
                    refine ⟨11452319243191003435628965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61079035963685351656687813 11452319243191003435628965)
                    ·
                      refine ⟨2147309858098313144180431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11452319243191003435628965 2147309858098313144180431)
                      ·
                        rfl

theorem cell23_4181871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 4].length) (baseStart_4181871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181871 prefixEnd_4181871 := by exact prefixLift 4181871
  have htrace : WordTrace (prefixWord ++ tailWord_4181871) baseStart_4181871 baseEnd_4181871 := by
    simpa [prefixWord, tailWord_4181871, baseEnd_4181871] using wordTrace_append hprefix tailTrace_4181871
  have hstable : (prefixWord ++ tailWord_4181871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181871).length < 2 ^ (prefixWord ++ tailWord_4181871).sum := by decide
  have hdescent : baseEnd_4181871 < baseStart_4181871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181889 : List Nat := [1, 2, 4, 4, 2, 1, 1, 1, 2, 5]
def baseStart_4181889 : Nat := 118140960795 + 4181889 * 2 ^ 59
def prefixEnd_4181889 : Nat := 4983230072969 + 3 ^ 40 * 4181889 * 2
def baseEnd_4181889 : Nat := 715773033583364691251783

theorem tailTrace_4181889 : CollatzResearch.WordTrace tailWord_4181889 prefixEnd_4181889 715773033583364691251783 := by
  unfold tailWord_4181889
  simp only [CollatzResearch.WordTrace]
  refine ⟨152526022346737837625164721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101684014897825225083443147 152526022346737837625164721)
  ·
    refine ⟨114394516760053378218873541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152526022346737837625164721 114394516760053378218873541)
    ·
      refine ⟨21448971892510008416038789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114394516760053378218873541 21448971892510008416038789)
      ·
        refine ⟨4021682229845626578007273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21448971892510008416038789 4021682229845626578007273)
        ·
          refine ⟨3016261672384219933505455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4021682229845626578007273 3016261672384219933505455)
          ·
            refine ⟨4524392508576329900258183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3016261672384219933505455 4524392508576329900258183)
            ·
              refine ⟨6786588762864494850387275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4524392508576329900258183 6786588762864494850387275)
              ·
                refine ⟨10179883144296742275580913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6786588762864494850387275 10179883144296742275580913)
                ·
                  refine ⟨7634912358222556706685685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10179883144296742275580913 7634912358222556706685685)
                  ·
                    refine ⟨715773033583364691251783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7634912358222556706685685 715773033583364691251783)
                    ·
                      rfl

theorem cell23_4181889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_4181889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181889 prefixEnd_4181889 := by exact prefixLift 4181889
  have htrace : WordTrace (prefixWord ++ tailWord_4181889) baseStart_4181889 baseEnd_4181889 := by
    simpa [prefixWord, tailWord_4181889, baseEnd_4181889] using wordTrace_append hprefix tailTrace_4181889
  have hstable : (prefixWord ++ tailWord_4181889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181889).length < 2 ^ (prefixWord ++ tailWord_4181889).sum := by decide
  have hdescent : baseEnd_4181889 < baseStart_4181889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181895 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 3]
def baseStart_4181895 : Nat := 118140960795 + 4181895 * 2 ^ 59
def prefixEnd_4181895 : Nat := 4983230072969 + 3 ^ 40 * 4181895 * 2
def baseEnd_4181895 : Nat := 2147322181634021050280321

theorem tailTrace_4181895 : CollatzResearch.WordTrace tailWord_4181895 prefixEnd_4181895 2147322181634021050280321 := by
  unfold tailWord_4181895
  simp only [CollatzResearch.WordTrace]
  refine ⟨152526241184716100649883139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101684160789810733766588759 152526241184716100649883139)
  ·
    refine ⟨228789361777074150974824709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152526241184716100649883139 228789361777074150974824709)
    ·
      refine ⟨42898005333201403307779633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228789361777074150974824709 42898005333201403307779633)
      ·
        refine ⟨32173503999901052480834725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42898005333201403307779633 32173503999901052480834725)
        ·
          refine ⟨6032531999981447340156511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32173503999901052480834725 6032531999981447340156511)
          ·
            refine ⟨9048797999972171010234767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6032531999981447340156511 9048797999972171010234767)
            ·
              refine ⟨13573196999958256515352151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9048797999972171010234767 13573196999958256515352151)
              ·
                refine ⟨20359795499937384773028227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13573196999958256515352151 20359795499937384773028227)
                ·
                  refine ⟨30539693249906077159542341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20359795499937384773028227 30539693249906077159542341)
                  ·
                    refine ⟨5726192484357389467414189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30539693249906077159542341 5726192484357389467414189)
                    ·
                      refine ⟨2147322181634021050280321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5726192484357389467414189 2147322181634021050280321)
                      ·
                        rfl

theorem cell23_4181895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_4181895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181895 prefixEnd_4181895 := by exact prefixLift 4181895
  have htrace : WordTrace (prefixWord ++ tailWord_4181895) baseStart_4181895 baseEnd_4181895 := by
    simpa [prefixWord, tailWord_4181895, baseEnd_4181895] using wordTrace_append hprefix tailTrace_4181895
  have hstable : (prefixWord ++ tailWord_4181895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181895).length < 2 ^ (prefixWord ++ tailWord_4181895).sum := by decide
  have hdescent : baseEnd_4181895 < baseStart_4181895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181945 : List Nat := [1, 2, 1, 4, 2, 1, 4, 2, 1, 5]
def baseStart_4181945 : Nat := 118140960795 + 4181945 * 2 ^ 59
def prefixEnd_4181945 : Nat := 4983230072969 + 3 ^ 40 * 4181945 * 2
def baseEnd_4181945 : Nat := 715782618555581951551697

theorem tailTrace_4181945 : CollatzResearch.WordTrace tailWord_4181945 prefixEnd_4181945 715782618555581951551697 := by
  unfold tailWord_4181945
  simp only [CollatzResearch.WordTrace]
  refine ⟨152528064834534959189203289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101685376556356639459468859 152528064834534959189203289)
  ·
    refine ⟨114396048625901219391902467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152528064834534959189203289 114396048625901219391902467)
    ·
      refine ⟨171594072938851829087853701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114396048625901219391902467 171594072938851829087853701)
      ·
        refine ⟨32173888676034717953972569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171594072938851829087853701 32173888676034717953972569)
        ·
          refine ⟨24130416507026038465479427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32173888676034717953972569 24130416507026038465479427)
          ·
            refine ⟨36195624760539057698219141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24130416507026038465479427 36195624760539057698219141)
            ·
              refine ⟨6786679642601073318416089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36195624760539057698219141 6786679642601073318416089)
              ·
                refine ⟨5090009731950804988812067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6786679642601073318416089 5090009731950804988812067)
                ·
                  refine ⟨7635014597926207483218101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5090009731950804988812067 7635014597926207483218101)
                  ·
                    refine ⟨715782618555581951551697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7635014597926207483218101 715782618555581951551697)
                    ·
                      rfl

theorem cell23_4181945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 5].length) (baseStart_4181945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181945 prefixEnd_4181945 := by exact prefixLift 4181945
  have htrace : WordTrace (prefixWord ++ tailWord_4181945) baseStart_4181945 baseEnd_4181945 := by
    simpa [prefixWord, tailWord_4181945, baseEnd_4181945] using wordTrace_append hprefix tailTrace_4181945
  have hstable : (prefixWord ++ tailWord_4181945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181945).length < 2 ^ (prefixWord ++ tailWord_4181945).sum := by decide
  have hdescent : baseEnd_4181945 < baseStart_4181945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181968 : List Nat := [2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 5]
def baseStart_4181968 : Nat := 118140960795 + 4181968 * 2 ^ 59
def prefixEnd_4181968 : Nat := 4983230072969 + 3 ^ 40 * 4181968 * 2
def baseEnd_4181968 : Nat := 2147359665721799264667485

theorem tailTrace_4181968 : CollatzResearch.WordTrace tailWord_4181968 prefixEnd_4181968 2147359665721799264667485 := by
  unfold tailWord_4181968
  simp only [CollatzResearch.WordTrace]
  refine ⟨76264451856725817058645279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101685935808967756078193705 76264451856725817058645279)
  ·
    refine ⟨114396677785088725587967919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76264451856725817058645279 114396677785088725587967919)
    ·
      refine ⟨171595016677633088381951879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114396677785088725587967919 171595016677633088381951879)
      ·
        refine ⟨257392525016449632572927819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171595016677633088381951879 257392525016449632572927819)
        ·
          refine ⟨386088787524674448859391729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257392525016449632572927819 386088787524674448859391729)
          ·
            refine ⟨289566590643505836644543797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386088787524674448859391729 289566590643505836644543797)
            ·
              refine ⟨27146867872828672185425981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 289566590643505836644543797 27146867872828672185425981)
              ·
                refine ⟨10180075452310752069534743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27146867872828672185425981 10180075452310752069534743)
                ·
                  refine ⟨15270113178466128104302115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10180075452310752069534743 15270113178466128104302115)
                  ·
                    refine ⟨22905169767699192156453173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15270113178466128104302115 22905169767699192156453173)
                    ·
                      refine ⟨2147359665721799264667485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22905169767699192156453173 2147359665721799264667485)
                      ·
                        rfl

theorem cell23_4181968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 5].length) (baseStart_4181968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181968 prefixEnd_4181968 := by exact prefixLift 4181968
  have htrace : WordTrace (prefixWord ++ tailWord_4181968) baseStart_4181968 baseEnd_4181968 := by
    simpa [prefixWord, tailWord_4181968, baseEnd_4181968] using wordTrace_append hprefix tailTrace_4181968
  have hstable : (prefixWord ++ tailWord_4181968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181968).length < 2 ^ (prefixWord ++ tailWord_4181968).sum := by decide
  have hdescent : baseEnd_4181968 < baseStart_4181968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181975 : List Nat := [1, 1, 3, 2, 1, 1, 4, 4, 2, 4]
def baseStart_4181975 : Nat := 118140960795 + 4181975 * 2 ^ 59
def prefixEnd_4181975 : Nat := 4983230072969 + 3 ^ 40 * 4181975 * 2
def baseEnd_4181975 : Nat := 715787753362126912426651

theorem tailTrace_4181975 : CollatzResearch.WordTrace tailWord_4181975 prefixEnd_4181975 715787753362126912426651 := by
  unfold tailWord_4181975
  simp only [CollatzResearch.WordTrace]
  refine ⟨152529159024426274312795379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101686106016284182875196919 152529159024426274312795379)
  ·
    refine ⟨228793738536639411469193069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152529159024426274312795379 228793738536639411469193069)
    ·
      refine ⟨85797651951239779300947401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228793738536639411469193069 85797651951239779300947401)
      ·
        refine ⟨64348238963429834475710551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85797651951239779300947401 64348238963429834475710551)
        ·
          refine ⟨96522358445144751713565827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64348238963429834475710551 96522358445144751713565827)
          ·
            refine ⟨144783537667717127570348741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96522358445144751713565827 144783537667717127570348741)
            ·
              refine ⟨27146913312696961419440389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144783537667717127570348741 27146913312696961419440389)
              ·
                refine ⟨5090046246130680266145073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27146913312696961419440389 5090046246130680266145073)
                ·
                  refine ⟨3817534684598010199608805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5090046246130680266145073 3817534684598010199608805)
                  ·
                    refine ⟨715787753362126912426651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3817534684598010199608805 715787753362126912426651)
                    ·
                      rfl

theorem cell23_4181975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 4].length) (baseStart_4181975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181975 prefixEnd_4181975 := by exact prefixLift 4181975
  have htrace : WordTrace (prefixWord ++ tailWord_4181975) baseStart_4181975 baseEnd_4181975 := by
    simpa [prefixWord, tailWord_4181975, baseEnd_4181975] using wordTrace_append hprefix tailTrace_4181975
  have hstable : (prefixWord ++ tailWord_4181975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181975).length < 2 ^ (prefixWord ++ tailWord_4181975).sum := by decide
  have hdescent : baseEnd_4181975 < baseStart_4181975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181988 : List Nat := [2, 3, 1, 1, 1, 1, 6, 8]
def baseStart_4181988 : Nat := 118140960795 + 4181988 * 2 ^ 59
def prefixEnd_4181988 : Nat := 4983230072969 + 3 ^ 40 * 4181988 * 2
def baseEnd_4181988 : Nat := 79532219827218118015459

theorem tailTrace_4181988 : CollatzResearch.WordTrace tailWord_4181988 prefixEnd_4181988 79532219827218118015459 := by
  unfold tailWord_4181988
  simp only [CollatzResearch.WordTrace]
  refine ⟨76264816586689588766509309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101686422115586118355345745 76264816586689588766509309)
  ·
    refine ⟨28599306220008595787440991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76264816586689588766509309 28599306220008595787440991)
    ·
      refine ⟨42898959330012893681161487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28599306220008595787440991 42898959330012893681161487)
      ·
        refine ⟨64348438995019340521742231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42898959330012893681161487 64348438995019340521742231)
        ·
          refine ⟨96522658492529010782613347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64348438995019340521742231 96522658492529010782613347)
          ·
            refine ⟨144783987738793516173920021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96522658492529010782613347 144783987738793516173920021)
            ·
              refine ⟨6786749425255946070652501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144783987738793516173920021 6786749425255946070652501)
              ·
                refine ⟨79532219827218118015459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6786749425255946070652501 79532219827218118015459)
                ·
                  rfl

theorem cell23_4181988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 8].length) (baseStart_4181988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4181988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4181988 prefixEnd_4181988 := by exact prefixLift 4181988
  have htrace : WordTrace (prefixWord ++ tailWord_4181988) baseStart_4181988 baseEnd_4181988 := by
    simpa [prefixWord, tailWord_4181988, baseEnd_4181988] using wordTrace_append hprefix tailTrace_4181988
  have hstable : (prefixWord ++ tailWord_4181988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181988).length < 2 ^ (prefixWord ++ tailWord_4181988).sum := by decide
  have hdescent : baseEnd_4181988 < baseStart_4181988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182015 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 6, 1, 3]
def baseStart_4182015 : Nat := 118140960795 + 4182015 * 2 ^ 59
def prefixEnd_4182015 : Nat := 4983230072969 + 3 ^ 40 * 4182015 * 2
def baseEnd_4182015 : Nat := 2147383799312560580779769

theorem tailTrace_4182015 : CollatzResearch.WordTrace tailWord_4182015 prefixEnd_4182015 2147383799312560580779769 := by
  unfold tailWord_4182015
  simp only [CollatzResearch.WordTrace]
  refine ⟨152530617944281361144251499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101687078629520907429500999 152530617944281361144251499)
  ·
    refine ⟨228795926916422041716377249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152530617944281361144251499 228795926916422041716377249)
    ·
      refine ⟨171596945187316531287282937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228795926916422041716377249 171596945187316531287282937)
      ·
        refine ⟨128697708890487398465462203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171596945187316531287282937 128697708890487398465462203)
        ·
          refine ⟨193046563335731097698193305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128697708890487398465462203 193046563335731097698193305)
          ·
            refine ⟨144784922501798323273644979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193046563335731097698193305 144784922501798323273644979)
            ·
              refine ⟨217177383752697484910467469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144784922501798323273644979 217177383752697484910467469)
              ·
                refine ⟨81441518907261556841425301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217177383752697484910467469 81441518907261556841425301)
                ·
                  refine ⟨3817571198777885476941811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81441518907261556841425301 3817571198777885476941811)
                  ·
                    refine ⟨5726356798166828215412717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3817571198777885476941811 5726356798166828215412717)
                    ·
                      refine ⟨2147383799312560580779769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5726356798166828215412717 2147383799312560580779769)
                      ·
                        rfl

theorem cell23_4182015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 1, 3].length) (baseStart_4182015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182015 prefixEnd_4182015 := by exact prefixLift 4182015
  have htrace : WordTrace (prefixWord ++ tailWord_4182015) baseStart_4182015 baseEnd_4182015 := by
    simpa [prefixWord, tailWord_4182015, baseEnd_4182015] using wordTrace_append hprefix tailTrace_4182015
  have hstable : (prefixWord ++ tailWord_4182015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182015).length < 2 ^ (prefixWord ++ tailWord_4182015).sum := by decide
  have hdescent : baseEnd_4182015 < baseStart_4182015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182042 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2]
def baseStart_4182042 : Nat := 118140960795 + 4182042 * 2 ^ 59
def prefixEnd_4182042 : Nat := 4983230072969 + 3 ^ 40 * 4182042 * 2
def baseEnd_4182042 : Nat := 2147397663290231975142145

theorem tailTrace_4182042 : CollatzResearch.WordTrace tailWord_4182042 prefixEnd_4182042 2147397663290231975142145 := by
  unfold tailWord_4182042
  simp only [CollatzResearch.WordTrace]
  refine ⟨38132900678795886188871095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101687735143455696503656253 38132900678795886188871095)
  ·
    refine ⟨57199351018193829283306643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38132900678795886188871095 57199351018193829283306643)
    ·
      refine ⟨85799026527290743924959965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57199351018193829283306643 85799026527290743924959965)
      ·
        refine ⟨32174634947734028971859987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85799026527290743924959965 32174634947734028971859987)
        ·
          refine ⟨48261952421601043457789981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32174634947734028971859987 48261952421601043457789981)
          ·
            refine ⟨18098232158100391296671243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48261952421601043457789981 18098232158100391296671243)
            ·
              refine ⟨27147348237150586945006865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18098232158100391296671243 27147348237150586945006865)
              ·
                refine ⟨20360511177862940208755149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27147348237150586945006865 20360511177862940208755149)
                ·
                  refine ⟨7635191691698602578283181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20360511177862940208755149 7635191691698602578283181)
                  ·
                    refine ⟨2863196884386975966856193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7635191691698602578283181 2863196884386975966856193)
                    ·
                      refine ⟨2147397663290231975142145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2863196884386975966856193 2147397663290231975142145)
                      ·
                        rfl

theorem cell23_4182042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_4182042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182042 prefixEnd_4182042 := by exact prefixLift 4182042
  have htrace : WordTrace (prefixWord ++ tailWord_4182042) baseStart_4182042 baseEnd_4182042 := by
    simpa [prefixWord, tailWord_4182042, baseEnd_4182042] using wordTrace_append hprefix tailTrace_4182042
  have hstable : (prefixWord ++ tailWord_4182042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182042).length < 2 ^ (prefixWord ++ tailWord_4182042).sum := by decide
  have hdescent : baseEnd_4182042 < baseStart_4182042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182088 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 1, 1, 9]
def baseStart_4182088 : Nat := 118140960795 + 4182088 * 2 ^ 59
def prefixEnd_4182088 : Nat := 4983230072969 + 3 ^ 40 * 4182088 * 2
def baseEnd_4182088 : Nat := 2147421283400338795166933

theorem tailTrace_4182088 : CollatzResearch.WordTrace tailWord_4182088 prefixEnd_4182088 2147421283400338795166933 := by
  unfold tailWord_4182088
  simp only [CollatzResearch.WordTrace]
  refine ⟨76266640236508447305829459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101688853648677929741105945 76266640236508447305829459)
  ·
    refine ⟨114399960354762670958744189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76266640236508447305829459 114399960354762670958744189)
    ·
      refine ⟨42899985133036001609529071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114399960354762670958744189 42899985133036001609529071)
      ·
        refine ⟨64349977699554002414293607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42899985133036001609529071 64349977699554002414293607)
        ·
          refine ⟨96524966549331003621440411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64349977699554002414293607 96524966549331003621440411)
          ·
            refine ⟨144787449823996505432160617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96524966549331003621440411 144787449823996505432160617)
            ·
              refine ⟨108590587367997379074120463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144787449823996505432160617 108590587367997379074120463)
              ·
                refine ⟨162885881051996068611180695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108590587367997379074120463 162885881051996068611180695)
                ·
                  refine ⟨244328821577994102916771043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162885881051996068611180695 244328821577994102916771043)
                  ·
                    refine ⟨366493232366991154375156565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 244328821577994102916771043 366493232366991154375156565)
                    ·
                      refine ⟨2147421283400338795166933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 366493232366991154375156565 2147421283400338795166933)
                      ·
                        rfl

theorem cell23_4182088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_4182088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182088 prefixEnd_4182088 := by exact prefixLift 4182088
  have htrace : WordTrace (prefixWord ++ tailWord_4182088) baseStart_4182088 baseEnd_4182088 := by
    simpa [prefixWord, tailWord_4182088, baseEnd_4182088] using wordTrace_append hprefix tailTrace_4182088
  have hstable : (prefixWord ++ tailWord_4182088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182088).length < 2 ^ (prefixWord ++ tailWord_4182088).sum := by decide
  have hdescent : baseEnd_4182088 < baseStart_4182088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182105 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 2, 3, 3]
def baseStart_4182105 : Nat := 118140960795 + 4182105 * 2 ^ 59
def prefixEnd_4182105 : Nat := 4983230072969 + 3 ^ 40 * 4182105 * 2
def baseEnd_4182105 : Nat := 2147430012571465228654355

theorem tailTrace_4182105 : CollatzResearch.WordTrace tailWord_4182105 prefixEnd_4182105 2147430012571465228654355 := by
  unfold tailWord_4182105
  simp only [CollatzResearch.WordTrace]
  refine ⟨152533900513955306515027769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101689267009303537676685179 152533900513955306515027769)
  ·
    refine ⟨114400425385466479886270827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152533900513955306515027769 114400425385466479886270827)
    ·
      refine ⟨171600638078199719829406241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114400425385466479886270827 171600638078199719829406241)
      ·
        refine ⟨128700478558649789872054681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171600638078199719829406241 128700478558649789872054681)
        ·
          refine ⟨96525358918987342404041011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128700478558649789872054681 96525358918987342404041011)
          ·
            refine ⟨144788038378481013606061517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96525358918987342404041011 144788038378481013606061517)
            ·
              refine ⟨54295514391930380102273069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144788038378481013606061517 54295514391930380102273069)
              ·
                refine ⟨20360817896973892538352401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54295514391930380102273069 20360817896973892538352401)
                ·
                  refine ⟨15270613422730419403764301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20360817896973892538352401 15270613422730419403764301)
                  ·
                    refine ⟨5726480033523907276411613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15270613422730419403764301 5726480033523907276411613)
                    ·
                      refine ⟨2147430012571465228654355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5726480033523907276411613 2147430012571465228654355)
                      ·
                        rfl

theorem cell23_4182105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 3, 3].length) (baseStart_4182105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182105 prefixEnd_4182105 := by exact prefixLift 4182105
  have htrace : WordTrace (prefixWord ++ tailWord_4182105) baseStart_4182105 baseEnd_4182105 := by
    simpa [prefixWord, tailWord_4182105, baseEnd_4182105] using wordTrace_append hprefix tailTrace_4182105
  have hstable : (prefixWord ++ tailWord_4182105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182105).length < 2 ^ (prefixWord ++ tailWord_4182105).sum := by decide
  have hdescent : baseEnd_4182105 < baseStart_4182105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182106 : List Nat := [3, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2]
def baseStart_4182106 : Nat := 118140960795 + 4182106 * 2 ^ 59
def prefixEnd_4182106 : Nat := 4983230072969 + 3 ^ 40 * 4182106 * 2
def baseEnd_4182106 : Nat := 2147430526052119724741851

theorem tailTrace_4182106 : CollatzResearch.WordTrace tailWord_4182106 prefixEnd_4182106 2147430526052119724741851 := by
  unfold tailWord_4182106
  simp only [CollatzResearch.WordTrace]
  refine ⟨38133484246737920921453543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101689291324634455790542781 38133484246737920921453543)
  ·
    refine ⟨57200226370106881382180315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38133484246737920921453543 57200226370106881382180315)
    ·
      refine ⟨85800339555160322073270473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57200226370106881382180315 85800339555160322073270473)
      ·
        refine ⟨64350254666370241554952855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85800339555160322073270473 64350254666370241554952855)
        ·
          refine ⟨96525381999555362332429283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64350254666370241554952855 96525381999555362332429283)
          ·
            refine ⟨144788072999333043498643925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96525381999555362332429283 144788072999333043498643925)
            ·
              refine ⟨3393470460921868206999467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 144788072999333043498643925 3393470460921868206999467)
              ·
                refine ⟨5090205691382802310499201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3393470460921868206999467 5090205691382802310499201)
                ·
                  refine ⟨3817654268537101732874401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5090205691382802310499201 3817654268537101732874401)
                  ·
                    refine ⟨2863240701402826299655801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3817654268537101732874401 2863240701402826299655801)
                    ·
                      refine ⟨2147430526052119724741851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2863240701402826299655801 2147430526052119724741851)
                      ·
                        rfl

theorem cell23_4182106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2].length) (baseStart_4182106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182106 prefixEnd_4182106 := by exact prefixLift 4182106
  have htrace : WordTrace (prefixWord ++ tailWord_4182106) baseStart_4182106 baseEnd_4182106 := by
    simpa [prefixWord, tailWord_4182106, baseEnd_4182106] using wordTrace_append hprefix tailTrace_4182106
  have hstable : (prefixWord ++ tailWord_4182106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182106).length < 2 ^ (prefixWord ++ tailWord_4182106).sum := by decide
  have hdescent : baseEnd_4182106 < baseStart_4182106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182110 : List Nat := [4, 4, 1, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_4182110 : Nat := 118140960795 + 4182110 * 2 ^ 59
def prefixEnd_4182110 : Nat := 4983230072969 + 3 ^ 40 * 4182110 * 2
def baseEnd_4182110 : Nat := 2147432579974737709091833

theorem tailTrace_4182110 : CollatzResearch.WordTrace tailWord_4182110 prefixEnd_4182110 2147432579974737709091833 := by
  unfold tailWord_4182110
  simp only [CollatzResearch.WordTrace]
  refine ⟨19066760359867149046119973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101689388585958128245973189 19066760359867149046119973)
  ·
    refine ⟨3575017567475090446147495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19066760359867149046119973 3575017567475090446147495)
    ·
      refine ⟨5362526351212635669221243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3575017567475090446147495 5362526351212635669221243)
      ·
        refine ⟨8043789526818953503831865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5362526351212635669221243 8043789526818953503831865)
        ·
          refine ⟨6032842145114215127873899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8043789526818953503831865 6032842145114215127873899)
          ·
            refine ⟨9049263217671322691810849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6032842145114215127873899 9049263217671322691810849)
            ·
              refine ⟨6786947413253492018858137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9049263217671322691810849 6786947413253492018858137)
              ·
                refine ⟨5090210559940119014143603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6786947413253492018858137 5090210559940119014143603)
                ·
                  refine ⟨7635315839910178521215405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5090210559940119014143603 7635315839910178521215405)
                  ·
                    refine ⟨2863243439966316945455777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7635315839910178521215405 2863243439966316945455777)
                    ·
                      refine ⟨2147432579974737709091833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2863243439966316945455777 2147432579974737709091833)
                      ·
                        rfl

theorem cell23_4182110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_4182110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182110 prefixEnd_4182110 := by exact prefixLift 4182110
  have htrace : WordTrace (prefixWord ++ tailWord_4182110) baseStart_4182110 baseEnd_4182110 := by
    simpa [prefixWord, tailWord_4182110, baseEnd_4182110] using wordTrace_append hprefix tailTrace_4182110
  have hstable : (prefixWord ++ tailWord_4182110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182110).length < 2 ^ (prefixWord ++ tailWord_4182110).sum := by decide
  have hdescent : baseEnd_4182110 < baseStart_4182110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182125 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 1, 7]
def baseStart_4182125 : Nat := 118140960795 + 4182125 * 2 ^ 59
def prefixEnd_4182125 : Nat := 4983230072969 + 3 ^ 40 * 4182125 * 2
def baseEnd_4182125 : Nat := 715813427394851716801421

theorem tailTrace_4182125 : CollatzResearch.WordTrace tailWord_4182125 prefixEnd_4182125 715813427394851716801421 := by
  unfold tailWord_4182125
  simp only [CollatzResearch.WordTrace]
  refine ⟨152534629973882849930755829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101689753315921899953837219 152534629973882849930755829)
  ·
    refine ⟨14300121560051517181008359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152534629973882849930755829 14300121560051517181008359)
    ·
      refine ⟨21450182340077275771512539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14300121560051517181008359 21450182340077275771512539)
      ·
        refine ⟨32175273510115913657268809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21450182340077275771512539 32175273510115913657268809)
        ·
          refine ⟨24131455132586935242951607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32175273510115913657268809 24131455132586935242951607)
          ·
            refine ⟨36197182698880402864427411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24131455132586935242951607 36197182698880402864427411)
            ·
              refine ⟨54295774048320604296641117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36197182698880402864427411 54295774048320604296641117)
              ·
                refine ⟨20360915268120226611240419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54295774048320604296641117 20360915268120226611240419)
                ·
                  refine ⟨30541372902180339916860629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20360915268120226611240419 30541372902180339916860629)
                  ·
                    refine ⟨715813427394851716801421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30541372902180339916860629 715813427394851716801421)
                    ·
                      rfl

theorem cell23_4182125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_4182125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182125 prefixEnd_4182125 := by exact prefixLift 4182125
  have htrace : WordTrace (prefixWord ++ tailWord_4182125) baseStart_4182125 baseEnd_4182125 := by
    simpa [prefixWord, tailWord_4182125, baseEnd_4182125] using wordTrace_append hprefix tailTrace_4182125
  have hstable : (prefixWord ++ tailWord_4182125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182125).length < 2 ^ (prefixWord ++ tailWord_4182125).sum := by decide
  have hdescent : baseEnd_4182125 < baseStart_4182125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182152 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 1, 2, 5]
def baseStart_4182152 : Nat := 118140960795 + 4182152 * 2 ^ 59
def prefixEnd_4182152 : Nat := 4983230072969 + 3 ^ 40 * 4182152 * 2
def baseEnd_4182152 : Nat := 2147454146162226544766639

theorem tailTrace_4182152 : CollatzResearch.WordTrace tailWord_4182152 prefixEnd_4182152 2147454146162226544766639 := by
  unfold tailWord_4182152
  simp only [CollatzResearch.WordTrace]
  refine ⟨76267807372392516770994355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101690409829856689027992473 76267807372392516770994355)
  ·
    refine ⟨114401711058588775156491533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76267807372392516770994355 114401711058588775156491533)
    ·
      refine ⟨42900641646970790683684325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114401711058588775156491533 42900641646970790683684325)
      ·
        refine ⟨8043870308807023253190811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42900641646970790683684325 8043870308807023253190811)
        ·
          refine ⟨12065805463210534879786217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8043870308807023253190811 12065805463210534879786217)
          ·
            refine ⟨9049354097407901159839663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12065805463210534879786217 9049354097407901159839663)
            ·
              refine ⟨13574031146111851739759495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9049354097407901159839663 13574031146111851739759495)
              ·
                refine ⟨20361046719167777609639243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13574031146111851739759495 20361046719167777609639243)
                ·
                  refine ⟨30541570078751666414458865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20361046719167777609639243 30541570078751666414458865)
                  ·
                    refine ⟨22906177559063749810844149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30541570078751666414458865 22906177559063749810844149)
                    ·
                      refine ⟨2147454146162226544766639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22906177559063749810844149 2147454146162226544766639)
                      ·
                        rfl

theorem cell23_4182152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_4182152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182152 prefixEnd_4182152 := by exact prefixLift 4182152
  have htrace : WordTrace (prefixWord ++ tailWord_4182152) baseStart_4182152 baseEnd_4182152 := by
    simpa [prefixWord, tailWord_4182152, baseEnd_4182152] using wordTrace_append hprefix tailTrace_4182152
  have hstable : (prefixWord ++ tailWord_4182152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182152).length < 2 ^ (prefixWord ++ tailWord_4182152).sum := by decide
  have hdescent : baseEnd_4182152 < baseStart_4182152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182162 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_4182162 : Nat := 118140960795 + 4182162 * 2 ^ 59
def prefixEnd_4182162 : Nat := 4983230072969 + 3 ^ 40 * 4182162 * 2
def baseEnd_4182162 : Nat := 2147459280968771505641593

theorem tailTrace_4182162 : CollatzResearch.WordTrace tailWord_4182162 prefixEnd_4182162 2147459280968771505641593 := by
  unfold tailWord_4182162
  simp only [CollatzResearch.WordTrace]
  refine ⟨38133994868687201312463185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101690652983165870166568493 38133994868687201312463185)
  ·
    refine ⟨28600496151515400984347389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38133994868687201312463185 28600496151515400984347389)
    ·
      refine ⟨10725186056818275369130271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28600496151515400984347389 10725186056818275369130271)
      ·
        refine ⟨16087779085227413053695407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10725186056818275369130271 16087779085227413053695407)
        ·
          refine ⟨24131668627841119580543111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16087779085227413053695407 24131668627841119580543111)
          ·
            refine ⟨36197502941761679370814667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24131668627841119580543111 36197502941761679370814667)
            ·
              refine ⟨54296254412642519056222001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36197502941761679370814667 54296254412642519056222001)
              ·
                refine ⟨40722190809481889292166501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54296254412642519056222001 40722190809481889292166501)
                ·
                  refine ⟨7635410776777854242281219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40722190809481889292166501 7635410776777854242281219)
                  ·
                    refine ⟨11453116165166781363421829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7635410776777854242281219 11453116165166781363421829)
                    ·
                      refine ⟨2147459280968771505641593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11453116165166781363421829 2147459280968771505641593)
                      ·
                        rfl

theorem cell23_4182162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_4182162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182162 prefixEnd_4182162 := by exact prefixLift 4182162
  have htrace : WordTrace (prefixWord ++ tailWord_4182162) baseStart_4182162 baseEnd_4182162 := by
    simpa [prefixWord, tailWord_4182162, baseEnd_4182162] using wordTrace_append hprefix tailTrace_4182162
  have hstable : (prefixWord ++ tailWord_4182162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182162).length < 2 ^ (prefixWord ++ tailWord_4182162).sum := by decide
  have hdescent : baseEnd_4182162 < baseStart_4182162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182172 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 5, 4]
def baseStart_4182172 : Nat := 118140960795 + 4182172 * 2 ^ 59
def prefixEnd_4182172 : Nat := 4983230072969 + 3 ^ 40 * 4182172 * 2
def baseEnd_4182172 : Nat := 715821471925105488838849

theorem tailTrace_4182172 : CollatzResearch.WordTrace tailWord_4182172 prefixEnd_4182172 715821471925105488838849 := by
  unfold tailWord_4182172
  simp only [CollatzResearch.WordTrace]
  refine ⟨76268172102356288478858385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101690896136475051305144513 76268172102356288478858385)
  ·
    refine ⟨57201129076767216359143789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76268172102356288478858385 57201129076767216359143789)
    ·
      refine ⟨21450423403787706134678921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57201129076767216359143789 21450423403787706134678921)
      ·
        refine ⟨16087817552840779601009191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21450423403787706134678921 16087817552840779601009191)
        ·
          refine ⟨24131726329261169401513787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16087817552840779601009191 24131726329261169401513787)
          ·
            refine ⟨36197589493891754102270681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24131726329261169401513787 36197589493891754102270681)
            ·
              refine ⟨27148192120418815576703011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36197589493891754102270681 27148192120418815576703011)
              ·
                refine ⟨40722288180628223365054517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27148192120418815576703011 40722288180628223365054517)
                ·
                  refine ⟨3817714516933895940473861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40722288180628223365054517 3817714516933895940473861)
                  ·
                    refine ⟨715821471925105488838849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3817714516933895940473861 715821471925105488838849)
                    ·
                      rfl

theorem cell23_4182172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_4182172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182172 prefixEnd_4182172 := by exact prefixLift 4182172
  have htrace : WordTrace (prefixWord ++ tailWord_4182172) baseStart_4182172 baseEnd_4182172 := by
    simpa [prefixWord, tailWord_4182172, baseEnd_4182172] using wordTrace_append hprefix tailTrace_4182172
  have hstable : (prefixWord ++ tailWord_4182172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182172).length < 2 ^ (prefixWord ++ tailWord_4182172).sum := by decide
  have hdescent : baseEnd_4182172 < baseStart_4182172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182205 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 1, 2, 6]
def baseStart_4182205 : Nat := 118140960795 + 4182205 * 2 ^ 59
def prefixEnd_4182205 : Nat := 4983230072969 + 3 ^ 40 * 4182205 * 2
def baseEnd_4182205 : Nat := 2147481360636914837403895

theorem tailTrace_4182205 : CollatzResearch.WordTrace tailWord_4182205 prefixEnd_4182205 2147481360636914837403895 := by
  unfold tailWord_4182205
  simp only [CollatzResearch.WordTrace]
  refine ⟨152537547813593023593668069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101691698542395349062445379 152537547813593023593668069)
  ·
    refine ⟨28600790215048691923812763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152537547813593023593668069 28600790215048691923812763)
    ·
      refine ⟨42901185322573037885719145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28600790215048691923812763 42901185322573037885719145)
      ·
        refine ⟨32175888991929778414289359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42901185322573037885719145 32175888991929778414289359)
        ·
          refine ⟨48263833487894667621434039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32175888991929778414289359 48263833487894667621434039)
          ·
            refine ⟨72395750231842001432151059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48263833487894667621434039 72395750231842001432151059)
            ·
              refine ⟨108593625347763002148226589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72395750231842001432151059 108593625347763002148226589)
              ·
                refine ⟨40722609505411125805584971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108593625347763002148226589 40722609505411125805584971)
                ·
                  refine ⟨61083914258116688708377457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40722609505411125805584971 61083914258116688708377457)
                  ·
                    refine ⟨45812935693587516531283093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61083914258116688708377457 45812935693587516531283093)
                    ·
                      refine ⟨2147481360636914837403895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45812935693587516531283093 2147481360636914837403895)
                      ·
                        rfl

theorem cell23_4182205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_4182205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182205 prefixEnd_4182205 := by exact prefixLift 4182205
  have htrace : WordTrace (prefixWord ++ tailWord_4182205) baseStart_4182205 baseEnd_4182205 := by
    simpa [prefixWord, tailWord_4182205, baseEnd_4182205] using wordTrace_append hprefix tailTrace_4182205
  have hstable : (prefixWord ++ tailWord_4182205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182205).length < 2 ^ (prefixWord ++ tailWord_4182205).sum := by decide
  have hdescent : baseEnd_4182205 < baseStart_4182205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182232 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 3, 5]
def baseStart_4182232 : Nat := 118140960795 + 4182232 * 2 ^ 59
def prefixEnd_4182232 : Nat := 4983230072969 + 3 ^ 40 * 4182232 * 2
def baseEnd_4182232 : Nat := 715831741538195410588757

theorem tailTrace_4182232 : CollatzResearch.WordTrace tailWord_4182232 prefixEnd_4182232 715831741538195410588757 := by
  unfold tailWord_4182232
  simp only [CollatzResearch.WordTrace]
  refine ⟨76269266292247603602450475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101692355056330138136600633 76269266292247603602450475)
  ·
    refine ⟨114403899438371405403675713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76269266292247603602450475 114403899438371405403675713)
    ·
      refine ⟨85802924578778554052756785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114403899438371405403675713 85802924578778554052756785)
      ·
        refine ⟨64352193434083915539567589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85802924578778554052756785 64352193434083915539567589)
        ·
          refine ⟨12066036268890734163668923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64352193434083915539567589 12066036268890734163668923)
          ·
            refine ⟨18099054403336101245503385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12066036268890734163668923 18099054403336101245503385)
            ·
              refine ⟨13574290802502075934127539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18099054403336101245503385 13574290802502075934127539)
              ·
                refine ⟨20361436203753113901191309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13574290802502075934127539 20361436203753113901191309)
                ·
                  refine ⟨7635538576407417712946741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20361436203753113901191309 7635538576407417712946741)
                  ·
                    refine ⟨715831741538195410588757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7635538576407417712946741 715831741538195410588757)
                    ·
                      rfl

theorem cell23_4182232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_4182232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182232 prefixEnd_4182232 := by exact prefixLift 4182232
  have htrace : WordTrace (prefixWord ++ tailWord_4182232) baseStart_4182232 baseEnd_4182232 := by
    simpa [prefixWord, tailWord_4182232, baseEnd_4182232] using wordTrace_append hprefix tailTrace_4182232
  have hstable : (prefixWord ++ tailWord_4182232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182232).length < 2 ^ (prefixWord ++ tailWord_4182232).sum := by decide
  have hdescent : baseEnd_4182232 < baseStart_4182232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182262 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 3, 6]
def baseStart_4182262 : Nat := 118140960795 + 4182262 * 2 ^ 59
def prefixEnd_4182262 : Nat := 4983230072969 + 3 ^ 40 * 4182262 * 2
def baseEnd_4182262 : Nat := 715836876344740371463711

theorem tailTrace_4182262 : CollatzResearch.WordTrace tailWord_4182262 prefixEnd_4182262 715836876344740371463711 := by
  unfold tailWord_4182262
  simp only [CollatzResearch.WordTrace]
  refine ⟨9533726673399157645530815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101693084516257681552328693 9533726673399157645530815)
  ·
    refine ⟨14300590010098736468296223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9533726673399157645530815 14300590010098736468296223)
    ·
      refine ⟨21450885015148104702444335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14300590010098736468296223 21450885015148104702444335)
      ·
        refine ⟨32176327522722157053666503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21450885015148104702444335 32176327522722157053666503)
        ·
          refine ⟨48264491284083235580499755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32176327522722157053666503 48264491284083235580499755)
          ·
            refine ⟨72396736926124853370749633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48264491284083235580499755 72396736926124853370749633)
            ·
              refine ⟨54297552694593640028062225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72396736926124853370749633 54297552694593640028062225)
              ·
                refine ⟨40723164520945230021046669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54297552694593640028062225 40723164520945230021046669)
                ·
                  refine ⟨15271186695354461257892501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40723164520945230021046669 15271186695354461257892501)
                  ·
                    refine ⟨715836876344740371463711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15271186695354461257892501 715836876344740371463711)
                    ·
                      rfl

theorem cell23_4182262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_4182262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182262 prefixEnd_4182262 := by exact prefixLift 4182262
  have htrace : WordTrace (prefixWord ++ tailWord_4182262) baseStart_4182262 baseEnd_4182262 := by
    simpa [prefixWord, tailWord_4182262, baseEnd_4182262] using wordTrace_append hprefix tailTrace_4182262
  have hstable : (prefixWord ++ tailWord_4182262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182262).length < 2 ^ (prefixWord ++ tailWord_4182262).sum := by decide
  have hdescent : baseEnd_4182262 < baseStart_4182262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182272 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 3]
def baseStart_4182272 : Nat := 118140960795 + 4182272 * 2 ^ 59
def prefixEnd_4182272 : Nat := 4983230072969 + 3 ^ 40 * 4182272 * 2
def baseEnd_4182272 : Nat := 2147515763840766075266087

theorem tailTrace_4182272 : CollatzResearch.WordTrace tailWord_4182272 prefixEnd_4182272 2147515763840766075266087 := by
  unfold tailWord_4182272
  simp only [CollatzResearch.WordTrace]
  refine ⟨76269995752175147018178535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101693327669566862690904713 76269995752175147018178535)
  ·
    refine ⟨114404993628262720527267803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76269995752175147018178535 114404993628262720527267803)
    ·
      refine ⟨171607490442394080790901705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114404993628262720527267803 171607490442394080790901705)
      ·
        refine ⟨128705617831795560593176279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171607490442394080790901705 128705617831795560593176279)
        ·
          refine ⟨193058426747693340889764419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128705617831795560593176279 193058426747693340889764419)
          ·
            refine ⟨289587640121540011334646629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193058426747693340889764419 289587640121540011334646629)
            ·
              refine ⟨54297682522788752125246243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289587640121540011334646629 54297682522788752125246243)
              ·
                refine ⟨81446523784183128187869365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54297682522788752125246243 81446523784183128187869365)
                ·
                  refine ⟨7635611604767168267612753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81446523784183128187869365 7635611604767168267612753)
                  ·
                    refine ⟨5726708703575376200709565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7635611604767168267612753 5726708703575376200709565)
                    ·
                      refine ⟨2147515763840766075266087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5726708703575376200709565 2147515763840766075266087)
                      ·
                        rfl

theorem cell23_4182272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 3].length) (baseStart_4182272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182272 prefixEnd_4182272 := by exact prefixLift 4182272
  have htrace : WordTrace (prefixWord ++ tailWord_4182272) baseStart_4182272 baseEnd_4182272 := by
    simpa [prefixWord, tailWord_4182272, baseEnd_4182272] using wordTrace_append hprefix tailTrace_4182272
  have hstable : (prefixWord ++ tailWord_4182272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182272).length < 2 ^ (prefixWord ++ tailWord_4182272).sum := by decide
  have hdescent : baseEnd_4182272 < baseStart_4182272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182275 : List Nat := [1, 1, 1, 3, 2, 3, 2, 10]
def baseStart_4182275 : Nat := 118140960795 + 4182275 * 2 ^ 59
def prefixEnd_4182275 : Nat := 4983230072969 + 3 ^ 40 * 4182275 * 2
def baseEnd_4182275 : Nat := 79537677936397391241799

theorem tailTrace_4182275 : CollatzResearch.WordTrace tailWord_4182275 prefixEnd_4182275 79537677936397391241799 := by
  unfold tailWord_4182275
  simp only [CollatzResearch.WordTrace]
  refine ⟨152540100923339425548716279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101693400615559617032477519 152540100923339425548716279)
  ·
    refine ⟨228810151385009138323074419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152540100923339425548716279 228810151385009138323074419)
    ·
      refine ⟨343215227077513707484611629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228810151385009138323074419 343215227077513707484611629)
      ·
        refine ⟨128705710154067640306729361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343215227077513707484611629 128705710154067640306729361)
        ·
          refine ⟨96529282615550730230047021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128705710154067640306729361 96529282615550730230047021)
          ·
            refine ⟨36198480980831523836267633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96529282615550730230047021 36198480980831523836267633)
            ·
              refine ⟨27148860735623642877200725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36198480980831523836267633 27148860735623642877200725)
              ·
                refine ⟨79537677936397391241799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27148860735623642877200725 79537677936397391241799)
                ·
                  rfl

theorem cell23_4182275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 10].length) (baseStart_4182275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182275 prefixEnd_4182275 := by exact prefixLift 4182275
  have htrace : WordTrace (prefixWord ++ tailWord_4182275) baseStart_4182275 baseEnd_4182275 := by
    simpa [prefixWord, tailWord_4182275, baseEnd_4182275] using wordTrace_append hprefix tailTrace_4182275
  have hstable : (prefixWord ++ tailWord_4182275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182275).length < 2 ^ (prefixWord ++ tailWord_4182275).sum := by decide
  have hdescent : baseEnd_4182275 < baseStart_4182275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182286 : List Nat := [4, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2]
def baseStart_4182286 : Nat := 118140960795 + 4182286 * 2 ^ 59
def prefixEnd_4182286 : Nat := 4983230072969 + 3 ^ 40 * 4182286 * 2
def baseEnd_4182286 : Nat := 2147522952569929020491023

theorem tailTrace_4182286 : CollatzResearch.WordTrace tailWord_4182286 prefixEnd_4182286 2147522952569929020491023 := by
  unfold tailWord_4182286
  simp only [CollatzResearch.WordTrace]
  refine ⟨19067562765787446803420839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101693668084199716284911141 19067562765787446803420839)
  ·
    refine ⟨28601344148681170205131259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19067562765787446803420839 28601344148681170205131259)
    ·
      refine ⟨42902016223021755307696889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28601344148681170205131259 42902016223021755307696889)
      ·
        refine ⟨32176512167266316480772667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42902016223021755307696889 32176512167266316480772667)
        ·
          refine ⟨48264768250899474721159001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32176512167266316480772667 48264768250899474721159001)
          ·
            refine ⟨36198576188174606040869251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48264768250899474721159001 36198576188174606040869251)
            ·
              refine ⟨54297864282261909061303877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36198576188174606040869251 54297864282261909061303877)
              ·
                refine ⟨10180849552924107948994477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54297864282261909061303877 10180849552924107948994477)
                ·
                  refine ⟨3817818582346540480872929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10180849552924107948994477 3817818582346540480872929)
                  ·
                    refine ⟨2863363936759905360654697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3817818582346540480872929 2863363936759905360654697)
                    ·
                      refine ⟨2147522952569929020491023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2863363936759905360654697 2147522952569929020491023)
                      ·
                        rfl

theorem cell23_4182286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_4182286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182286 prefixEnd_4182286 := by exact prefixLift 4182286
  have htrace : WordTrace (prefixWord ++ tailWord_4182286) baseStart_4182286 baseEnd_4182286 := by
    simpa [prefixWord, tailWord_4182286, baseEnd_4182286] using wordTrace_append hprefix tailTrace_4182286
  have hstable : (prefixWord ++ tailWord_4182286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182286).length < 2 ^ (prefixWord ++ tailWord_4182286).sum := by decide
  have hdescent : baseEnd_4182286 < baseStart_4182286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182289 : List Nat := [1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 3]
def baseStart_4182289 : Nat := 118140960795 + 4182289 * 2 ^ 59
def prefixEnd_4182289 : Nat := 4983230072969 + 3 ^ 40 * 4182289 * 2
def baseEnd_4182289 : Nat := 2147524493011892508753509

theorem tailTrace_4182289 : CollatzResearch.WordTrace tailWord_4182289 prefixEnd_4182289 2147524493011892508753509 := by
  unfold tailWord_4182289
  simp only [CollatzResearch.WordTrace]
  refine ⟨152540611545288705939725921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101693741030192470626483947 152540611545288705939725921)
  ·
    refine ⟨114405458658966529454794441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152540611545288705939725921 114405458658966529454794441)
    ·
      refine ⟨85804093994224897091095831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114405458658966529454794441 85804093994224897091095831)
      ·
        refine ⟨128706140991337345636643747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85804093994224897091095831 128706140991337345636643747)
        ·
          refine ⟨193059211487006018454965621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128706140991337345636643747 193059211487006018454965621)
          ·
            refine ⟨18099301076906814230153027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 193059211487006018454965621 18099301076906814230153027)
            ·
              refine ⟨27148951615360221345229541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18099301076906814230153027 27148951615360221345229541)
              ·
                refine ⟨5090428427880041502230539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27148951615360221345229541 5090428427880041502230539)
                ·
                  refine ⟨7635642641820062253345809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5090428427880041502230539 7635642641820062253345809)
                  ·
                    refine ⟨5726731981365046690009357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7635642641820062253345809 5726731981365046690009357)
                    ·
                      refine ⟨2147524493011892508753509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5726731981365046690009357 2147524493011892508753509)
                      ·
                        rfl

theorem cell23_4182289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 3].length) (baseStart_4182289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182289 prefixEnd_4182289 := by exact prefixLift 4182289
  have htrace : WordTrace (prefixWord ++ tailWord_4182289) baseStart_4182289 baseEnd_4182289 := by
    simpa [prefixWord, tailWord_4182289, baseEnd_4182289] using wordTrace_append hprefix tailTrace_4182289
  have hstable : (prefixWord ++ tailWord_4182289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182289).length < 2 ^ (prefixWord ++ tailWord_4182289).sum := by decide
  have hdescent : baseEnd_4182289 < baseStart_4182289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182306 : List Nat := [3, 3, 1, 1, 3, 1, 2, 3, 1, 2, 3]
def baseStart_4182306 : Nat := 118140960795 + 4182306 * 2 ^ 59
def prefixEnd_4182306 : Nat := 4983230072969 + 3 ^ 40 * 4182306 * 2
def baseEnd_4182306 : Nat := 2147533222183018942240931

theorem tailTrace_4182306 : CollatzResearch.WordTrace tailWord_4182306 prefixEnd_4182306 2147533222183018942240931 := by
  unfold tailWord_4182306
  simp only [CollatzResearch.WordTrace]
  refine ⟨38135307896556779460773693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101694154390818078562063181 38135307896556779460773693)
  ·
    refine ⟨14300740461208792297790135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38135307896556779460773693 14300740461208792297790135)
    ·
      refine ⟨21451110691813188446685203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14300740461208792297790135 21451110691813188446685203)
      ·
        refine ⟨32176666037719782670027805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21451110691813188446685203 32176666037719782670027805)
        ·
          refine ⟨12066249764144918501260427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32176666037719782670027805 12066249764144918501260427)
          ·
            refine ⟨18099374646217377751890641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12066249764144918501260427 18099374646217377751890641)
            ·
              refine ⟨13574530984663033313917981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18099374646217377751890641 13574530984663033313917981)
              ·
                refine ⟨5090449119248637492719243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13574530984663033313917981 5090449119248637492719243)
                ·
                  refine ⟨7635673678872956239078865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5090449119248637492719243 7635673678872956239078865)
                  ·
                    refine ⟨5726755259154717179309149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7635673678872956239078865 5726755259154717179309149)
                    ·
                      refine ⟨2147533222183018942240931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5726755259154717179309149 2147533222183018942240931)
                      ·
                        rfl

theorem cell23_4182306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_4182306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182306 prefixEnd_4182306 := by exact prefixLift 4182306
  have htrace : WordTrace (prefixWord ++ tailWord_4182306) baseStart_4182306 baseEnd_4182306 := by
    simpa [prefixWord, tailWord_4182306, baseEnd_4182306] using wordTrace_append hprefix tailTrace_4182306
  have hstable : (prefixWord ++ tailWord_4182306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182306).length < 2 ^ (prefixWord ++ tailWord_4182306).sum := by decide
  have hdescent : baseEnd_4182306 < baseStart_4182306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182309 : List Nat := [1, 3, 1, 2, 6, 1, 9]
def baseStart_4182309 : Nat := 118140960795 + 4182309 * 2 ^ 59
def prefixEnd_4182309 : Nat := 4983230072969 + 3 ^ 40 * 4182309 * 2
def baseEnd_4182309 : Nat := 26512774847222005314857

theorem tailTrace_4182309 : CollatzResearch.WordTrace tailWord_4182309 prefixEnd_4182309 26512774847222005314857 := by
  unfold tailWord_4182309
  simp only [CollatzResearch.WordTrace]
  refine ⟨152541341005216249355453981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101694227336810832903635987 152541341005216249355453981)
  ·
    refine ⟨57203002876956093508295243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152541341005216249355453981 57203002876956093508295243)
    ·
      refine ⟨85804504315434140262442865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57203002876956093508295243 85804504315434140262442865)
      ·
        refine ⟨64353378236575605196832149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85804504315434140262442865 64353378236575605196832149)
        ·
          refine ⟨3016564604839481493601507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64353378236575605196832149 3016564604839481493601507)
          ·
            refine ⟨4524846907259222240402261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3016564604839481493601507 4524846907259222240402261)
            ·
              refine ⟨26512774847222005314857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4524846907259222240402261 26512774847222005314857)
              ·
                rfl

theorem cell23_4182309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 9].length) (baseStart_4182309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182309 prefixEnd_4182309 := by exact prefixLift 4182309
  have htrace : WordTrace (prefixWord ++ tailWord_4182309) baseStart_4182309 baseEnd_4182309 := by
    simpa [prefixWord, tailWord_4182309, baseEnd_4182309] using wordTrace_append hprefix tailTrace_4182309
  have hstable : (prefixWord ++ tailWord_4182309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182309).length < 2 ^ (prefixWord ++ tailWord_4182309).sum := by decide
  have hdescent : baseEnd_4182309 < baseStart_4182309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182315 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 7]
def baseStart_4182315 : Nat := 118140960795 + 4182315 * 2 ^ 59
def prefixEnd_4182315 : Nat := 4983230072969 + 3 ^ 40 * 4182315 * 2
def baseEnd_4182315 : Nat := 2147537843508909407028389

theorem tailTrace_4182315 : CollatzResearch.WordTrace tailWord_4182315 prefixEnd_4182315 2147537843508909407028389 := by
  unfold tailWord_4182315
  simp only [CollatzResearch.WordTrace]
  refine ⟨152541559843194512380172399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101694373228796341586781599 152541559843194512380172399)
  ·
    refine ⟨228812339764791768570258599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152541559843194512380172399 228812339764791768570258599)
    ·
      refine ⟨343218509647187652855387899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228812339764791768570258599 343218509647187652855387899)
      ·
        refine ⟨514827764470781479283081849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343218509647187652855387899 514827764470781479283081849)
        ·
          refine ⟨386120823353086109462311387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514827764470781479283081849 386120823353086109462311387)
          ·
            refine ⟨579181235029629164193467081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386120823353086109462311387 579181235029629164193467081)
            ·
              refine ⟨434385926272221873145100311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579181235029629164193467081 434385926272221873145100311)
              ·
                refine ⟨651578889408332809717650467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434385926272221873145100311 651578889408332809717650467)
                ·
                  refine ⟨977368334112499214576475701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 651578889408332809717650467 977368334112499214576475701)
                  ·
                    refine ⟨91628281323046801366544597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 977368334112499214576475701 91628281323046801366544597)
                    ·
                      refine ⟨2147537843508909407028389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91628281323046801366544597 2147537843508909407028389)
                      ·
                        rfl

theorem cell23_4182315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 7].length) (baseStart_4182315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182315 prefixEnd_4182315 := by exact prefixLift 4182315
  have htrace : WordTrace (prefixWord ++ tailWord_4182315) baseStart_4182315 baseEnd_4182315 := by
    simpa [prefixWord, tailWord_4182315, baseEnd_4182315] using wordTrace_append hprefix tailTrace_4182315
  have hstable : (prefixWord ++ tailWord_4182315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182315).length < 2 ^ (prefixWord ++ tailWord_4182315).sum := by decide
  have hdescent : baseEnd_4182315 < baseStart_4182315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182319 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 4, 1, 3]
def baseStart_4182319 : Nat := 118140960795 + 4182319 * 2 ^ 59
def prefixEnd_4182319 : Nat := 4983230072969 + 3 ^ 40 * 4182319 * 2
def baseEnd_4182319 : Nat := 2147539897431527391378371

theorem tailTrace_4182319 : CollatzResearch.WordTrace tailWord_4182319 prefixEnd_4182319 2147539897431527391378371 := by
  unfold tailWord_4182319
  simp only [CollatzResearch.WordTrace]
  refine ⟨152541705735180021063318011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101694470490120014042212007 152541705735180021063318011)
  ·
    refine ⟨228812558602770031594977017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152541705735180021063318011 228812558602770031594977017)
    ·
      refine ⟨171609418952077523696232763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228812558602770031594977017 171609418952077523696232763)
      ·
        refine ⟨257414128428116285544349145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171609418952077523696232763 257414128428116285544349145)
        ·
          refine ⟨193060596321087214158261859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257414128428116285544349145 193060596321087214158261859)
          ·
            refine ⟨289590894481630821237392789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193060596321087214158261859 289590894481630821237392789)
            ·
              refine ⟨13574573178826444745502787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 289590894481630821237392789 13574573178826444745502787)
              ·
                refine ⟨20361859768239667118254181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13574573178826444745502787 20361859768239667118254181)
                ·
                  refine ⟨3817848706544937584672659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20361859768239667118254181 3817848706544937584672659)
                  ·
                    refine ⟨5726773059817406377008989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3817848706544937584672659 5726773059817406377008989)
                    ·
                      refine ⟨2147539897431527391378371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5726773059817406377008989 2147539897431527391378371)
                      ·
                        rfl

theorem cell23_4182319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 1, 3].length) (baseStart_4182319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182319 prefixEnd_4182319 := by exact prefixLift 4182319
  have htrace : WordTrace (prefixWord ++ tailWord_4182319) baseStart_4182319 baseEnd_4182319 := by
    simpa [prefixWord, tailWord_4182319, baseEnd_4182319] using wordTrace_append hprefix tailTrace_4182319
  have hstable : (prefixWord ++ tailWord_4182319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182319).length < 2 ^ (prefixWord ++ tailWord_4182319).sum := by decide
  have hdescent : baseEnd_4182319 < baseStart_4182319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182340 : List Nat := [2, 3, 4, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_4182340 : Nat := 118140960795 + 4182340 * 2 ^ 59
def prefixEnd_4182340 : Nat := 4983230072969 + 3 ^ 40 * 4182340 * 2
def baseEnd_4182340 : Nat := 2147550680525271809215775

theorem tailTrace_4182340 : CollatzResearch.WordTrace tailWord_4182340 prefixEnd_4182340 2147550680525271809215775 := by
  unfold tailWord_4182340
  simp only [CollatzResearch.WordTrace]
  refine ⟨76271235834051970824916237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101694981112069294433221649 76271235834051970824916237)
  ·
    refine ⟨28601713437769489059343589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76271235834051970824916237 28601713437769489059343589)
    ·
      refine ⟨5362821269581779198626923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28601713437769489059343589 5362821269581779198626923)
      ·
        refine ⟨8044231904372668797940385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5362821269581779198626923 8044231904372668797940385)
        ·
          refine ⟨6033173928279501598455289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8044231904372668797940385 6033173928279501598455289)
          ·
            refine ⟨4524880446209626198841467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6033173928279501598455289 4524880446209626198841467)
            ·
              refine ⟨6787320669314439298262201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4524880446209626198841467 6787320669314439298262201)
              ·
                refine ⟨5090490501985829473696651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6787320669314439298262201 5090490501985829473696651)
                ·
                  refine ⟨7635735752978744210544977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5090490501985829473696651 7635735752978744210544977)
                  ·
                    refine ⟨5726801814734058157908733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7635735752978744210544977 5726801814734058157908733)
                    ·
                      refine ⟨2147550680525271809215775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5726801814734058157908733 2147550680525271809215775)
                      ·
                        rfl

theorem cell23_4182340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_4182340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182340 prefixEnd_4182340 := by exact prefixLift 4182340
  have htrace : WordTrace (prefixWord ++ tailWord_4182340) baseStart_4182340 baseEnd_4182340 := by
    simpa [prefixWord, tailWord_4182340, baseEnd_4182340] using wordTrace_append hprefix tailTrace_4182340
  have hstable : (prefixWord ++ tailWord_4182340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182340).length < 2 ^ (prefixWord ++ tailWord_4182340).sum := by decide
  have hdescent : baseEnd_4182340 < baseStart_4182340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182389 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_4182389 : Nat := 118140960795 + 4182389 * 2 ^ 59
def prefixEnd_4182389 : Nat := 4983230072969 + 3 ^ 40 * 4182389 * 2
def baseEnd_4182389 : Nat := 2147575841077342117503049

theorem tailTrace_4182389 : CollatzResearch.WordTrace tailWord_4182389 prefixEnd_4182389 2147575841077342117503049 := by
  unfold tailWord_4182389
  simp only [CollatzResearch.WordTrace]
  refine ⟨152544258844926423018366221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101696172563284282012244147 152544258844926423018366221)
  ·
    refine ⟨57204097066847408631887333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152544258844926423018366221 57204097066847408631887333)
    ·
      refine ⟨10725768200033889118478875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57204097066847408631887333 10725768200033889118478875)
      ·
        refine ⟨16088652300050833677718313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10725768200033889118478875 16088652300050833677718313)
        ·
          refine ⟨12066489225038125258288735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16088652300050833677718313 12066489225038125258288735)
          ·
            refine ⟨18099733837557187887433103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12066489225038125258288735 18099733837557187887433103)
            ·
              refine ⟨27149600756335781831149655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18099733837557187887433103 27149600756335781831149655)
              ·
                refine ⟨40724401134503672746724483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27149600756335781831149655 40724401134503672746724483)
                ·
                  refine ⟨61086601701755509120086725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40724401134503672746724483 61086601701755509120086725)
                  ·
                    refine ⟨11453737819079157960016261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61086601701755509120086725 11453737819079157960016261)
                    ·
                      refine ⟨2147575841077342117503049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11453737819079157960016261 2147575841077342117503049)
                      ·
                        rfl

theorem cell23_4182389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_4182389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182389 prefixEnd_4182389 := by exact prefixLift 4182389
  have htrace : WordTrace (prefixWord ++ tailWord_4182389) baseStart_4182389 baseEnd_4182389 := by
    simpa [prefixWord, tailWord_4182389, baseEnd_4182389] using wordTrace_append hprefix tailTrace_4182389
  have hstable : (prefixWord ++ tailWord_4182389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182389).length < 2 ^ (prefixWord ++ tailWord_4182389).sum := by decide
  have hdescent : baseEnd_4182389 < baseStart_4182389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182449 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 1, 3, 4]
def baseStart_4182449 : Nat := 118140960795 + 4182449 * 2 ^ 59
def prefixEnd_4182449 : Nat := 4983230072969 + 3 ^ 40 * 4182449 * 2
def baseEnd_4182449 : Nat := 2147606649916611882752773

theorem tailTrace_4182449 : CollatzResearch.WordTrace tailWord_4182449 prefixEnd_4182449 2147606649916611882752773 := by
  unfold tailWord_4182449
  simp only [CollatzResearch.WordTrace]
  refine ⟨152546447224709053265550401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101697631483139368843700267 152546447224709053265550401)
  ·
    refine ⟨114409835418531789949162801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152546447224709053265550401 114409835418531789949162801)
    ·
      refine ⟨85807376563898842461872101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114409835418531789949162801 85807376563898842461872101)
      ·
        refine ⟨16088883105731032961601019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85807376563898842461872101 16088883105731032961601019)
        ·
          refine ⟨24133324658596549442401529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16088883105731032961601019 24133324658596549442401529)
          ·
            refine ⟨18099993493947412081801147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24133324658596549442401529 18099993493947412081801147)
            ·
              refine ⟨27149990240921118122701721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18099993493947412081801147 27149990240921118122701721)
              ·
                refine ⟨20362492680690838592026291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27149990240921118122701721 20362492680690838592026291)
                ·
                  refine ⟨30543739021036257888039437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20362492680690838592026291 30543739021036257888039437)
                  ·
                    refine ⟨11453902132888596708014789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30543739021036257888039437 11453902132888596708014789)
                    ·
                      refine ⟨2147606649916611882752773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11453902132888596708014789 2147606649916611882752773)
                      ·
                        rfl

theorem cell23_4182449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_4182449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182449 prefixEnd_4182449 := by exact prefixLift 4182449
  have htrace : WordTrace (prefixWord ++ tailWord_4182449) baseStart_4182449 baseEnd_4182449 := by
    simpa [prefixWord, tailWord_4182449, baseEnd_4182449] using wordTrace_append hprefix tailTrace_4182449
  have hstable : (prefixWord ++ tailWord_4182449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182449).length < 2 ^ (prefixWord ++ tailWord_4182449).sum := by decide
  have hdescent : baseEnd_4182449 < baseStart_4182449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182469 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 8, 2, 3]
def baseStart_4182469 : Nat := 118140960795 + 4182469 * 2 ^ 59
def prefixEnd_4182469 : Nat := 4983230072969 + 3 ^ 40 * 4182469 * 2
def baseEnd_4182469 : Nat := 2147616919529701804502681

theorem tailTrace_4182469 : CollatzResearch.WordTrace tailWord_4182469 prefixEnd_4182469 2147616919529701804502681 := by
  unfold tailWord_4182469
  simp only [CollatzResearch.WordTrace]
  refine ⟨152547176684636596681278461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101698117789757731120852307 152547176684636596681278461)
  ·
    refine ⟨57205191256738723755479423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152547176684636596681278461 57205191256738723755479423)
    ·
      refine ⟨85807786885108085633219135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57205191256738723755479423 85807786885108085633219135)
      ·
        refine ⟨128711680327662128449828703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85807786885108085633219135 128711680327662128449828703)
        ·
          refine ⟨193067520491493192674743055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128711680327662128449828703 193067520491493192674743055)
          ·
            refine ⟨289601280737239789012114583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193067520491493192674743055 289601280737239789012114583)
            ·
              refine ⟨434401921105859683518171875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289601280737239789012114583 434401921105859683518171875)
              ·
                refine ⟨651602881658789525277257813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434401921105859683518171875 651602881658789525277257813)
                ·
                  refine ⟨7635971269438939749342865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 651602881658789525277257813 7635971269438939749342865)
                  ·
                    refine ⟨5726978452079204812007149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7635971269438939749342865 5726978452079204812007149)
                    ·
                      refine ⟨2147616919529701804502681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5726978452079204812007149 2147616919529701804502681)
                      ·
                        rfl

theorem cell23_4182469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 2, 3].length) (baseStart_4182469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182469 prefixEnd_4182469 := by exact prefixLift 4182469
  have htrace : WordTrace (prefixWord ++ tailWord_4182469) baseStart_4182469 baseEnd_4182469 := by
    simpa [prefixWord, tailWord_4182469, baseEnd_4182469] using wordTrace_append hprefix tailTrace_4182469
  have hstable : (prefixWord ++ tailWord_4182469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182469).length < 2 ^ (prefixWord ++ tailWord_4182469).sum := by decide
  have hdescent : baseEnd_4182469 < baseStart_4182469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182489 : List Nat := [1, 2, 1, 2, 4, 1, 2, 4, 6]
def baseStart_4182489 : Nat := 118140960795 + 4182489 * 2 ^ 59
def prefixEnd_4182489 : Nat := 4983230072969 + 3 ^ 40 * 4182489 * 2
def baseEnd_4182489 : Nat := 238625243238087969583621

theorem tailTrace_4182489 : CollatzResearch.WordTrace tailWord_4182489 prefixEnd_4182489 238625243238087969583621 := by
  unfold tailWord_4182489
  simp only [CollatzResearch.WordTrace]
  refine ⟨152547906144564140097006521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101698604096376093398004347 152547906144564140097006521)
  ·
    refine ⟨114410929608423105072754891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152547906144564140097006521 114410929608423105072754891)
    ·
      refine ⟨171616394412634657609132337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114410929608423105072754891 171616394412634657609132337)
      ·
        refine ⟨128712295809475993206849253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171616394412634657609132337 128712295809475993206849253)
        ·
          refine ⟨24133555464276748726284235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128712295809475993206849253 24133555464276748726284235)
          ·
            refine ⟨36200333196415123089426353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24133555464276748726284235 36200333196415123089426353)
            ·
              refine ⟨27150249897311342317069765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36200333196415123089426353 27150249897311342317069765)
              ·
                refine ⟨5090671855745876684450581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27150249897311342317069765 5090671855745876684450581)
                ·
                  refine ⟨238625243238087969583621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5090671855745876684450581 238625243238087969583621)
                  ·
                    rfl

theorem cell23_4182489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 6].length) (baseStart_4182489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182489 prefixEnd_4182489 := by exact prefixLift 4182489
  have htrace : WordTrace (prefixWord ++ tailWord_4182489) baseStart_4182489 baseEnd_4182489 := by
    simpa [prefixWord, tailWord_4182489, baseEnd_4182489] using wordTrace_append hprefix tailTrace_4182489
  have hstable : (prefixWord ++ tailWord_4182489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182489).length < 2 ^ (prefixWord ++ tailWord_4182489).sum := by decide
  have hdescent : baseEnd_4182489 < baseStart_4182489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182506 : List Nat := [3, 1, 3, 1, 3, 2, 1, 3, 6]
def baseStart_4182506 : Nat := 118140960795 + 4182506 * 2 ^ 59
def prefixEnd_4182506 : Nat := 4983230072969 + 3 ^ 40 * 4182506 * 2
def baseEnd_4182506 : Nat := 238626213145990906637779

theorem tailTrace_4182506 : CollatzResearch.WordTrace tailWord_4182506 prefixEnd_4182506 238626213145990906637779 := by
  unfold tailWord_4182506
  simp only [CollatzResearch.WordTrace]
  refine ⟨38137131546375638000093843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101699017457001701333583581 38137131546375638000093843)
  ·
    refine ⟨57205697319563457000140765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38137131546375638000093843 57205697319563457000140765)
    ·
      refine ⟨21452136494836296375052787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57205697319563457000140765 21452136494836296375052787)
      ·
        refine ⟨32178204742254444562579181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21452136494836296375052787 32178204742254444562579181)
        ·
          refine ⟨12066826778345416710967193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32178204742254444562579181 12066826778345416710967193)
          ·
            refine ⟨9050120083759062533225395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12066826778345416710967193 9050120083759062533225395)
            ·
              refine ⟨13575180125638593799838093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9050120083759062533225395 13575180125638593799838093)
              ·
                refine ⟨5090692547114472674939285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13575180125638593799838093 5090692547114472674939285)
                ·
                  refine ⟨238626213145990906637779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5090692547114472674939285 238626213145990906637779)
                  ·
                    rfl

theorem cell23_4182506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 6].length) (baseStart_4182506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182506 prefixEnd_4182506 := by exact prefixLift 4182506
  have htrace : WordTrace (prefixWord ++ tailWord_4182506) baseStart_4182506 baseEnd_4182506 := by
    simpa [prefixWord, tailWord_4182506, baseEnd_4182506] using wordTrace_append hprefix tailTrace_4182506
  have hstable : (prefixWord ++ tailWord_4182506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182506).length < 2 ^ (prefixWord ++ tailWord_4182506).sum := by decide
  have hdescent : baseEnd_4182506 < baseStart_4182506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182549 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 3, 6]
def baseStart_4182549 : Nat := 118140960795 + 4182549 * 2 ^ 59
def prefixEnd_4182549 : Nat := 4983230072969 + 3 ^ 40 * 4182549 * 2
def baseEnd_4182549 : Nat := 715885999327353830500771

theorem tailTrace_4182549 : CollatzResearch.WordTrace tailWord_4182549 prefixEnd_4182549 715885999327353830500771 := by
  unfold tailWord_4182549
  simp only [CollatzResearch.WordTrace]
  refine ⟨152550094524346770344190701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101700063016231180229460467 152550094524346770344190701)
  ·
    refine ⟨57206285446630038879071513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152550094524346770344190701 57206285446630038879071513)
    ·
      refine ⟨42904714084972529159303635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57206285446630038879071513 42904714084972529159303635)
      ·
        refine ⟨64357071127458793738955453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42904714084972529159303635 64357071127458793738955453)
        ·
          refine ⟨24133901672797047652108295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64357071127458793738955453 24133901672797047652108295)
          ·
            refine ⟨36200852509195571478162443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24133901672797047652108295 36200852509195571478162443)
            ·
              refine ⟨54301278763793357217243665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36200852509195571478162443 54301278763793357217243665)
              ·
                refine ⟨40725959072845017912932749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54301278763793357217243665 40725959072845017912932749)
                ·
                  refine ⟨15272234652316881717349781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40725959072845017912932749 15272234652316881717349781)
                  ·
                    refine ⟨715885999327353830500771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15272234652316881717349781 715885999327353830500771)
                    ·
                      rfl

theorem cell23_4182549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_4182549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182549 prefixEnd_4182549 := by exact prefixLift 4182549
  have htrace : WordTrace (prefixWord ++ tailWord_4182549) baseStart_4182549 baseEnd_4182549 := by
    simpa [prefixWord, tailWord_4182549, baseEnd_4182549] using wordTrace_append hprefix tailTrace_4182549
  have hstable : (prefixWord ++ tailWord_4182549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182549).length < 2 ^ (prefixWord ++ tailWord_4182549).sum := by decide
  have hdescent : baseEnd_4182549 < baseStart_4182549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182556 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_4182556 : Nat := 118140960795 + 4182556 * 2 ^ 59
def prefixEnd_4182556 : Nat := 4983230072969 + 3 ^ 40 * 4182556 * 2
def baseEnd_4182556 : Nat := 2147661592346642964114781

theorem tailTrace_4182556 : CollatzResearch.WordTrace tailWord_4182556 prefixEnd_4182556 2147661592346642964114781 := by
  unfold tailWord_4182556
  simp only [CollatzResearch.WordTrace]
  refine ⟨76275174917660705269847761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101700233223547607026463681 76275174917660705269847761)
  ·
    refine ⟨57206381188245528952385821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76275174917660705269847761 57206381188245528952385821)
    ·
      refine ⟨21452392945592073357144683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57206381188245528952385821 21452392945592073357144683)
      ·
        refine ⟨32178589418388110035717025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21452392945592073357144683 32178589418388110035717025)
        ·
          refine ⟨24133942063791082526787769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32178589418388110035717025 24133942063791082526787769)
          ·
            refine ⟨18100456547843311895090827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24133942063791082526787769 18100456547843311895090827)
            ·
              refine ⟨27150684821764967842636241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18100456547843311895090827 27150684821764967842636241)
              ·
                refine ⟨20363013616323725881977181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27150684821764967842636241 20363013616323725881977181)
                ·
                  refine ⟨7636130106121397205741443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20363013616323725881977181 7636130106121397205741443)
                  ·
                    refine ⟨11454195159182095808612165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7636130106121397205741443 11454195159182095808612165)
                    ·
                      refine ⟨2147661592346642964114781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11454195159182095808612165 2147661592346642964114781)
                      ·
                        rfl

theorem cell23_4182556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_4182556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182556 prefixEnd_4182556 := by exact prefixLift 4182556
  have htrace : WordTrace (prefixWord ++ tailWord_4182556) baseStart_4182556 baseEnd_4182556 := by
    simpa [prefixWord, tailWord_4182556, baseEnd_4182556] using wordTrace_append hprefix tailTrace_4182556
  have hstable : (prefixWord ++ tailWord_4182556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182556).length < 2 ^ (prefixWord ++ tailWord_4182556).sum := by decide
  have hdescent : baseEnd_4182556 < baseStart_4182556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182559 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 5]
def baseStart_4182559 : Nat := 118140960795 + 4182559 * 2 ^ 59
def prefixEnd_4182559 : Nat := 4983230072969 + 3 ^ 40 * 4182559 * 2
def baseEnd_4182559 : Nat := 2147663132788606452377267

theorem tailTrace_4182559 : CollatzResearch.WordTrace tailWord_4182559 prefixEnd_4182559 2147663132788606452377267 := by
  unfold tailWord_4182559
  simp only [CollatzResearch.WordTrace]
  refine ⟨152550459254310542052054731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101700306169540361368036487 152550459254310542052054731)
  ·
    refine ⟨228825688881465813078082097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152550459254310542052054731 228825688881465813078082097)
    ·
      refine ⟨171619266661099359808561573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228825688881465813078082097 171619266661099359808561573)
      ·
        refine ⟨32178612498956129964105295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171619266661099359808561573 32178612498956129964105295)
        ·
          refine ⟨48267918748434194946157943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32178612498956129964105295 48267918748434194946157943)
          ·
            refine ⟨72401878122651292419236915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48267918748434194946157943 72401878122651292419236915)
            ·
              refine ⟨108602817183976938628855373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72401878122651292419236915 108602817183976938628855373)
              ·
                refine ⟨40726056443991351985820765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108602817183976938628855373 40726056443991351985820765)
                ·
                  refine ⟨15272271166496756994682787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40726056443991351985820765 15272271166496756994682787)
                  ·
                    refine ⟨22908406749745135492024181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15272271166496756994682787 22908406749745135492024181)
                    ·
                      refine ⟨2147663132788606452377267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22908406749745135492024181 2147663132788606452377267)
                      ·
                        rfl

theorem cell23_4182559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_4182559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182559 prefixEnd_4182559 := by exact prefixLift 4182559
  have htrace : WordTrace (prefixWord ++ tailWord_4182559) baseStart_4182559 baseEnd_4182559 := by
    simpa [prefixWord, tailWord_4182559, baseEnd_4182559] using wordTrace_append hprefix tailTrace_4182559
  have hstable : (prefixWord ++ tailWord_4182559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182559).length < 2 ^ (prefixWord ++ tailWord_4182559).sum := by decide
  have hdescent : baseEnd_4182559 < baseStart_4182559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182567 : List Nat := [1, 1, 7, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_4182567 : Nat := 118140960795 + 4182567 * 2 ^ 59
def prefixEnd_4182567 : Nat := 4983230072969 + 3 ^ 40 * 4182567 * 2
def baseEnd_4182567 : Nat := 2147667240633842421077231

theorem tailTrace_4182567 : CollatzResearch.WordTrace tailWord_4182567 prefixEnd_4182567 2147667240633842421077231 := by
  unfold tailWord_4182567
  simp only [CollatzResearch.WordTrace]
  refine ⟨152550751038281559418345955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101700500692187706278897303 152550751038281559418345955)
  ·
    refine ⟨228826126557422339127518933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152550751038281559418345955 228826126557422339127518933)
    ·
      refine ⟨5363112341189586073301225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 228826126557422339127518933 5363112341189586073301225)
      ·
        refine ⟨4022334255892189554975919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5363112341189586073301225 4022334255892189554975919)
        ·
          refine ⟨6033501383838284332463879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4022334255892189554975919 6033501383838284332463879)
          ·
            refine ⟨9050252075757426498695819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6033501383838284332463879 9050252075757426498695819)
            ·
              refine ⟨13575378113636139748043729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9050252075757426498695819 13575378113636139748043729)
              ·
                refine ⟨10181533585227104811032797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13575378113636139748043729 10181533585227104811032797)
                ·
                  refine ⟨3818075094460164304137299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10181533585227104811032797 3818075094460164304137299)
                  ·
                    refine ⟨5727112641690246456205949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3818075094460164304137299 5727112641690246456205949)
                    ·
                      refine ⟨2147667240633842421077231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5727112641690246456205949 2147667240633842421077231)
                      ·
                        rfl

theorem cell23_4182567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_4182567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182567 prefixEnd_4182567 := by exact prefixLift 4182567
  have htrace : WordTrace (prefixWord ++ tailWord_4182567) baseStart_4182567 baseEnd_4182567 := by
    simpa [prefixWord, tailWord_4182567, baseEnd_4182567] using wordTrace_append hprefix tailTrace_4182567
  have hstable : (prefixWord ++ tailWord_4182567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182567).length < 2 ^ (prefixWord ++ tailWord_4182567).sum := by decide
  have hdescent : baseEnd_4182567 < baseStart_4182567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182576 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 3]
def baseStart_4182576 : Nat := 118140960795 + 4182576 * 2 ^ 59
def prefixEnd_4182576 : Nat := 4983230072969 + 3 ^ 40 * 4182576 * 2
def baseEnd_4182576 : Nat := 2147671861959732885864689

theorem tailTrace_4182576 : CollatzResearch.WordTrace tailWord_4182576 prefixEnd_4182576 2147671861959732885864689 := by
  unfold tailWord_4182576
  simp only [CollatzResearch.WordTrace]
  refine ⟨76275539647624476977711791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101700719530165969303615721 76275539647624476977711791)
  ·
    refine ⟨114413309471436715466567687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76275539647624476977711791 114413309471436715466567687)
    ·
      refine ⟨171619964207155073199851531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114413309471436715466567687 171619964207155073199851531)
      ·
        refine ⟨257429946310732609799777297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171619964207155073199851531 257429946310732609799777297)
        ·
          refine ⟨193072459733049457349832973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257429946310732609799777297 193072459733049457349832973)
          ·
            refine ⟨72402172399893546506187365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193072459733049457349832973 72402172399893546506187365)
            ·
              refine ⟨13575407324980039969910131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72402172399893546506187365 13575407324980039969910131)
              ·
                refine ⟨20363110987470059954865197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13575407324980039969910131 20363110987470059954865197)
                ·
                  refine ⟨7636166620301272483074449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20363110987470059954865197 7636166620301272483074449)
                  ·
                    refine ⟨5727124965225954362305837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7636166620301272483074449 5727124965225954362305837)
                    ·
                      refine ⟨2147671861959732885864689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5727124965225954362305837 2147671861959732885864689)
                      ·
                        rfl

theorem cell23_4182576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 3].length) (baseStart_4182576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182576 prefixEnd_4182576 := by exact prefixLift 4182576
  have htrace : WordTrace (prefixWord ++ tailWord_4182576) baseStart_4182576 baseEnd_4182576 := by
    simpa [prefixWord, tailWord_4182576, baseEnd_4182576] using wordTrace_append hprefix tailTrace_4182576
  have hstable : (prefixWord ++ tailWord_4182576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182576).length < 2 ^ (prefixWord ++ tailWord_4182576).sum := by decide
  have hdescent : baseEnd_4182576 < baseStart_4182576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182586 : List Nat := [3, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4]
def baseStart_4182586 : Nat := 118140960795 + 4182586 * 2 ^ 59
def prefixEnd_4182586 : Nat := 4983230072969 + 3 ^ 40 * 4182586 * 2
def baseEnd_4182586 : Nat := 2147676996766277846739643

theorem tailTrace_4182586 : CollatzResearch.WordTrace tailWord_4182586 prefixEnd_4182586 2147676996766277846739643 := by
  unfold tailWord_4182586
  simp only [CollatzResearch.WordTrace]
  refine ⟨38137861006303181415821903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101700962683475150442191741 38137861006303181415821903)
  ·
    refine ⟨57206791509454772123732855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38137861006303181415821903 57206791509454772123732855)
    ·
      refine ⟨85810187264182158185599283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57206791509454772123732855 85810187264182158185599283)
      ·
        refine ⟨128715280896273237278398925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85810187264182158185599283 128715280896273237278398925)
        ·
          refine ⟨48268230336102463979399597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128715280896273237278398925 48268230336102463979399597)
          ·
            refine ⟨18100586376038423992274849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48268230336102463979399597 18100586376038423992274849)
            ·
              refine ⟨13575439782028817994206137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18100586376038423992274849 13575439782028817994206137)
              ·
                refine ⟨10181579836521613495654603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13575439782028817994206137 10181579836521613495654603)
                ·
                  refine ⟨15272369754782420243481905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10181579836521613495654603 15272369754782420243481905)
                  ·
                    refine ⟨11454277316086815182611429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15272369754782420243481905 11454277316086815182611429)
                    ·
                      refine ⟨2147676996766277846739643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11454277316086815182611429 2147676996766277846739643)
                      ·
                        rfl

theorem cell23_4182586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_4182586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182586 prefixEnd_4182586 := by exact prefixLift 4182586
  have htrace : WordTrace (prefixWord ++ tailWord_4182586) baseStart_4182586 baseEnd_4182586 := by
    simpa [prefixWord, tailWord_4182586, baseEnd_4182586] using wordTrace_append hprefix tailTrace_4182586
  have hstable : (prefixWord ++ tailWord_4182586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182586).length < 2 ^ (prefixWord ++ tailWord_4182586).sum := by decide
  have hdescent : baseEnd_4182586 < baseStart_4182586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182606 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3]
def baseStart_4182606 : Nat := 118140960795 + 4182606 * 2 ^ 59
def prefixEnd_4182606 : Nat := 4983230072969 + 3 ^ 40 * 4182606 * 2
def baseEnd_4182606 : Nat := 2147687266379367768489551

theorem tailTrace_4182606 : CollatzResearch.WordTrace tailWord_4182606 prefixEnd_4182606 2147687266379367768489551 := by
  unfold tailWord_4182606
  simp only [CollatzResearch.WordTrace]
  refine ⟨19069021685642533634876959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101701448990093512719343781 19069021685642533634876959)
  ·
    refine ⟨28603532528463800452315439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19069021685642533634876959 28603532528463800452315439)
    ·
      refine ⟨42905298792695700678473159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28603532528463800452315439 42905298792695700678473159)
      ·
        refine ⟨64357948189043551017709739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42905298792695700678473159 64357948189043551017709739)
        ·
          refine ⟨96536922283565326526564609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64357948189043551017709739 96536922283565326526564609)
          ·
            refine ⟨72402691712673994894923457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96536922283565326526564609 72402691712673994894923457)
            ·
              refine ⟨54302018784505496171192593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72402691712673994894923457 54302018784505496171192593)
              ·
                refine ⟨40726514088379122128394445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54302018784505496171192593 40726514088379122128394445)
                ·
                  refine ⟨15272442783142170798147917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40726514088379122128394445 15272442783142170798147917)
                  ·
                    refine ⟨5727166043678314049305469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15272442783142170798147917 5727166043678314049305469)
                    ·
                      refine ⟨2147687266379367768489551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5727166043678314049305469 2147687266379367768489551)
                      ·
                        rfl

theorem cell23_4182606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_4182606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182606 prefixEnd_4182606 := by exact prefixLift 4182606
  have htrace : WordTrace (prefixWord ++ tailWord_4182606) baseStart_4182606 baseEnd_4182606 := by
    simpa [prefixWord, tailWord_4182606, baseEnd_4182606] using wordTrace_append hprefix tailTrace_4182606
  have hstable : (prefixWord ++ tailWord_4182606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182606).length < 2 ^ (prefixWord ++ tailWord_4182606).sum := by decide
  have hdescent : baseEnd_4182606 < baseStart_4182606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182620 : List Nat := [2, 2, 4, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_4182620 : Nat := 118140960795 + 4182620 * 2 ^ 59
def prefixEnd_4182620 : Nat := 4983230072969 + 3 ^ 40 * 4182620 * 2
def baseEnd_4182620 : Nat := 2147694455108530713714487

theorem tailTrace_4182620 : CollatzResearch.WordTrace tailWord_4182620 prefixEnd_4182620 2147694455108530713714487 := by
  unfold tailWord_4182620
  simp only [CollatzResearch.WordTrace]
  refine ⟨76276342053544774735012657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101701789404726366313350209 76276342053544774735012657)
  ·
    refine ⟨57207256540158581051259493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76276342053544774735012657 57207256540158581051259493)
    ·
      refine ⟨10726360601279733947111155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57207256540158581051259493 10726360601279733947111155)
      ·
        refine ⟨16089540901919600920666733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10726360601279733947111155 16089540901919600920666733)
        ·
          refine ⟨6033577838219850345250025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16089540901919600920666733 6033577838219850345250025)
          ·
            refine ⟨4525183378664887758937519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6033577838219850345250025 4525183378664887758937519)
            ·
              refine ⟨6787775067997331638406279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4525183378664887758937519 6787775067997331638406279)
              ·
                refine ⟨10181662601995997457609419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6787775067997331638406279 10181662601995997457609419)
                ·
                  refine ⟨15272493902993996186414129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10181662601995997457609419 15272493902993996186414129)
                  ·
                    refine ⟨11454370427245497139810597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15272493902993996186414129 11454370427245497139810597)
                    ·
                      refine ⟨2147694455108530713714487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11454370427245497139810597 2147694455108530713714487)
                      ·
                        rfl

theorem cell23_4182620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_4182620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182620 prefixEnd_4182620 := by exact prefixLift 4182620
  have htrace : WordTrace (prefixWord ++ tailWord_4182620) baseStart_4182620 baseEnd_4182620 := by
    simpa [prefixWord, tailWord_4182620, baseEnd_4182620] using wordTrace_append hprefix tailTrace_4182620
  have hstable : (prefixWord ++ tailWord_4182620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182620).length < 2 ^ (prefixWord ++ tailWord_4182620).sum := by decide
  have hdescent : baseEnd_4182620 < baseStart_4182620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182623 : List Nat := [1, 1, 2, 3, 1, 1, 1, 7, 2, 1, 3]
def baseStart_4182623 : Nat := 118140960795 + 4182623 * 2 ^ 59
def prefixEnd_4182623 : Nat := 4983230072969 + 3 ^ 40 * 4182623 * 2
def baseEnd_4182623 : Nat := 2147695995550494201976973

theorem tailTrace_4182623 : CollatzResearch.WordTrace tailWord_4182623 prefixEnd_4182623 2147695995550494201976973 := by
  unfold tailWord_4182623
  simp only [CollatzResearch.WordTrace]
  refine ⟨152552793526078680982384523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101701862350719120654923015 152552793526078680982384523)
  ·
    refine ⟨228829190289118021473576785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152552793526078680982384523 228829190289118021473576785)
    ·
      refine ⟨171621892716838516105182589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228829190289118021473576785 171621892716838516105182589)
      ·
        refine ⟨64358209768814443539443471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171621892716838516105182589 64358209768814443539443471)
        ·
          refine ⟨96537314653221665309165207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64358209768814443539443471 96537314653221665309165207)
          ·
            refine ⟨144805971979832497963747811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96537314653221665309165207 144805971979832497963747811)
            ·
              refine ⟨217208957969748746945621717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144805971979832497963747811 217208957969748746945621717)
              ·
                refine ⟨5090834952415986256538009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 217208957969748746945621717 5090834952415986256538009)
                ·
                  refine ⟨3818126214311989692403507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5090834952415986256538009 3818126214311989692403507)
                  ·
                    refine ⟨5727189321467984538605261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3818126214311989692403507 5727189321467984538605261)
                    ·
                      refine ⟨2147695995550494201976973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5727189321467984538605261 2147695995550494201976973)
                      ·
                        rfl

theorem cell23_4182623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_4182623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182623 prefixEnd_4182623 := by exact prefixLift 4182623
  have htrace : WordTrace (prefixWord ++ tailWord_4182623) baseStart_4182623 baseEnd_4182623 := by
    simpa [prefixWord, tailWord_4182623, baseEnd_4182623] using wordTrace_append hprefix tailTrace_4182623
  have hstable : (prefixWord ++ tailWord_4182623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182623).length < 2 ^ (prefixWord ++ tailWord_4182623).sum := by decide
  have hdescent : baseEnd_4182623 < baseStart_4182623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182639 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 1, 8]
def baseStart_4182639 : Nat := 118140960795 + 4182639 * 2 ^ 59
def prefixEnd_4182639 : Nat := 4983230072969 + 3 ^ 40 * 4182639 * 2
def baseEnd_4182639 : Nat := 715901403746988713125633

theorem tailTrace_4182639 : CollatzResearch.WordTrace tailWord_4182639 prefixEnd_4182639 715901403746988713125633 := by
  unfold tailWord_4182639
  simp only [CollatzResearch.WordTrace]
  refine ⟨152553377094020715714966971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101702251396013810476644647 152553377094020715714966971)
  ·
    refine ⟨228830065641031073572450457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152553377094020715714966971 228830065641031073572450457)
    ·
      refine ⟨171622549230773305179337843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228830065641031073572450457 171622549230773305179337843)
      ·
        refine ⟨257433823846159957769006765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171622549230773305179337843 257433823846159957769006765)
        ·
          refine ⟨96537683942309984163377537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257433823846159957769006765 96537683942309984163377537)
          ·
            refine ⟨72403262956732488122533153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96537683942309984163377537 72403262956732488122533153)
            ·
              refine ⟨54302447217549366091899865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72403262956732488122533153 54302447217549366091899865)
              ·
                refine ⟨40726835413162024568924899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54302447217549366091899865 40726835413162024568924899)
                ·
                  refine ⟨61090253119743036853387349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40726835413162024568924899 61090253119743036853387349)
                  ·
                    refine ⟨715901403746988713125633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61090253119743036853387349 715901403746988713125633)
                    ·
                      rfl

theorem cell23_4182639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 8].length) (baseStart_4182639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182639 prefixEnd_4182639 := by exact prefixLift 4182639
  have htrace : WordTrace (prefixWord ++ tailWord_4182639) baseStart_4182639 baseEnd_4182639 := by
    simpa [prefixWord, tailWord_4182639, baseEnd_4182639] using wordTrace_append hprefix tailTrace_4182639
  have hstable : (prefixWord ++ tailWord_4182639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182639).length < 2 ^ (prefixWord ++ tailWord_4182639).sum := by decide
  have hdescent : baseEnd_4182639 < baseStart_4182639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182658 : List Nat := [3, 4, 3, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_4182658 : Nat := 118140960795 + 4182658 * 2 ^ 59
def prefixEnd_4182658 : Nat := 4983230072969 + 3 ^ 40 * 4182658 * 2
def baseEnd_4182658 : Nat := 2147713967373401565039313

theorem tailTrace_4182658 : CollatzResearch.WordTrace tailWord_4182658 prefixEnd_4182658 2147713967373401565039313 := by
  unfold tailWord_4182658
  simp only [CollatzResearch.WordTrace]
  refine ⟨38138517520237970489977157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101702713387301254639939085 38138517520237970489977157)
  ·
    refine ⟨7150972035044619466870717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38138517520237970489977157 7150972035044619466870717)
    ·
      refine ⟨2681614513141732300076519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7150972035044619466870717 2681614513141732300076519)
      ·
        refine ⟨4022421769712598450114779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2681614513141732300076519 4022421769712598450114779)
        ·
          refine ⟨6033632654568897675172169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4022421769712598450114779 6033632654568897675172169)
          ·
            refine ⟨4525224490926673256379127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6033632654568897675172169 4525224490926673256379127)
            ·
              refine ⟨6787836736390009884568691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4525224490926673256379127 6787836736390009884568691)
              ·
                refine ⟨10181755104585014826853037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6787836736390009884568691 10181755104585014826853037)
                ·
                  refine ⟨3818158164219380560069889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10181755104585014826853037 3818158164219380560069889)
                  ·
                    refine ⟨2863618623164535420052417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3818158164219380560069889 2863618623164535420052417)
                    ·
                      refine ⟨2147713967373401565039313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2863618623164535420052417 2147713967373401565039313)
                      ·
                        rfl

theorem cell23_4182658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_4182658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182658 prefixEnd_4182658 := by exact prefixLift 4182658
  have htrace : WordTrace (prefixWord ++ tailWord_4182658) baseStart_4182658 baseEnd_4182658 := by
    simpa [prefixWord, tailWord_4182658, baseEnd_4182658] using wordTrace_append hprefix tailTrace_4182658
  have hstable : (prefixWord ++ tailWord_4182658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182658).length < 2 ^ (prefixWord ++ tailWord_4182658).sum := by decide
  have hdescent : baseEnd_4182658 < baseStart_4182658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182674 : List Nat := [3, 2, 3, 1, 2, 3, 2, 1, 2, 1, 3]
def baseStart_4182674 : Nat := 118140960795 + 4182674 * 2 ^ 59
def prefixEnd_4182674 : Nat := 4983230072969 + 3 ^ 40 * 4182674 * 2
def baseEnd_4182674 : Nat := 2147722183063873502439239

theorem tailTrace_4182674 : CollatzResearch.WordTrace tailWord_4182674 prefixEnd_4182674 2147722183063873502439239 := by
  unfold tailWord_4182674
  simp only [CollatzResearch.WordTrace]
  refine ⟨38138663412223479173122769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101703102432595944461660717 38138663412223479173122769)
  ·
    refine ⟨28603997559167609379842077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38138663412223479173122769 28603997559167609379842077)
    ·
      refine ⟨10726499084687853517440779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28603997559167609379842077 10726499084687853517440779)
      ·
        refine ⟨16089748627031780276161169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10726499084687853517440779 16089748627031780276161169)
        ·
          refine ⟨12067311470273835207120877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16089748627031780276161169 12067311470273835207120877)
          ·
            refine ⟨4525241801352688202670329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12067311470273835207120877 4525241801352688202670329)
            ·
              refine ⟨3393931351014516152002747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4525241801352688202670329 3393931351014516152002747)
              ·
                refine ⟨5090897026521774228004121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3393931351014516152002747 5090897026521774228004121)
                ·
                  refine ⟨3818172769891330671003091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5090897026521774228004121 3818172769891330671003091)
                  ·
                    refine ⟨5727259154836996006504637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3818172769891330671003091 5727259154836996006504637)
                    ·
                      refine ⟨2147722183063873502439239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5727259154836996006504637 2147722183063873502439239)
                      ·
                        rfl

theorem cell23_4182674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_4182674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182674 prefixEnd_4182674 := by exact prefixLift 4182674
  have htrace : WordTrace (prefixWord ++ tailWord_4182674) baseStart_4182674 baseEnd_4182674 := by
    simpa [prefixWord, tailWord_4182674, baseEnd_4182674] using wordTrace_append hprefix tailTrace_4182674
  have hstable : (prefixWord ++ tailWord_4182674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182674).length < 2 ^ (prefixWord ++ tailWord_4182674).sum := by decide
  have hdescent : baseEnd_4182674 < baseStart_4182674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182720 : List Nat := [2, 1, 1, 2, 4, 2, 4, 2, 5]
def baseStart_4182720 : Nat := 118140960795 + 4182720 * 2 ^ 59
def prefixEnd_4182720 : Nat := 4983230072969 + 3 ^ 40 * 4182720 * 2
def baseEnd_4182720 : Nat := 238638422574886702496003

theorem tailTrace_4182720 : CollatzResearch.WordTrace tailWord_4182720 prefixEnd_4182720 238638422574886702496003 := by
  unfold tailWord_4182720
  simp only [CollatzResearch.WordTrace]
  refine ⟨76278165703363633274332807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101704220937818177699110409 76278165703363633274332807)
  ·
    refine ⟨114417248555045449911499211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76278165703363633274332807 114417248555045449911499211)
    ·
      refine ⟨171625872832568174867248817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114417248555045449911499211 171625872832568174867248817)
      ·
        refine ⟨128719404624426131150436613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171625872832568174867248817 128719404624426131150436613)
        ·
          refine ⟨24134888367079899590706865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128719404624426131150436613 24134888367079899590706865)
          ·
            refine ⟨18101166275309924693030149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24134888367079899590706865 18101166275309924693030149)
            ·
              refine ⟨3393968676620610879943153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18101166275309924693030149 3393968676620610879943153)
              ·
                refine ⟨2545476507465458159957365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3393968676620610879943153 2545476507465458159957365)
                ·
                  refine ⟨238638422574886702496003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2545476507465458159957365 238638422574886702496003)
                  ·
                    rfl

theorem cell23_4182720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 5].length) (baseStart_4182720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182720 prefixEnd_4182720 := by exact prefixLift 4182720
  have htrace : WordTrace (prefixWord ++ tailWord_4182720) baseStart_4182720 baseEnd_4182720 := by
    simpa [prefixWord, tailWord_4182720, baseEnd_4182720] using wordTrace_append hprefix tailTrace_4182720
  have hstable : (prefixWord ++ tailWord_4182720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182720).length < 2 ^ (prefixWord ++ tailWord_4182720).sum := by decide
  have hdescent : baseEnd_4182720 < baseStart_4182720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182753 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 1, 3, 4]
def baseStart_4182753 : Nat := 118140960795 + 4182753 * 2 ^ 59
def prefixEnd_4182753 : Nat := 4983230072969 + 3 ^ 40 * 4182753 * 2
def baseEnd_4182753 : Nat := 2147762748035578693351375

theorem tailTrace_4182753 : CollatzResearch.WordTrace tailWord_4182753 prefixEnd_4182753 2147762748035578693351375 := by
  unfold tailWord_4182753
  simp only [CollatzResearch.WordTrace]
  refine ⟨152557535015607713184616913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101705023343738475456411275 152557535015607713184616913)
  ·
    refine ⟨114418151261705784888462685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152557535015607713184616913 114418151261705784888462685)
    ·
      refine ⟨42906806723139669333173507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114418151261705784888462685 42906806723139669333173507)
      ·
        refine ⟨64360210084709503999760261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42906806723139669333173507 64360210084709503999760261)
        ·
          refine ⟨12067539390883031999955049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64360210084709503999760261 12067539390883031999955049)
          ·
            refine ⟨9050654543162273999966287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12067539390883031999955049 9050654543162273999966287)
            ·
              refine ⟨13575981814743410999949431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9050654543162273999966287 13575981814743410999949431)
              ·
                refine ⟨20363972722115116499924147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13575981814743410999949431 20363972722115116499924147)
                ·
                  refine ⟨30545959083172674749886221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20363972722115116499924147 30545959083172674749886221)
                  ·
                    refine ⟨11454734656189753031207333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30545959083172674749886221 11454734656189753031207333)
                    ·
                      refine ⟨2147762748035578693351375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11454734656189753031207333 2147762748035578693351375)
                      ·
                        rfl

theorem cell23_4182753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_4182753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182753 prefixEnd_4182753 := by exact prefixLift 4182753
  have htrace : WordTrace (prefixWord ++ tailWord_4182753) baseStart_4182753 baseEnd_4182753 := by
    simpa [prefixWord, tailWord_4182753, baseEnd_4182753] using wordTrace_append hprefix tailTrace_4182753
  have hstable : (prefixWord ++ tailWord_4182753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182753).length < 2 ^ (prefixWord ++ tailWord_4182753).sum := by decide
  have hdescent : baseEnd_4182753 < baseStart_4182753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182770 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 2, 4, 2]
def baseStart_4182770 : Nat := 118140960795 + 4182770 * 2 ^ 59
def prefixEnd_4182770 : Nat := 4983230072969 + 3 ^ 40 * 4182770 * 2
def baseEnd_4182770 : Nat := 2147771477206705126838797

theorem tailTrace_4182770 : CollatzResearch.WordTrace tailWord_4182770 prefixEnd_4182770 2147771477206705126838797 := by
  unfold tailWord_4182770
  simp only [CollatzResearch.WordTrace]
  refine ⟨38139538764136531271996441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101705436704364083391990509 38139538764136531271996441)
  ·
    refine ⟨28604654073102398453997331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38139538764136531271996441 28604654073102398453997331)
    ·
      refine ⟨42906981109653597680995997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28604654073102398453997331 42906981109653597680995997)
      ·
        refine ⟨16090117916120099130373499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42906981109653597680995997 16090117916120099130373499)
        ·
          refine ⟨24135176874180148695560249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16090117916120099130373499 24135176874180148695560249)
          ·
            refine ⟨18101382655635111521670187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24135176874180148695560249 18101382655635111521670187)
            ·
              refine ⟨27152073983452667282505281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18101382655635111521670187 27152073983452667282505281)
              ·
                refine ⟨20364055487589500461878961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27152073983452667282505281 20364055487589500461878961)
                ·
                  refine ⟨15273041615692125346409221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20364055487589500461878961 15273041615692125346409221)
                  ·
                    refine ⟨2863695302942273502451729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15273041615692125346409221 2863695302942273502451729)
                    ·
                      refine ⟨2147771477206705126838797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2863695302942273502451729 2147771477206705126838797)
                      ·
                        rfl

theorem cell23_4182770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_4182770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182770 prefixEnd_4182770 := by exact prefixLift 4182770
  have htrace : WordTrace (prefixWord ++ tailWord_4182770) baseStart_4182770 baseEnd_4182770 := by
    simpa [prefixWord, tailWord_4182770, baseEnd_4182770] using wordTrace_append hprefix tailTrace_4182770
  have hstable : (prefixWord ++ tailWord_4182770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182770).length < 2 ^ (prefixWord ++ tailWord_4182770).sum := by decide
  have hdescent : baseEnd_4182770 < baseStart_4182770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182776 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 8]
def baseStart_4182776 : Nat := 118140960795 + 4182776 * 2 ^ 59
def prefixEnd_4182776 : Nat := 4983230072969 + 3 ^ 40 * 4182776 * 2
def baseEnd_4182776 : Nat := 238641617565625789262641

theorem tailTrace_4182776 : CollatzResearch.WordTrace tailWord_4182776 prefixEnd_4182776 238641617565625789262641 := by
  unfold tailWord_4182776
  simp only [CollatzResearch.WordTrace]
  refine ⟨76279186947262194056352091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101705582596349592075136121 76279186947262194056352091)
  ·
    refine ⟨114418780420893291084528137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76279186947262194056352091 114418780420893291084528137)
    ·
      refine ⟨85814085315669968313396103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114418780420893291084528137 85814085315669968313396103)
      ·
        refine ⟨128721127973504952470094155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85814085315669968313396103 128721127973504952470094155)
        ·
          refine ⟨193081691960257428705141233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128721127973504952470094155 193081691960257428705141233)
          ·
            refine ⟨144811268970193071528855925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193081691960257428705141233 144811268970193071528855925)
            ·
              refine ⟨13576056465955600455830243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144811268970193071528855925 13576056465955600455830243)
              ·
                refine ⟨20364084698933400683745365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13576056465955600455830243 20364084698933400683745365)
                ·
                  refine ⟨238641617565625789262641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20364084698933400683745365 238641617565625789262641)
                  ·
                    rfl

theorem cell23_4182776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 8].length) (baseStart_4182776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182776 prefixEnd_4182776 := by exact prefixLift 4182776
  have htrace : WordTrace (prefixWord ++ tailWord_4182776) baseStart_4182776 baseEnd_4182776 := by
    simpa [prefixWord, tailWord_4182776, baseEnd_4182776] using wordTrace_append hprefix tailTrace_4182776
  have hstable : (prefixWord ++ tailWord_4182776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182776).length < 2 ^ (prefixWord ++ tailWord_4182776).sum := by decide
  have hdescent : baseEnd_4182776 < baseStart_4182776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182780 : List Nat := [2, 2, 2, 1, 3, 3, 2, 1, 3, 4]
def baseStart_4182780 : Nat := 118140960795 + 4182780 * 2 ^ 59
def prefixEnd_4182780 : Nat := 4983230072969 + 3 ^ 40 * 4182780 * 2
def baseEnd_4182780 : Nat := 715925537337750029237917

theorem tailTrace_4182780 : CollatzResearch.WordTrace tailWord_4182780 prefixEnd_4182780 715925537337750029237917 := by
  unfold tailWord_4182780
  simp only [CollatzResearch.WordTrace]
  refine ⟨76279259893254948397924897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101705679857673264530566529 76279259893254948397924897)
  ·
    refine ⟨57209444919941211298443673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76279259893254948397924897 57209444919941211298443673)
    ·
      refine ⟨42907083689955908473832755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57209444919941211298443673 42907083689955908473832755)
      ·
        refine ⟨64360625534933862710749133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42907083689955908473832755 64360625534933862710749133)
        ·
          refine ⟨24135234575600198516530925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64360625534933862710749133 24135234575600198516530925)
          ·
            refine ⟨9050712965850074443699097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24135234575600198516530925 9050712965850074443699097)
            ·
              refine ⟨6788034724387555832774323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9050712965850074443699097 6788034724387555832774323)
              ·
                refine ⟨10182052086581333749161485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6788034724387555832774323 10182052086581333749161485)
                ·
                  refine ⟨3818269532468000155935557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10182052086581333749161485 3818269532468000155935557)
                  ·
                    refine ⟨715925537337750029237917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3818269532468000155935557 715925537337750029237917)
                    ·
                      rfl

theorem cell23_4182780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_4182780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182780 prefixEnd_4182780 := by exact prefixLift 4182780
  have htrace : WordTrace (prefixWord ++ tailWord_4182780) baseStart_4182780 baseEnd_4182780 := by
    simpa [prefixWord, tailWord_4182780, baseEnd_4182780] using wordTrace_append hprefix tailTrace_4182780
  have hstable : (prefixWord ++ tailWord_4182780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182780).length < 2 ^ (prefixWord ++ tailWord_4182780).sum := by decide
  have hdescent : baseEnd_4182780 < baseStart_4182780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182796 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 3, 2, 6]
def baseStart_4182796 : Nat := 118140960795 + 4182796 * 2 ^ 59
def prefixEnd_4182796 : Nat := 4983230072969 + 3 ^ 40 * 4182796 * 2
def baseEnd_4182796 : Nat := 2147784827703722025113677

theorem tailTrace_4182796 : CollatzResearch.WordTrace tailWord_4182796 prefixEnd_4182796 2147784827703722025113677 := by
  unfold tailWord_4182796
  simp only [CollatzResearch.WordTrace]
  refine ⟨76279551677225965764216121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101706068902967954352288161 76279551677225965764216121)
  ·
    refine ⟨57209663757919474323162091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76279551677225965764216121 57209663757919474323162091)
    ·
      refine ⟨85814495636879211484743137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57209663757919474323162091 85814495636879211484743137)
      ·
        refine ⟨64360871727659408613557353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85814495636879211484743137 64360871727659408613557353)
        ·
          refine ⟨48270653795744556460168015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64360871727659408613557353 48270653795744556460168015)
          ·
            refine ⟨72405980693616834690252023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48270653795744556460168015 72405980693616834690252023)
            ·
              refine ⟨108608971040425252035378035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72405980693616834690252023 108608971040425252035378035)
              ·
                refine ⟨162913456560637878053067053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108608971040425252035378035 162913456560637878053067053)
                ·
                  refine ⟨61092546210239204269900145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162913456560637878053067053 61092546210239204269900145)
                  ·
                    refine ⟨45819409657679403202425109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61092546210239204269900145 45819409657679403202425109)
                    ·
                      refine ⟨2147784827703722025113677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45819409657679403202425109 2147784827703722025113677)
                      ·
                        rfl

theorem cell23_4182796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_4182796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182796 prefixEnd_4182796 := by exact prefixLift 4182796
  have htrace : WordTrace (prefixWord ++ tailWord_4182796) baseStart_4182796 baseEnd_4182796 := by
    simpa [prefixWord, tailWord_4182796, baseEnd_4182796] using wordTrace_append hprefix tailTrace_4182796
  have hstable : (prefixWord ++ tailWord_4182796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182796).length < 2 ^ (prefixWord ++ tailWord_4182796).sum := by decide
  have hdescent : baseEnd_4182796 < baseStart_4182796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182837 : List Nat := [1, 3, 3, 1, 3, 1, 3, 1, 3, 1, 3]
def baseStart_4182837 : Nat := 118140960795 + 4182837 * 2 ^ 59
def prefixEnd_4182837 : Nat := 4983230072969 + 3 ^ 40 * 4182837 * 2
def baseEnd_4182837 : Nat := 2147805880410556364700989

theorem tailTrace_4182837 : CollatzResearch.WordTrace tailWord_4182837 prefixEnd_4182837 2147805880410556364700989 := by
  unfold tailWord_4182837
  simp only [CollatzResearch.WordTrace]
  refine ⟨152560598747303395530674765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101707065831535597020449843 152560598747303395530674765)
  ·
    refine ⟨57210224530238773324003037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152560598747303395530674765 57210224530238773324003037)
    ·
      refine ⟨21453834198839539996501139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57210224530238773324003037 21453834198839539996501139)
      ·
        refine ⟨32180751298259309994751709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21453834198839539996501139 32180751298259309994751709)
        ·
          refine ⟨12067781736847241248031891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32180751298259309994751709 12067781736847241248031891)
          ·
            refine ⟨18101672605270861872047837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12067781736847241248031891 18101672605270861872047837)
            ·
              refine ⟨6788127226976573202017939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18101672605270861872047837 6788127226976573202017939)
              ·
                refine ⟨10182190840464859803026909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6788127226976573202017939 10182190840464859803026909)
                ·
                  refine ⟨3818321565174322426135091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10182190840464859803026909 3818321565174322426135091)
                  ·
                    refine ⟨5727482347761483639202637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3818321565174322426135091 5727482347761483639202637)
                    ·
                      refine ⟨2147805880410556364700989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5727482347761483639202637 2147805880410556364700989)
                      ·
                        rfl

theorem cell23_4182837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_4182837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182837 prefixEnd_4182837 := by exact prefixLift 4182837
  have htrace : WordTrace (prefixWord ++ tailWord_4182837) baseStart_4182837 baseEnd_4182837 := by
    simpa [prefixWord, tailWord_4182837, baseEnd_4182837] using wordTrace_append hprefix tailTrace_4182837
  have hstable : (prefixWord ++ tailWord_4182837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182837).length < 2 ^ (prefixWord ++ tailWord_4182837).sum := by decide
  have hdescent : baseEnd_4182837 < baseStart_4182837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182853 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 6, 4]
def baseStart_4182853 : Nat := 118140960795 + 4182853 * 2 ^ 59
def prefixEnd_4182853 : Nat := 4983230072969 + 3 ^ 40 * 4182853 * 2
def baseEnd_4182853 : Nat := 715938032033676100700305

theorem tailTrace_4182853 : CollatzResearch.WordTrace tailWord_4182853 prefixEnd_4182853 715938032033676100700305 := by
  unfold tailWord_4182853
  simp only [CollatzResearch.WordTrace]
  refine ⟨152561182315245430263257213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101707454876830286842171475 152561182315245430263257213)
  ·
    refine ⟨57210443368217036348721455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152561182315245430263257213 57210443368217036348721455)
    ·
      refine ⟨85815665052325554523082183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57210443368217036348721455 85815665052325554523082183)
      ·
        refine ⟨128723497578488331784623275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85815665052325554523082183 128723497578488331784623275)
        ·
          refine ⟨193085246367732497676934913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128723497578488331784623275 193085246367732497676934913)
          ·
            refine ⟨144813934775799373257701185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193085246367732497676934913 144813934775799373257701185)
            ·
              refine ⟨108610451081849529943275889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144813934775799373257701185 108610451081849529943275889)
              ·
                refine ⟨81457838311387147457456917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108610451081849529943275889 81457838311387147457456917)
                ·
                  refine ⟨3818336170846272537068293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81457838311387147457456917 3818336170846272537068293)
                  ·
                    refine ⟨715938032033676100700305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3818336170846272537068293 715938032033676100700305)
                    ·
                      rfl

theorem cell23_4182853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 4].length) (baseStart_4182853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182853 prefixEnd_4182853 := by exact prefixLift 4182853
  have htrace : WordTrace (prefixWord ++ tailWord_4182853) baseStart_4182853 baseEnd_4182853 := by
    simpa [prefixWord, tailWord_4182853, baseEnd_4182853] using wordTrace_append hprefix tailTrace_4182853
  have hstable : (prefixWord ++ tailWord_4182853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182853).length < 2 ^ (prefixWord ++ tailWord_4182853).sum := by decide
  have hdescent : baseEnd_4182853 < baseStart_4182853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182860 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 3, 1, 4]
def baseStart_4182860 : Nat := 118140960795 + 4182860 * 2 ^ 59
def prefixEnd_4182860 : Nat := 4983230072969 + 3 ^ 40 * 4182860 * 2
def baseEnd_4182860 : Nat := 2147817690465609774713383

theorem tailTrace_4182860 : CollatzResearch.WordTrace tailWord_4182860 prefixEnd_4182860 2147817690465609774713383 := by
  unfold tailWord_4182860
  simp only [CollatzResearch.WordTrace]
  refine ⟨76280718813110035229381017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101707625084146713639174689 76280718813110035229381017)
  ·
    refine ⟨57210539109832526422035763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76280718813110035229381017 57210539109832526422035763)
    ·
      refine ⟨85815808664748789633053645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57210539109832526422035763 85815808664748789633053645)
      ·
        refine ⟨32180928249280796112395117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85815808664748789633053645 32180928249280796112395117)
        ·
          refine ⟨12067848093480298542148169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32180928249280796112395117 12067848093480298542148169)
          ·
            refine ⟨9050886070110223906611127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12067848093480298542148169 9050886070110223906611127)
            ·
              refine ⟨13576329105165335859916691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9050886070110223906611127 13576329105165335859916691)
              ·
                refine ⟨20364493657748003789875037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13576329105165335859916691 20364493657748003789875037)
                ·
                  refine ⟨7636685121655501421203139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20364493657748003789875037 7636685121655501421203139)
                  ·
                    refine ⟨11455027682483252131804709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7636685121655501421203139 11455027682483252131804709)
                    ·
                      refine ⟨2147817690465609774713383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11455027682483252131804709 2147817690465609774713383)
                      ·
                        rfl

theorem cell23_4182860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_4182860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182860 prefixEnd_4182860 := by exact prefixLift 4182860
  have htrace : WordTrace (prefixWord ++ tailWord_4182860) baseStart_4182860 baseEnd_4182860 := by
    simpa [prefixWord, tailWord_4182860, baseEnd_4182860] using wordTrace_append hprefix tailTrace_4182860
  have hstable : (prefixWord ++ tailWord_4182860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182860).length < 2 ^ (prefixWord ++ tailWord_4182860).sum := by decide
  have hdescent : baseEnd_4182860 < baseStart_4182860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182873 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 3, 2, 4]
def baseStart_4182873 : Nat := 118140960795 + 4182873 * 2 ^ 59
def prefixEnd_4182873 : Nat := 4983230072969 + 3 ^ 40 * 4182873 * 2
def baseEnd_4182873 : Nat := 2147824365714118223850823

theorem tailTrace_4182873 : CollatzResearch.WordTrace tailWord_4182873 prefixEnd_4182873 2147824365714118223850823 := by
  unfold tailWord_4182873
  simp only [CollatzResearch.WordTrace]
  refine ⟨152561911775172973678985273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101707941183448649119323515 152561911775172973678985273)
  ·
    refine ⟨114421433831379730259238955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152561911775172973678985273 114421433831379730259238955)
    ·
      refine ⟨171632150747069595388858433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114421433831379730259238955 171632150747069595388858433)
      ·
        refine ⟨128724113060302196541643825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171632150747069595388858433 128724113060302196541643825)
        ·
          refine ⟨96543084795226647406232869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128724113060302196541643825 96543084795226647406232869)
          ·
            refine ⟨18101828399104996388668663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96543084795226647406232869 18101828399104996388668663)
            ·
              refine ⟨27152742598657494583002995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18101828399104996388668663 27152742598657494583002995)
              ·
                refine ⟨40729113897986241874504493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27152742598657494583002995 40729113897986241874504493)
                ·
                  refine ⟨15273417711744840702939185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40729113897986241874504493 15273417711744840702939185)
                  ·
                    refine ⟨11455063283808630527204389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15273417711744840702939185 11455063283808630527204389)
                    ·
                      refine ⟨2147824365714118223850823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11455063283808630527204389 2147824365714118223850823)
                      ·
                        rfl

theorem cell23_4182873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_4182873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182873 prefixEnd_4182873 := by exact prefixLift 4182873
  have htrace : WordTrace (prefixWord ++ tailWord_4182873) baseStart_4182873 baseEnd_4182873 := by
    simpa [prefixWord, tailWord_4182873, baseEnd_4182873] using wordTrace_append hprefix tailTrace_4182873
  have hstable : (prefixWord ++ tailWord_4182873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182873).length < 2 ^ (prefixWord ++ tailWord_4182873).sum := by decide
  have hdescent : baseEnd_4182873 < baseStart_4182873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182887 : List Nat := [1, 1, 5, 1, 2, 3, 2, 2, 2, 4]
def baseStart_4182887 : Nat := 118140960795 + 4182887 * 2 ^ 59
def prefixEnd_4182887 : Nat := 4983230072969 + 3 ^ 40 * 4182887 * 2
def baseEnd_4182887 : Nat := 715943851481093723025253

theorem tailTrace_4182887 : CollatzResearch.WordTrace tailWord_4182887 prefixEnd_4182887 715943851481093723025253 := by
  unfold tailWord_4182887
  simp only [CollatzResearch.WordTrace]
  refine ⟨152562422397122254069994915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101708281598081502713329943 152562422397122254069994915)
  ·
    refine ⟨228843633595683381104992373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152562422397122254069994915 228843633595683381104992373)
    ·
      refine ⟨21454090649595316978593035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228843633595683381104992373 21454090649595316978593035)
      ·
        refine ⟨32181135974392975467889553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21454090649595316978593035 32181135974392975467889553)
        ·
          refine ⟨24135851980794731600917165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32181135974392975467889553 24135851980794731600917165)
          ·
            refine ⟨9050944492798024350343937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24135851980794731600917165 9050944492798024350343937)
            ·
              refine ⟨6788208369598518262757953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9050944492798024350343937 6788208369598518262757953)
              ·
                refine ⟨5091156277198888697068465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6788208369598518262757953 5091156277198888697068465)
                ·
                  refine ⟨3818367207899166522801349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5091156277198888697068465 3818367207899166522801349)
                  ·
                    refine ⟨715943851481093723025253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3818367207899166522801349 715943851481093723025253)
                    ·
                      rfl

theorem cell23_4182887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_4182887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182887 prefixEnd_4182887 := by exact prefixLift 4182887
  have htrace : WordTrace (prefixWord ++ tailWord_4182887) baseStart_4182887 baseEnd_4182887 := by
    simpa [prefixWord, tailWord_4182887, baseEnd_4182887] using wordTrace_append hprefix tailTrace_4182887
  have hstable : (prefixWord ++ tailWord_4182887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182887).length < 2 ^ (prefixWord ++ tailWord_4182887).sum := by decide
  have hdescent : baseEnd_4182887 < baseStart_4182887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182961 : List Nat := [1, 2, 2, 4, 3, 1, 3, 1, 2, 1, 3]
def baseStart_4182961 : Nat := 118140960795 + 4182961 * 2 ^ 59
def prefixEnd_4182961 : Nat := 4983230072969 + 3 ^ 40 * 4182961 * 2
def baseEnd_4182961 : Nat := 2147869552011713879550419

theorem tailTrace_4182961 : CollatzResearch.WordTrace tailWord_4182961 prefixEnd_4182961 2147869552011713879550419 := by
  unfold tailWord_4182961
  simp only [CollatzResearch.WordTrace]
  refine ⟨152565121398854164708188737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101710080932569443138792491 152565121398854164708188737)
  ·
    refine ⟨114423841049140623531141553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152565121398854164708188737 114423841049140623531141553)
    ·
      refine ⟨85817880786855467648356165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114423841049140623531141553 85817880786855467648356165)
      ·
        refine ⟨16090852647535400184066781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85817880786855467648356165 16090852647535400184066781)
        ·
          refine ⟨6034069742825775069025043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16090852647535400184066781 6034069742825775069025043)
          ·
            refine ⟨9051104614238662603537565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6034069742825775069025043 9051104614238662603537565)
            ·
              refine ⟨3394164230339498476326587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9051104614238662603537565 3394164230339498476326587)
              ·
                refine ⟨5091246345509247714489881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3394164230339498476326587 5091246345509247714489881)
                ·
                  refine ⟨3818434759131935785867411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5091246345509247714489881 3818434759131935785867411)
                  ·
                    refine ⟨5727652138697903678801117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3818434759131935785867411 5727652138697903678801117)
                    ·
                      refine ⟨2147869552011713879550419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5727652138697903678801117 2147869552011713879550419)
                      ·
                        rfl

theorem cell23_4182961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_4182961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182961 prefixEnd_4182961 := by exact prefixLift 4182961
  have htrace : WordTrace (prefixWord ++ tailWord_4182961) baseStart_4182961 baseEnd_4182961 := by
    simpa [prefixWord, tailWord_4182961, baseEnd_4182961] using wordTrace_append hprefix tailTrace_4182961
  have hstable : (prefixWord ++ tailWord_4182961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182961).length < 2 ^ (prefixWord ++ tailWord_4182961).sum := by decide
  have hdescent : baseEnd_4182961 < baseStart_4182961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182963 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 4]
def baseStart_4182963 : Nat := 118140960795 + 4182963 * 2 ^ 59
def prefixEnd_4182963 : Nat := 4983230072969 + 3 ^ 40 * 4182963 * 2
def baseEnd_4182963 : Nat := 2147870578973022871725409

theorem tailTrace_4182963 : CollatzResearch.WordTrace tailWord_4182963 prefixEnd_4182963 2147870578973022871725409 := by
  unfold tailWord_4182963
  simp only [CollatzResearch.WordTrace]
  refine ⟨152565194344846919049761543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101710129563231279366507695 152565194344846919049761543)
  ·
    refine ⟨228847791517270378574642315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152565194344846919049761543 228847791517270378574642315)
    ·
      refine ⟨343271687275905567861963473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228847791517270378574642315 343271687275905567861963473)
      ·
        refine ⟨257453765456929175896472605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343271687275905567861963473 257453765456929175896472605)
        ·
          refine ⟨96545162046348440961177227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257453765456929175896472605 96545162046348440961177227)
          ·
            refine ⟨144817743069522661441765841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96545162046348440961177227 144817743069522661441765841)
            ·
              refine ⟨108613307302141996081324381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144817743069522661441765841 108613307302141996081324381)
              ·
                refine ⟨40729990238303248530496643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108613307302141996081324381 40729990238303248530496643)
                ·
                  refine ⟨61094985357454872795744965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40729990238303248530496643 61094985357454872795744965)
                  ·
                    refine ⟨11455309754522788649202181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61094985357454872795744965 11455309754522788649202181)
                    ·
                      refine ⟨2147870578973022871725409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11455309754522788649202181 2147870578973022871725409)
                      ·
                        rfl

theorem cell23_4182963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 4].length) (baseStart_4182963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182963 prefixEnd_4182963 := by exact prefixLift 4182963
  have htrace : WordTrace (prefixWord ++ tailWord_4182963) baseStart_4182963 baseEnd_4182963 := by
    simpa [prefixWord, tailWord_4182963, baseEnd_4182963] using wordTrace_append hprefix tailTrace_4182963
  have hstable : (prefixWord ++ tailWord_4182963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182963).length < 2 ^ (prefixWord ++ tailWord_4182963).sum := by decide
  have hdescent : baseEnd_4182963 < baseStart_4182963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182967 : List Nat := [1, 1, 3, 1, 3, 1, 5, 1, 1, 4, 2]
def baseStart_4182967 : Nat := 118140960795 + 4182967 * 2 ^ 59
def prefixEnd_4182967 : Nat := 4983230072969 + 3 ^ 40 * 4182967 * 2
def baseEnd_4182967 : Nat := 2147872632895640856075391

theorem tailTrace_4182967 : CollatzResearch.WordTrace tailWord_4182967 prefixEnd_4182967 2147872632895640856075391 := by
  unfold tailWord_4182967
  simp only [CollatzResearch.WordTrace]
  refine ⟨152565340236832427732907155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101710226824554951821938103 152565340236832427732907155)
  ·
    refine ⟨228848010355248641599360733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152565340236832427732907155 228848010355248641599360733)
    ·
      refine ⟨85818003883218240599760275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228848010355248641599360733 85818003883218240599760275)
      ·
        refine ⟨128727005824827360899640413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85818003883218240599760275 128727005824827360899640413)
        ·
          refine ⟨48272627184310260337365155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128727005824827360899640413 48272627184310260337365155)
          ·
            refine ⟨72408940776465390506047733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48272627184310260337365155 72408940776465390506047733)
            ·
              refine ⟨6788338197793630359941975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72408940776465390506047733 6788338197793630359941975)
              ·
                refine ⟨10182507296690445539912963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6788338197793630359941975 10182507296690445539912963)
                ·
                  refine ⟨15273760945035668309869445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10182507296690445539912963 15273760945035668309869445)
                  ·
                    refine ⟨2863830177194187808100521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15273760945035668309869445 2863830177194187808100521)
                    ·
                      refine ⟨2147872632895640856075391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2863830177194187808100521 2147872632895640856075391)
                      ·
                        rfl

theorem cell23_4182967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 4, 2].length) (baseStart_4182967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4182967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4182967 prefixEnd_4182967 := by exact prefixLift 4182967
  have htrace : WordTrace (prefixWord ++ tailWord_4182967) baseStart_4182967 baseEnd_4182967 := by
    simpa [prefixWord, tailWord_4182967, baseEnd_4182967] using wordTrace_append hprefix tailTrace_4182967
  have hstable : (prefixWord ++ tailWord_4182967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182967).length < 2 ^ (prefixWord ++ tailWord_4182967).sum := by decide
  have hdescent : baseEnd_4182967 < baseStart_4182967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183007 : List Nat := [1, 1, 2, 3, 5, 2, 1, 1, 7]
def baseStart_4183007 : Nat := 118140960795 + 4183007 * 2 ^ 59
def prefixEnd_4183007 : Nat := 4983230072969 + 3 ^ 40 * 4183007 * 2
def baseEnd_4183007 : Nat := 238654796902424522175023

theorem tailTrace_4183007 : CollatzResearch.WordTrace tailWord_4183007 prefixEnd_4183007 238654796902424522175023 := by
  unfold tailWord_4183007
  simp only [CollatzResearch.WordTrace]
  refine ⟨152566799156687514564363275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101711199437791676376242183 152566799156687514564363275)
  ·
    refine ⟨228850198735031271846544913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152566799156687514564363275 228850198735031271846544913)
    ·
      refine ⟨171637649051273453884908685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228850198735031271846544913 171637649051273453884908685)
      ·
        refine ⟨64364118394227545206840757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171637649051273453884908685 64364118394227545206840757)
        ·
          refine ⟨6034136099458832363141321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64364118394227545206840757 6034136099458832363141321)
          ·
            refine ⟨4525602074594124272355991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6034136099458832363141321 4525602074594124272355991)
            ·
              refine ⟨6788403111891186408533987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4525602074594124272355991 6788403111891186408533987)
              ·
                refine ⟨10182604667836779612800981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6788403111891186408533987 10182604667836779612800981)
                ·
                  refine ⟨238654796902424522175023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10182604667836779612800981 238654796902424522175023)
                  ·
                    rfl

theorem cell23_4183007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 7].length) (baseStart_4183007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183007 prefixEnd_4183007 := by exact prefixLift 4183007
  have htrace : WordTrace (prefixWord ++ tailWord_4183007) baseStart_4183007 baseEnd_4183007 := by
    simpa [prefixWord, tailWord_4183007, baseEnd_4183007] using wordTrace_append hprefix tailTrace_4183007
  have hstable : (prefixWord ++ tailWord_4183007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183007).length < 2 ^ (prefixWord ++ tailWord_4183007).sum := by decide
  have hdescent : baseEnd_4183007 < baseStart_4183007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183018 : List Nat := [3, 1, 3, 1, 2, 4, 2, 1, 2, 2, 2]
def baseStart_4183018 : Nat := 118140960795 + 4183018 * 2 ^ 59
def prefixEnd_4183018 : Nat := 4983230072969 + 3 ^ 40 * 4183018 * 2
def baseEnd_4183018 : Nat := 2147898820409020156537657

theorem tailTrace_4183018 : CollatzResearch.WordTrace tailWord_4183018 prefixEnd_4183018 2147898820409020156537657 := by
  unfold tailWord_4183018
  simp only [CollatzResearch.WordTrace]
  refine ⟨38141800089911915860753427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101711466906431775628675805 38141800089911915860753427)
  ·
    refine ⟨57212700134867873791130141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38141800089911915860753427 57212700134867873791130141)
    ·
      refine ⟨21454762550575452671673803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57212700134867873791130141 21454762550575452671673803)
      ·
        refine ⟨32182143825863179007510705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21454762550575452671673803 32182143825863179007510705)
        ·
          refine ⟨24136607869397384255633029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32182143825863179007510705 24136607869397384255633029)
          ·
            refine ⟨4525613975512009547931193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24136607869397384255633029 4525613975512009547931193)
            ·
              refine ⟨3394210481634007160948395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4525613975512009547931193 3394210481634007160948395)
              ·
                refine ⟨5091315722451010741422593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3394210481634007160948395 5091315722451010741422593)
                ·
                  refine ⟨3818486791838258056066945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5091315722451010741422593 3818486791838258056066945)
                  ·
                    refine ⟨2863865093878693542050209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3818486791838258056066945 2863865093878693542050209)
                    ·
                      refine ⟨2147898820409020156537657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2863865093878693542050209 2147898820409020156537657)
                      ·
                        rfl

theorem cell23_4183018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_4183018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183018 prefixEnd_4183018 := by exact prefixLift 4183018
  have htrace : WordTrace (prefixWord ++ tailWord_4183018) baseStart_4183018 baseEnd_4183018 := by
    simpa [prefixWord, tailWord_4183018, baseEnd_4183018] using wordTrace_append hprefix tailTrace_4183018
  have hstable : (prefixWord ++ tailWord_4183018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183018).length < 2 ^ (prefixWord ++ tailWord_4183018).sum := by decide
  have hdescent : baseEnd_4183018 < baseStart_4183018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183043 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 9]
def baseStart_4183043 : Nat := 118140960795 + 4183043 * 2 ^ 59
def prefixEnd_4183043 : Nat := 4983230072969 + 3 ^ 40 * 4183043 * 2
def baseEnd_4183043 : Nat := 2147911657425382558725041

theorem tailTrace_4183043 : CollatzResearch.WordTrace tailWord_4183043 prefixEnd_4183043 2147911657425382558725041 := by
  unfold tailWord_4183043
  simp only [CollatzResearch.WordTrace]
  refine ⟨152568112184557092712673783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101712074789704728475115855 152568112184557092712673783)
  ·
    refine ⟨228852168276835639069010675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152568112184557092712673783 228852168276835639069010675)
    ·
      refine ⟨343278252415253458603516013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228852168276835639069010675 343278252415253458603516013)
      ·
        refine ⟨128729344655720046976318505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343278252415253458603516013 128729344655720046976318505)
        ·
          refine ⟨96547008491790035232238879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128729344655720046976318505 96547008491790035232238879)
          ·
            refine ⟨144820512737685052848358319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96547008491790035232238879 144820512737685052848358319)
            ·
              refine ⟨217230769106527579272537479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144820512737685052848358319 217230769106527579272537479)
              ·
                refine ⟨325846153659791368908806219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217230769106527579272537479 325846153659791368908806219)
                ·
                  refine ⟨488769230489687053363209329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325846153659791368908806219 488769230489687053363209329)
                  ·
                    refine ⟨366576922867265290022406997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 488769230489687053363209329 366576922867265290022406997)
                    ·
                      refine ⟨2147911657425382558725041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 366576922867265290022406997 2147911657425382558725041)
                      ·
                        rfl

theorem cell23_4183043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_4183043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183043 prefixEnd_4183043 := by exact prefixLift 4183043
  have htrace : WordTrace (prefixWord ++ tailWord_4183043) baseStart_4183043 baseEnd_4183043 := by
    simpa [prefixWord, tailWord_4183043, baseEnd_4183043] using wordTrace_append hprefix tailTrace_4183043
  have hstable : (prefixWord ++ tailWord_4183043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183043).length < 2 ^ (prefixWord ++ tailWord_4183043).sum := by decide
  have hdescent : baseEnd_4183043 < baseStart_4183043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183058 : List Nat := [3, 2, 5, 1, 1, 1, 1, 4, 5]
def baseStart_4183058 : Nat := 118140960795 + 4183058 * 2 ^ 59
def prefixEnd_4183058 : Nat := 4983230072969 + 3 ^ 40 * 4183058 * 2
def baseEnd_4183058 : Nat := 238657706626133333337497

theorem tailTrace_4183058 : CollatzResearch.WordTrace tailWord_4183058 prefixEnd_4183058 238657706626133333337497 := by
  unfold tailWord_4183058
  simp only [CollatzResearch.WordTrace]
  refine ⟨38142164819875687568617457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101712439519668500182979885 38142164819875687568617457)
  ·
    refine ⟨28606623614906765676463093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38142164819875687568617457 28606623614906765676463093)
    ·
      refine ⟨2681870963897509282168415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28606623614906765676463093 2681870963897509282168415)
      ·
        refine ⟨4022806445846263923252623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2681870963897509282168415 4022806445846263923252623)
        ·
          refine ⟨6034209668769395884878935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4022806445846263923252623 6034209668769395884878935)
          ·
            refine ⟨9051314503154093827318403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6034209668769395884878935 9051314503154093827318403)
            ·
              refine ⟨13576971754731140740977605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9051314503154093827318403 13576971754731140740977605)
              ·
                refine ⟨2545682204012088888933301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13576971754731140740977605 2545682204012088888933301)
                ·
                  refine ⟨238657706626133333337497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2545682204012088888933301 238657706626133333337497)
                  ·
                    rfl

theorem cell23_4183058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_4183058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183058 prefixEnd_4183058 := by exact prefixLift 4183058
  have htrace : WordTrace (prefixWord ++ tailWord_4183058) baseStart_4183058 baseEnd_4183058 := by
    simpa [prefixWord, tailWord_4183058, baseEnd_4183058] using wordTrace_append hprefix tailTrace_4183058
  have hstable : (prefixWord ++ tailWord_4183058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183058).length < 2 ^ (prefixWord ++ tailWord_4183058).sum := by decide
  have hdescent : baseEnd_4183058 < baseStart_4183058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183074 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 2, 4, 2]
def baseStart_4183074 : Nat := 118140960795 + 4183074 * 2 ^ 59
def prefixEnd_4183074 : Nat := 4983230072969 + 3 ^ 40 * 4183074 * 2
def baseEnd_4183074 : Nat := 2147927575325671937437399

theorem tailTrace_4183074 : CollatzResearch.WordTrace tailWord_4183074 prefixEnd_4183074 2147927575325671937437399 := by
  unfold tailWord_4183074
  simp only [CollatzResearch.WordTrace]
  refine ⟨38142310711861196251763069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101712828564963190004701517 38142310711861196251763069)
  ·
    refine ⟨14303366516947948594411151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38142310711861196251763069 14303366516947948594411151)
    ·
      refine ⟨21455049775421922891616727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14303366516947948594411151 21455049775421922891616727)
      ·
        refine ⟨32182574663132884337425091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21455049775421922891616727 32182574663132884337425091)
        ·
          refine ⟨48273861994699326506137637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32182574663132884337425091 48273861994699326506137637)
          ·
            refine ⟨9051349124006123719900807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48273861994699326506137637 9051349124006123719900807)
            ·
              refine ⟨13577023686009185579851211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9051349124006123719900807 13577023686009185579851211)
              ·
                refine ⟨20365535529013778369776817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13577023686009185579851211 20365535529013778369776817)
                ·
                  refine ⟨15274151646760333777332613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20365535529013778369776817 15274151646760333777332613)
                  ·
                    refine ⟨2863903433767562583249865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15274151646760333777332613 2863903433767562583249865)
                    ·
                      refine ⟨2147927575325671937437399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2863903433767562583249865 2147927575325671937437399)
                      ·
                        rfl

theorem cell23_4183074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_4183074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183074 prefixEnd_4183074 := by exact prefixLift 4183074
  have htrace : WordTrace (prefixWord ++ tailWord_4183074) baseStart_4183074 baseEnd_4183074 := by
    simpa [prefixWord, tailWord_4183074, baseEnd_4183074] using wordTrace_append hprefix tailTrace_4183074
  have hstable : (prefixWord ++ tailWord_4183074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183074).length < 2 ^ (prefixWord ++ tailWord_4183074).sum := by decide
  have hdescent : baseEnd_4183074 < baseStart_4183074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183094 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_4183094 : Nat := 118140960795 + 4183094 * 2 ^ 59
def prefixEnd_4183094 : Nat := 4983230072969 + 3 ^ 40 * 4183094 * 2
def baseEnd_4183094 : Nat := 2147937844938761859187307

theorem tailTrace_4183094 : CollatzResearch.WordTrace tailWord_4183094 prefixEnd_4183094 2147937844938761859187307 := by
  unfold tailWord_4183094
  simp only [CollatzResearch.WordTrace]
  refine ⟨9535623269210770526423771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101713314871581552281853557 9535623269210770526423771)
  ·
    refine ⟨14303434903816155789635657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9535623269210770526423771 14303434903816155789635657)
    ·
      refine ⟨10727576177862116842226743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14303434903816155789635657 10727576177862116842226743)
      ·
        refine ⟨16091364266793175263340115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10727576177862116842226743 16091364266793175263340115)
        ·
          refine ⟨24137046400189762895010173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16091364266793175263340115 24137046400189762895010173)
          ·
            refine ⟨9051392400071161085628815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24137046400189762895010173 9051392400071161085628815)
            ·
              refine ⟨13577088600106741628443223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9051392400071161085628815 13577088600106741628443223)
              ·
                refine ⟨20365632900160112442664835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13577088600106741628443223 20365632900160112442664835)
                ·
                  refine ⟨30548449350240168663997253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20365632900160112442664835 30548449350240168663997253)
                  ·
                    refine ⟨5727834253170031624499485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30548449350240168663997253 5727834253170031624499485)
                    ·
                      refine ⟨2147937844938761859187307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5727834253170031624499485 2147937844938761859187307)
                      ·
                        rfl

theorem cell23_4183094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_4183094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183094 prefixEnd_4183094 := by exact prefixLift 4183094
  have htrace : WordTrace (prefixWord ++ tailWord_4183094) baseStart_4183094 baseEnd_4183094 := by
    simpa [prefixWord, tailWord_4183094, baseEnd_4183094] using wordTrace_append hprefix tailTrace_4183094
  have hstable : (prefixWord ++ tailWord_4183094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183094).length < 2 ^ (prefixWord ++ tailWord_4183094).sum := by decide
  have hdescent : baseEnd_4183094 < baseStart_4183094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183101 : List Nat := [1, 4, 1, 3, 1, 3, 2, 3, 1, 4]
def baseStart_4183101 : Nat := 118140960795 + 4183101 * 2 ^ 59
def prefixEnd_4183101 : Nat := 4983230072969 + 3 ^ 40 * 4183101 * 2
def baseEnd_4183101 : Nat := 715980479767781110599925

theorem tailTrace_4183101 : CollatzResearch.WordTrace tailWord_4183101 prefixEnd_4183101 715980479767781110599925 := by
  unfold tailWord_4183101
  simp only [CollatzResearch.WordTrace]
  refine ⟨152570227618346968618285157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101713485078897979078856771 152570227618346968618285157)
  ·
    refine ⟨28606917678440056615928467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152570227618346968618285157 28606917678440056615928467)
    ·
      refine ⟨42910376517660084923892701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28606917678440056615928467 42910376517660084923892701)
      ·
        refine ⟨16091391194122531846459763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42910376517660084923892701 16091391194122531846459763)
        ·
          refine ⟨24137086791183797769689645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16091391194122531846459763 24137086791183797769689645)
          ·
            refine ⟨9051407546693924163633617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24137086791183797769689645 9051407546693924163633617)
            ·
              refine ⟨6788555660020443122725213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9051407546693924163633617 6788555660020443122725213)
              ·
                refine ⟨2545708372507666171021955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6788555660020443122725213 2545708372507666171021955)
                ·
                  refine ⟨3818562558761499256532933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2545708372507666171021955 3818562558761499256532933)
                  ·
                    refine ⟨715980479767781110599925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3818562558761499256532933 715980479767781110599925)
                    ·
                      rfl

theorem cell23_4183101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_4183101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183101 prefixEnd_4183101 := by exact prefixLift 4183101
  have htrace : WordTrace (prefixWord ++ tailWord_4183101) baseStart_4183101 baseEnd_4183101 := by
    simpa [prefixWord, tailWord_4183101, baseEnd_4183101] using wordTrace_append hprefix tailTrace_4183101
  have hstable : (prefixWord ++ tailWord_4183101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183101).length < 2 ^ (prefixWord ++ tailWord_4183101).sum := by decide
  have hdescent : baseEnd_4183101 < baseStart_4183101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183107 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 5, 1, 3]
def baseStart_4183107 : Nat := 118140960795 + 4183107 * 2 ^ 59
def prefixEnd_4183107 : Nat := 4983230072969 + 3 ^ 40 * 4183107 * 2
def baseEnd_4183107 : Nat := 2147944520187270308324747

theorem tailTrace_4183107 : CollatzResearch.WordTrace tailWord_4183107 prefixEnd_4183107 2147944520187270308324747 := by
  unfold tailWord_4183107
  simp only [CollatzResearch.WordTrace]
  refine ⟨152570446456325231643003575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101713630970883487762002383 152570446456325231643003575)
  ·
    refine ⟨228855669684487847464505363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152570446456325231643003575 228855669684487847464505363)
    ·
      refine ⟨343283504526731771196758045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228855669684487847464505363 343283504526731771196758045)
      ·
        refine ⟨128731314197524414198784267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343283504526731771196758045 128731314197524414198784267)
        ·
          refine ⟨193096971296286621298176401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128731314197524414198784267 193096971296286621298176401)
          ·
            refine ⟨144822728472214965973632301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193096971296286621298176401 144822728472214965973632301)
            ·
              refine ⟨54308523177080612240112113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144822728472214965973632301 54308523177080612240112113)
              ·
                refine ⟨40731392382810459180084085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54308523177080612240112113 40731392382810459180084085)
                ·
                  refine ⟨3818568035888480548132883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40731392382810459180084085 3818568035888480548132883)
                  ·
                    refine ⟨5727852053832720822199325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3818568035888480548132883 5727852053832720822199325)
                    ·
                      refine ⟨2147944520187270308324747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5727852053832720822199325 2147944520187270308324747)
                      ·
                        rfl

theorem cell23_4183107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 1, 3].length) (baseStart_4183107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183107 prefixEnd_4183107 := by exact prefixLift 4183107
  have htrace : WordTrace (prefixWord ++ tailWord_4183107) baseStart_4183107 baseEnd_4183107 := by
    simpa [prefixWord, tailWord_4183107, baseEnd_4183107] using wordTrace_append hprefix tailTrace_4183107
  have hstable : (prefixWord ++ tailWord_4183107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183107).length < 2 ^ (prefixWord ++ tailWord_4183107).sum := by decide
  have hdescent : baseEnd_4183107 < baseStart_4183107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183117 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_4183117 : Nat := 118140960795 + 4183117 * 2 ^ 59
def prefixEnd_4183117 : Nat := 4983230072969 + 3 ^ 40 * 4183117 * 2
def baseEnd_4183117 : Nat := 2147949654993815269199701

theorem tailTrace_4183117 : CollatzResearch.WordTrace tailWord_4183117 prefixEnd_4183117 2147949654993815269199701 := by
  unfold tailWord_4183117
  simp only [CollatzResearch.WordTrace]
  refine ⟨152570811186289003350867605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101713874124192668900578403 152570811186289003350867605)
  ·
    refine ⟨7151756774357297032071919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152570811186289003350867605 7151756774357297032071919)
    ·
      refine ⟨10727635161535945548107879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7151756774357297032071919 10727635161535945548107879)
      ·
        refine ⟨16091452742303918322161819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10727635161535945548107879 16091452742303918322161819)
        ·
          refine ⟨24137179113455877483242729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16091452742303918322161819 24137179113455877483242729)
          ·
            refine ⟨18102884335091908112432047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24137179113455877483242729 18102884335091908112432047)
            ·
              refine ⟨27154326502637862168648071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18102884335091908112432047 27154326502637862168648071)
              ·
                refine ⟨40731489753956793252972107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27154326502637862168648071 40731489753956793252972107)
                ·
                  refine ⟨61097234630935189879458161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40731489753956793252972107 61097234630935189879458161)
                  ·
                    refine ⟨45822925973201392409593621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61097234630935189879458161 45822925973201392409593621)
                    ·
                      refine ⟨2147949654993815269199701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45822925973201392409593621 2147949654993815269199701)
                      ·
                        rfl

theorem cell23_4183117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_4183117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183117 prefixEnd_4183117 := by exact prefixLift 4183117
  have htrace : WordTrace (prefixWord ++ tailWord_4183117) baseStart_4183117 baseEnd_4183117 := by
    simpa [prefixWord, tailWord_4183117, baseEnd_4183117] using wordTrace_append hprefix tailTrace_4183117
  have hstable : (prefixWord ++ tailWord_4183117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183117).length < 2 ^ (prefixWord ++ tailWord_4183117).sum := by decide
  have hdescent : baseEnd_4183117 < baseStart_4183117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183124 : List Nat := [2, 4, 1, 1, 1, 1, 3, 3, 3, 1, 3]
def baseStart_4183124 : Nat := 118140960795 + 4183124 * 2 ^ 59
def prefixEnd_4183124 : Nat := 4983230072969 + 3 ^ 40 * 4183124 * 2
def baseEnd_4183124 : Nat := 2147953249358396741812169

theorem tailTrace_4183124 : CollatzResearch.WordTrace tailWord_4183124 prefixEnd_4183124 2147953249358396741812169 := by
  unfold tailWord_4183124
  simp only [CollatzResearch.WordTrace]
  refine ⟨76285533248631821773186213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101714044331509095697581617 76285533248631821773186213)
  ·
    refine ⟨14303537484118466582472415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76285533248631821773186213 14303537484118466582472415)
    ·
      refine ⟨21455306226177699873708623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14303537484118466582472415 21455306226177699873708623)
      ·
        refine ⟨32182959339266549810562935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21455306226177699873708623 32182959339266549810562935)
        ·
          refine ⟨48274439008899824715844403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32182959339266549810562935 48274439008899824715844403)
          ·
            refine ⟨72411658513349737073766605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48274439008899824715844403 72411658513349737073766605)
            ·
              refine ⟨27154371942506151402662477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72411658513349737073766605 27154371942506151402662477)
              ·
                refine ⟨10182889478439806775998429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27154371942506151402662477 10182889478439806775998429)
                ·
                  refine ⟨3818583554414927540999411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10182889478439806775998429 3818583554414927540999411)
                  ·
                    refine ⟨5727875331622391311499117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3818583554414927540999411 5727875331622391311499117)
                    ·
                      refine ⟨2147953249358396741812169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5727875331622391311499117 2147953249358396741812169)
                      ·
                        rfl

theorem cell23_4183124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_4183124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183124 prefixEnd_4183124 := by exact prefixLift 4183124
  have htrace : WordTrace (prefixWord ++ tailWord_4183124) baseStart_4183124 baseEnd_4183124 := by
    simpa [prefixWord, tailWord_4183124, baseEnd_4183124] using wordTrace_append hprefix tailTrace_4183124
  have hstable : (prefixWord ++ tailWord_4183124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183124).length < 2 ^ (prefixWord ++ tailWord_4183124).sum := by decide
  have hdescent : baseEnd_4183124 < baseStart_4183124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183130 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4]
def baseStart_4183130 : Nat := 118140960795 + 4183130 * 2 ^ 59
def prefixEnd_4183130 : Nat := 4983230072969 + 3 ^ 40 * 4183130 * 2
def baseEnd_4183130 : Nat := 2147956330242323718337141

theorem tailTrace_4183130 : CollatzResearch.WordTrace tailWord_4183130 prefixEnd_4183130 2147956330242323718337141 := by
  unfold tailWord_4183130
  simp only [CollatzResearch.WordTrace]
  refine ⟨38142821333810476642772711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101714190223494604380727229 38142821333810476642772711)
  ·
    refine ⟨57214232000715714964159067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38142821333810476642772711 57214232000715714964159067)
    ·
      refine ⟨85821348001073572446238601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57214232000715714964159067 85821348001073572446238601)
      ·
        refine ⟨64366011000805179334678951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85821348001073572446238601 64366011000805179334678951)
        ·
          refine ⟨96549016501207769002018427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64366011000805179334678951 96549016501207769002018427)
          ·
            refine ⟨144823524751811653503027641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96549016501207769002018427 144823524751811653503027641)
            ·
              refine ⟨108617643563858740127270731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144823524751811653503027641 108617643563858740127270731)
              ·
                refine ⟨162926465345788110190906097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108617643563858740127270731 162926465345788110190906097)
                ·
                  refine ⟨122194849009341082643179573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162926465345788110190906097 122194849009341082643179573)
                  ·
                    refine ⟨11455767094625726497798085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 122194849009341082643179573 11455767094625726497798085)
                    ·
                      refine ⟨2147956330242323718337141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11455767094625726497798085 2147956330242323718337141)
                      ·
                        rfl

theorem cell23_4183130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_4183130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183130 prefixEnd_4183130 := by exact prefixLift 4183130
  have htrace : WordTrace (prefixWord ++ tailWord_4183130) baseStart_4183130 baseEnd_4183130 := by
    simpa [prefixWord, tailWord_4183130, baseEnd_4183130] using wordTrace_append hprefix tailTrace_4183130
  have hstable : (prefixWord ++ tailWord_4183130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183130).length < 2 ^ (prefixWord ++ tailWord_4183130).sum := by decide
  have hdescent : baseEnd_4183130 < baseStart_4183130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183191 : List Nat := [1, 1, 3, 3, 3, 1, 4, 1, 2, 4]
def baseStart_4183191 : Nat := 118140960795 + 4183191 * 2 ^ 59
def prefixEnd_4183191 : Nat := 4983230072969 + 3 ^ 40 * 4183191 * 2
def baseEnd_4183191 : Nat := 715995884187415993224787

theorem tailTrace_4183191 : CollatzResearch.WordTrace tailWord_4183191 prefixEnd_4183191 715995884187415993224787 := by
  unfold tailWord_4183191
  simp only [CollatzResearch.WordTrace]
  refine ⟨152573510188020913989061427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101715673458680609326040951 152573510188020913989061427)
  ·
    refine ⟨228860265282031370983592141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152573510188020913989061427 228860265282031370983592141)
    ·
      refine ⟨85822599480761764118847053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228860265282031370983592141 85822599480761764118847053)
      ·
        refine ⟨32183474805285661544567645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85822599480761764118847053 32183474805285661544567645)
        ·
          refine ⟨12068803051982123079212867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32183474805285661544567645 12068803051982123079212867)
          ·
            refine ⟨18103204577973184618819301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12068803051982123079212867 18103204577973184618819301)
            ·
              refine ⟨3394350858369972116028619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18103204577973184618819301 3394350858369972116028619)
              ·
                refine ⟨5091526287554958174042929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3394350858369972116028619 5091526287554958174042929)
                ·
                  refine ⟨3818644715666218630532197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5091526287554958174042929 3818644715666218630532197)
                  ·
                    refine ⟨715995884187415993224787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3818644715666218630532197 715995884187415993224787)
                    ·
                      rfl

theorem cell23_4183191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 2, 4].length) (baseStart_4183191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183191 prefixEnd_4183191 := by exact prefixLift 4183191
  have htrace : WordTrace (prefixWord ++ tailWord_4183191) baseStart_4183191 baseEnd_4183191 := by
    simpa [prefixWord, tailWord_4183191, baseEnd_4183191] using wordTrace_append hprefix tailTrace_4183191
  have hstable : (prefixWord ++ tailWord_4183191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183191).length < 2 ^ (prefixWord ++ tailWord_4183191).sum := by decide
  have hdescent : baseEnd_4183191 < baseStart_4183191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183198 : List Nat := [4, 3, 1, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_4183198 : Nat := 118140960795 + 4183198 * 2 ^ 59
def prefixEnd_4183198 : Nat := 4983230072969 + 3 ^ 40 * 4183198 * 2
def baseEnd_4183198 : Nat := 2147991246926829452286829

theorem tailTrace_4183198 : CollatzResearch.WordTrace tailWord_4183198 prefixEnd_4183198 2147991246926829452286829 := by
  unfold tailWord_4183198
  simp only [CollatzResearch.WordTrace]
  refine ⟨19071720687374444273070781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101715843665997036123044165 19071720687374444273070781)
  ·
    refine ⟨7151895257765416602401543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19071720687374444273070781 7151895257765416602401543)
    ·
      refine ⟨10727842886648124903602315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7151895257765416602401543 10727842886648124903602315)
      ·
        refine ⟨16091764329972187355403473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10727842886648124903602315 16091764329972187355403473)
        ·
          refine ⟨12068823247479140516552605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16091764329972187355403473 12068823247479140516552605)
          ·
            refine ⟨4525808717804677693707227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12068823247479140516552605 4525808717804677693707227)
            ·
              refine ⟨6788713076707016540560841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4525808717804677693707227 6788713076707016540560841)
              ·
                refine ⟨5091534807530262405420631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6788713076707016540560841 5091534807530262405420631)
                ·
                  refine ⟨7637302211295393608130947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5091534807530262405420631 7637302211295393608130947)
                  ·
                    refine ⟨11455953316943090412196421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7637302211295393608130947 11455953316943090412196421)
                    ·
                      refine ⟨2147991246926829452286829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11455953316943090412196421 2147991246926829452286829)
                      ·
                        rfl

theorem cell23_4183198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_4183198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183198 prefixEnd_4183198 := by exact prefixLift 4183198
  have htrace : WordTrace (prefixWord ++ tailWord_4183198) baseStart_4183198 baseEnd_4183198 := by
    simpa [prefixWord, tailWord_4183198, baseEnd_4183198] using wordTrace_append hprefix tailTrace_4183198
  have hstable : (prefixWord ++ tailWord_4183198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183198).length < 2 ^ (prefixWord ++ tailWord_4183198).sum := by decide
  have hdescent : baseEnd_4183198 < baseStart_4183198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183232 : List Nat := [2, 1, 1, 2, 6, 2, 2, 2, 1, 2, 2]
def baseStart_4183232 : Nat := 118140960795 + 4183232 * 2 ^ 59
def prefixEnd_4183232 : Nat := 4983230072969 + 3 ^ 40 * 4183232 * 2
def baseEnd_4183232 : Nat := 2148008705269082319261673

theorem tailTrace_4183232 : CollatzResearch.WordTrace tailWord_4183232 prefixEnd_4183232 2148008705269082319261673 := by
  unfold tailWord_4183232
  simp only [CollatzResearch.WordTrace]
  refine ⟨76287502790436188995651975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101716670387248251994202633 76287502790436188995651975)
  ·
    refine ⟨114431254185654283493477963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76287502790436188995651975 114431254185654283493477963)
    ·
      refine ⟨171646881278481425240216945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114431254185654283493477963 171646881278481425240216945)
      ·
        refine ⟨128735160958861068930162709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171646881278481425240216945 128735160958861068930162709)
        ·
          refine ⟨6034460669946612606101377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128735160958861068930162709 6034460669946612606101377)
          ·
            refine ⟨4525845502459959454576033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6034460669946612606101377 4525845502459959454576033)
            ·
              refine ⟨3394384126844969590932025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4525845502459959454576033 3394384126844969590932025)
              ·
                refine ⟨2545788095133727193199019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3394384126844969590932025 2545788095133727193199019)
                ·
                  refine ⟨3818682142700590789798529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2545788095133727193199019 3818682142700590789798529)
                  ·
                    refine ⟨2864011607025443092348897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3818682142700590789798529 2864011607025443092348897)
                    ·
                      refine ⟨2148008705269082319261673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2864011607025443092348897 2148008705269082319261673)
                      ·
                        rfl

theorem cell23_4183232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 1, 2, 2].length) (baseStart_4183232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183232 prefixEnd_4183232 := by exact prefixLift 4183232
  have htrace : WordTrace (prefixWord ++ tailWord_4183232) baseStart_4183232 baseEnd_4183232 := by
    simpa [prefixWord, tailWord_4183232, baseEnd_4183232] using wordTrace_append hprefix tailTrace_4183232
  have hstable : (prefixWord ++ tailWord_4183232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183232).length < 2 ^ (prefixWord ++ tailWord_4183232).sum := by decide
  have hdescent : baseEnd_4183232 < baseStart_4183232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183257 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 4, 4, 3]
def baseStart_4183257 : Nat := 118140960795 + 4183257 * 2 ^ 59
def prefixEnd_4183257 : Nat := 4983230072969 + 3 ^ 40 * 4183257 * 2
def baseEnd_4183257 : Nat := 2148021542285444721449057

theorem tailTrace_4183257 : CollatzResearch.WordTrace tailWord_4183257 prefixEnd_4183257 2148021542285444721449057 := by
  unfold tailWord_4183257
  simp only [CollatzResearch.WordTrace]
  refine ⟨152575917405781807260964025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101717278270521204840642683 152575917405781807260964025)
  ·
    refine ⟨114431938054336355445723019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152575917405781807260964025 114431938054336355445723019)
    ·
      refine ⟨171647907081504533168584529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114431938054336355445723019 171647907081504533168584529)
      ·
        refine ⟨128735930311128399876438397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171647907081504533168584529 128735930311128399876438397)
        ·
          refine ⟨48275973866673149953664399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128735930311128399876438397 48275973866673149953664399)
          ·
            refine ⟨72413960800009724930496599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48275973866673149953664399 72413960800009724930496599)
            ·
              refine ⟨108620941200014587395744899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72413960800009724930496599 108620941200014587395744899)
              ·
                refine ⟨162931411800021881093617349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108620941200014587395744899 162931411800021881093617349)
                ·
                  refine ⟨30549639712504102705053253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162931411800021881093617349 30549639712504102705053253)
                  ·
                    refine ⟨5728057446094519257197485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30549639712504102705053253 5728057446094519257197485)
                    ·
                      refine ⟨2148021542285444721449057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5728057446094519257197485 2148021542285444721449057)
                      ·
                        rfl

theorem cell23_4183257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 4, 3].length) (baseStart_4183257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183257 prefixEnd_4183257 := by exact prefixLift 4183257
  have htrace : WordTrace (prefixWord ++ tailWord_4183257) baseStart_4183257 baseEnd_4183257 := by
    simpa [prefixWord, tailWord_4183257, baseEnd_4183257] using wordTrace_append hprefix tailTrace_4183257
  have hstable : (prefixWord ++ tailWord_4183257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183257).length < 2 ^ (prefixWord ++ tailWord_4183257).sum := by decide
  have hdescent : baseEnd_4183257 < baseStart_4183257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183287 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 3]
def baseStart_4183287 : Nat := 118140960795 + 4183287 * 2 ^ 59
def prefixEnd_4183287 : Nat := 4983230072969 + 3 ^ 40 * 4183287 * 2
def baseEnd_4183287 : Nat := 2148036946705079604073919

theorem tailTrace_4183287 : CollatzResearch.WordTrace tailWord_4183287 prefixEnd_4183287 2148036946705079604073919 := by
  unfold tailWord_4183287
  simp only [CollatzResearch.WordTrace]
  refine ⟨152577011595673122384556115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101718007730448748256370743 152577011595673122384556115)
  ·
    refine ⟨228865517393509683576834173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152577011595673122384556115 228865517393509683576834173)
    ·
      refine ⟨85824569022566131341312815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228865517393509683576834173 85824569022566131341312815)
      ·
        refine ⟨128736853533849197011969223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85824569022566131341312815 128736853533849197011969223)
        ·
          refine ⟨193105280300773795517953835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128736853533849197011969223 193105280300773795517953835)
          ·
            refine ⟨289657920451160693276930753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193105280300773795517953835 289657920451160693276930753)
            ·
              refine ⟨217243440338370519957698065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289657920451160693276930753 217243440338370519957698065)
              ·
                refine ⟨162932580253777889968273549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217243440338370519957698065 162932580253777889968273549)
                ·
                  refine ⟨61099717595166708738102581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162932580253777889968273549 61099717595166708738102581)
                  ·
                    refine ⟨5728098524546878944197117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61099717595166708738102581 5728098524546878944197117)
                    ·
                      refine ⟨2148036946705079604073919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5728098524546878944197117 2148036946705079604073919)
                      ·
                        rfl

theorem cell23_4183287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 3].length) (baseStart_4183287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183287 prefixEnd_4183287 := by exact prefixLift 4183287
  have htrace : WordTrace (prefixWord ++ tailWord_4183287) baseStart_4183287 baseEnd_4183287 := by
    simpa [prefixWord, tailWord_4183287, baseEnd_4183287] using wordTrace_append hprefix tailTrace_4183287
  have hstable : (prefixWord ++ tailWord_4183287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183287).length < 2 ^ (prefixWord ++ tailWord_4183287).sum := by decide
  have hdescent : baseEnd_4183287 < baseStart_4183287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183294 : List Nat := [4, 2, 2, 1, 1, 2, 1, 3, 7]
def baseStart_4183294 : Nat := 118140960795 + 4183294 * 2 ^ 59
def prefixEnd_4183294 : Nat := 4983230072969 + 3 ^ 40 * 4183294 * 2
def baseEnd_4183294 : Nat := 238671171229962341854043

theorem tailTrace_4183294 : CollatzResearch.WordTrace tailWord_4183294 prefixEnd_4183294 238671171229962341854043 := by
  unfold tailWord_4183294
  simp only [CollatzResearch.WordTrace]
  refine ⟨19072158363330970322507617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101718177937765175053373957 19072158363330970322507617)
  ·
    refine ⟨14304118772498227741880713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19072158363330970322507617 14304118772498227741880713)
    ·
      refine ⟨10728089079373670806410535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14304118772498227741880713 10728089079373670806410535)
      ·
        refine ⟨16092133619060506209615803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10728089079373670806410535 16092133619060506209615803)
        ·
          refine ⟨24138200428590759314423705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16092133619060506209615803 24138200428590759314423705)
          ·
            refine ⟨18103650321443069485817779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24138200428590759314423705 18103650321443069485817779)
            ·
              refine ⟨27155475482164604228726669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18103650321443069485817779 27155475482164604228726669)
              ·
                refine ⟨10183303305811726585772501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27155475482164604228726669 10183303305811726585772501)
                ·
                  refine ⟨238671171229962341854043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10183303305811726585772501 238671171229962341854043)
                  ·
                    rfl

theorem cell23_4183294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_4183294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183294 prefixEnd_4183294 := by exact prefixLift 4183294
  have htrace : WordTrace (prefixWord ++ tailWord_4183294) baseStart_4183294 baseEnd_4183294 := by
    simpa [prefixWord, tailWord_4183294, baseEnd_4183294] using wordTrace_append hprefix tailTrace_4183294
  have hstable : (prefixWord ++ tailWord_4183294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183294).length < 2 ^ (prefixWord ++ tailWord_4183294).sum := by decide
  have hdescent : baseEnd_4183294 < baseStart_4183294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183307 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 1, 7]
def baseStart_4183307 : Nat := 118140960795 + 4183307 * 2 ^ 59
def prefixEnd_4183307 : Nat := 4983230072969 + 3 ^ 40 * 4183307 * 2
def baseEnd_4183307 : Nat := 716015738772723175274609

theorem tailTrace_4183307 : CollatzResearch.WordTrace tailWord_4183307 prefixEnd_4183307 716015738772723175274609 := by
  unfold tailWord_4183307
  simp only [CollatzResearch.WordTrace]
  refine ⟨152577741055600665800284175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101718494037067110533522783 152577741055600665800284175)
  ·
    refine ⟨228866611583400998700426263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152577741055600665800284175 228866611583400998700426263)
    ·
      refine ⟨343299917375101498050639395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228866611583400998700426263 343299917375101498050639395)
      ·
        refine ⟨514949876062652247075959093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343299917375101498050639395 514949876062652247075959093)
        ·
          refine ⟨48276550880873648163371165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 514949876062652247075959093 48276550880873648163371165)
          ·
            refine ⟨18103706580327618061264187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48276550880873648163371165 18103706580327618061264187)
            ·
              refine ⟨27155559870491427091896281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18103706580327618061264187 27155559870491427091896281)
              ·
                refine ⟨20366669902868570318922211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27155559870491427091896281 20366669902868570318922211)
                ·
                  refine ⟨30550004854302855478383317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20366669902868570318922211 30550004854302855478383317)
                  ·
                    refine ⟨716015738772723175274609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30550004854302855478383317 716015738772723175274609)
                    ·
                      rfl

theorem cell23_4183307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 7].length) (baseStart_4183307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183307 prefixEnd_4183307 := by exact prefixLift 4183307
  have htrace : WordTrace (prefixWord ++ tailWord_4183307) baseStart_4183307 baseEnd_4183307 := by
    simpa [prefixWord, tailWord_4183307, baseEnd_4183307] using wordTrace_append hprefix tailTrace_4183307
  have hstable : (prefixWord ++ tailWord_4183307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183307).length < 2 ^ (prefixWord ++ tailWord_4183307).sum := by decide
  have hdescent : baseEnd_4183307 < baseStart_4183307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183317 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 3, 2, 5]
def baseStart_4183317 : Nat := 118140960795 + 4183317 * 2 ^ 59
def prefixEnd_4183317 : Nat := 4983230072969 + 3 ^ 40 * 4183317 * 2
def baseEnd_4183317 : Nat := 2148052351124714486698781

theorem tailTrace_4183317 : CollatzResearch.WordTrace tailWord_4183317 prefixEnd_4183317 2148052351124714486698781 := by
  unfold tailWord_4183317
  simp only [CollatzResearch.WordTrace]
  refine ⟨152578105785564437508148205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101718737190376291672098803 152578105785564437508148205)
  ·
    refine ⟨57216789669586664065555577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152578105785564437508148205 57216789669586664065555577)
    ·
      refine ⟨42912592252189998049166683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57216789669586664065555577 42912592252189998049166683)
      ·
        refine ⟨64368888378284997073750025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42912592252189998049166683 64368888378284997073750025)
        ·
          refine ⟨48276666283713747805312519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64368888378284997073750025 48276666283713747805312519)
          ·
            refine ⟨72414999425570621707968779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48276666283713747805312519 72414999425570621707968779)
            ·
              refine ⟨108622499138355932561953169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72414999425570621707968779 108622499138355932561953169)
              ·
                refine ⟨81466874353766949421464877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108622499138355932561953169 81466874353766949421464877)
                ·
                  refine ⟨30550077882662606033049329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81466874353766949421464877 30550077882662606033049329)
                  ·
                    refine ⟨22912558411996954524786997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30550077882662606033049329 22912558411996954524786997)
                    ·
                      refine ⟨2148052351124714486698781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22912558411996954524786997 2148052351124714486698781)
                      ·
                        rfl

theorem cell23_4183317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_4183317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183317 prefixEnd_4183317 := by exact prefixLift 4183317
  have htrace : WordTrace (prefixWord ++ tailWord_4183317) baseStart_4183317 baseEnd_4183317 := by
    simpa [prefixWord, tailWord_4183317, baseEnd_4183317] using wordTrace_append hprefix tailTrace_4183317
  have hstable : (prefixWord ++ tailWord_4183317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183317).length < 2 ^ (prefixWord ++ tailWord_4183317).sum := by decide
  have hdescent : baseEnd_4183317 < baseStart_4183317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183328 : List Nat := [2, 1, 1, 5, 3, 2, 1, 3, 5]
def baseStart_4183328 : Nat := 118140960795 + 4183328 * 2 ^ 59
def prefixEnd_4183328 : Nat := 4983230072969 + 3 ^ 40 * 4183328 * 2
def baseEnd_4183328 : Nat := 238673111045768215962359

theorem tailTrace_4183328 : CollatzResearch.WordTrace tailWord_4183328 prefixEnd_4183328 238673111045768215962359 := by
  unfold tailWord_4183328
  simp only [CollatzResearch.WordTrace]
  refine ⟨76289253494262293193399319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101719004659016390924532425 76289253494262293193399319)
  ·
    refine ⟨114433880241393439790098979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76289253494262293193399319 114433880241393439790098979)
    ·
      refine ⟨171650820362090159685148469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114433880241393439790098979 171650820362090159685148469)
      ·
        refine ⟨16092264408945952470482669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171650820362090159685148469 16092264408945952470482669)
        ·
          refine ⟨6034599153354732176431001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16092264408945952470482669 6034599153354732176431001)
          ·
            refine ⟨4525949365016049132323251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6034599153354732176431001 4525949365016049132323251)
            ·
              refine ⟨6788924047524073698484877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4525949365016049132323251 6788924047524073698484877)
              ·
                refine ⟨2545846517821527636931829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6788924047524073698484877 2545846517821527636931829)
                ·
                  refine ⟨238673111045768215962359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2545846517821527636931829 238673111045768215962359)
                  ·
                    rfl

theorem cell23_4183328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 5].length) (baseStart_4183328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183328 prefixEnd_4183328 := by exact prefixLift 4183328
  have htrace : WordTrace (prefixWord ++ tailWord_4183328) baseStart_4183328 baseEnd_4183328 := by
    simpa [prefixWord, tailWord_4183328, baseEnd_4183328] using wordTrace_append hprefix tailTrace_4183328
  have hstable : (prefixWord ++ tailWord_4183328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183328).length < 2 ^ (prefixWord ++ tailWord_4183328).sum := by decide
  have hdescent : baseEnd_4183328 < baseStart_4183328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183341 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 4, 5]
def baseStart_4183341 : Nat := 118140960795 + 4183341 * 2 ^ 59
def prefixEnd_4183341 : Nat := 4983230072969 + 3 ^ 40 * 4183341 * 2
def baseEnd_4183341 : Nat := 716021558220140797599557

theorem tailTrace_4183341 : CollatzResearch.WordTrace tailWord_4183341 prefixEnd_4183341 716021558220140797599557 := by
  unfold tailWord_4183341
  simp only [CollatzResearch.WordTrace]
  refine ⟨152578981137477489607021877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101719320758318326404681251 152578981137477489607021877)
  ·
    refine ⟨14304279481638514650658301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152578981137477489607021877 14304279481638514650658301)
    ·
      refine ⟨5364104805614442993996863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14304279481638514650658301 5364104805614442993996863)
      ·
        refine ⟨8046157208421664490995295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5364104805614442993996863 8046157208421664490995295)
        ·
          refine ⟨12069235812632496736492943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8046157208421664490995295 12069235812632496736492943)
          ·
            refine ⟨18103853718948745104739415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12069235812632496736492943 18103853718948745104739415)
            ·
              refine ⟨27155780578423117657109123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18103853718948745104739415 27155780578423117657109123)
              ·
                refine ⟨40733670867634676485663685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27155780578423117657109123 40733670867634676485663685)
                ·
                  refine ⟨7637563287681501841061941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40733670867634676485663685 7637563287681501841061941)
                  ·
                    refine ⟨716021558220140797599557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7637563287681501841061941 716021558220140797599557)
                    ·
                      rfl

theorem cell23_4183341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_4183341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183341 prefixEnd_4183341 := by exact prefixLift 4183341
  have htrace : WordTrace (prefixWord ++ tailWord_4183341) baseStart_4183341 baseEnd_4183341 := by
    simpa [prefixWord, tailWord_4183341, baseEnd_4183341] using wordTrace_append hprefix tailTrace_4183341
  have hstable : (prefixWord ++ tailWord_4183341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183341).length < 2 ^ (prefixWord ++ tailWord_4183341).sum := by decide
  have hdescent : baseEnd_4183341 < baseStart_4183341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183344 : List Nat := [2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 4]
def baseStart_4183344 : Nat := 118140960795 + 4183344 * 2 ^ 59
def prefixEnd_4183344 : Nat := 4983230072969 + 3 ^ 40 * 4183344 * 2
def baseEnd_4183344 : Nat := 2148066215102385881061157

theorem tailTrace_4183344 : CollatzResearch.WordTrace tailWord_4183344 prefixEnd_4183344 2148066215102385881061157 := by
  unfold tailWord_4183344
  simp only [CollatzResearch.WordTrace]
  refine ⟨76289545278233310559690543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101719393704311080746254057 76289545278233310559690543)
  ·
    refine ⟨114434317917349965839535815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76289545278233310559690543 114434317917349965839535815)
    ·
      refine ⟨171651476876024948759303723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114434317917349965839535815 171651476876024948759303723)
      ·
        refine ⟨257477215314037423138955585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171651476876024948759303723 257477215314037423138955585)
        ·
          refine ⟨193107911485528067354216689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257477215314037423138955585 193107911485528067354216689)
          ·
            refine ⟨144830933614146050515662517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193107911485528067354216689 144830933614146050515662517)
            ·
              refine ⟨13577900026326192235843361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144830933614146050515662517 13577900026326192235843361)
              ·
                refine ⟨10183425019744644176882521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13577900026326192235843361 10183425019744644176882521)
                ·
                  refine ⟨7637568764808483132661891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10183425019744644176882521 7637568764808483132661891)
                  ·
                    refine ⟨11456353147212724698992837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7637568764808483132661891 11456353147212724698992837)
                    ·
                      refine ⟨2148066215102385881061157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11456353147212724698992837 2148066215102385881061157)
                      ·
                        rfl

theorem cell23_4183344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 4].length) (baseStart_4183344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183344 prefixEnd_4183344 := by exact prefixLift 4183344
  have htrace : WordTrace (prefixWord ++ tailWord_4183344) baseStart_4183344 baseEnd_4183344 := by
    simpa [prefixWord, tailWord_4183344, baseEnd_4183344] using wordTrace_append hprefix tailTrace_4183344
  have hstable : (prefixWord ++ tailWord_4183344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183344).length < 2 ^ (prefixWord ++ tailWord_4183344).sum := by decide
  have hdescent : baseEnd_4183344 < baseStart_4183344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183381 : List Nat := [1, 3, 2, 2, 3, 1, 1, 3, 2, 2, 3]
def baseStart_4183381 : Nat := 118140960795 + 4183381 * 2 ^ 59
def prefixEnd_4183381 : Nat := 4983230072969 + 3 ^ 40 * 4183381 * 2
def baseEnd_4183381 : Nat := 2148085213886602236298487

theorem tailTrace_4183381 : CollatzResearch.WordTrace tailWord_4183381 prefixEnd_4183381 2148085213886602236298487 := by
  unfold tailWord_4183381
  simp only [CollatzResearch.WordTrace]
  refine ⟨152580440057332576438477997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101720293371555050958985331 152580440057332576438477997)
  ·
    refine ⟨57217665021499716164429249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152580440057332576438477997 57217665021499716164429249)
    ·
      refine ⟨42913248766124787123321937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57217665021499716164429249 42913248766124787123321937)
      ·
        refine ⟨32184936574593590342491453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42913248766124787123321937 32184936574593590342491453)
        ·
          refine ⟨12069351215472596378434295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32184936574593590342491453 12069351215472596378434295)
          ·
            refine ⟨18104026823208894567651443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12069351215472596378434295 18104026823208894567651443)
            ·
              refine ⟨27156040234813341851477165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18104026823208894567651443 27156040234813341851477165)
              ·
                refine ⟨10183515088055003194303937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27156040234813341851477165 10183515088055003194303937)
                ·
                  refine ⟨7637636316041252395727953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10183515088055003194303937 7637636316041252395727953)
                  ·
                    refine ⟨5728227237030939296795965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7637636316041252395727953 5728227237030939296795965)
                    ·
                      refine ⟨2148085213886602236298487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5728227237030939296795965 2148085213886602236298487)
                      ·
                        rfl

theorem cell23_4183381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_4183381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183381 prefixEnd_4183381 := by exact prefixLift 4183381
  have htrace : WordTrace (prefixWord ++ tailWord_4183381) baseStart_4183381 baseEnd_4183381 := by
    simpa [prefixWord, tailWord_4183381, baseEnd_4183381] using wordTrace_append hprefix tailTrace_4183381
  have hstable : (prefixWord ++ tailWord_4183381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183381).length < 2 ^ (prefixWord ++ tailWord_4183381).sum := by decide
  have hdescent : baseEnd_4183381 < baseStart_4183381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183405 : List Nat := [1, 5, 1, 1, 1, 3, 4, 2, 1, 4]
def baseStart_4183405 : Nat := 118140960795 + 4183405 * 2 ^ 59
def prefixEnd_4183405 : Nat := 4983230072969 + 3 ^ 40 * 4183405 * 2
def baseEnd_4183405 : Nat := 716032512474103380799459

theorem tailTrace_4183405 : CollatzResearch.WordTrace tailWord_4183405 prefixEnd_4183405 716032512474103380799459 := by
  unfold tailWord_4183405
  simp only [CollatzResearch.WordTrace]
  refine ⟨152581315409245628537351669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101720876939497085691567779 152581315409245628537351669)
  ·
    refine ⟨14304498319616777675376719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152581315409245628537351669 14304498319616777675376719)
    ·
      refine ⟨21456747479425166513065079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14304498319616777675376719 21456747479425166513065079)
      ·
        refine ⟨32185121219137749769597619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21456747479425166513065079 32185121219137749769597619)
        ·
          refine ⟨48277681828706624654396429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32185121219137749769597619 48277681828706624654396429)
          ·
            refine ⟨18104130685764984245398661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48277681828706624654396429 18104130685764984245398661)
            ·
              refine ⟨3394524503580934546012249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18104130685764984245398661 3394524503580934546012249)
              ·
                refine ⟨2545893377685700909509187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3394524503580934546012249 2545893377685700909509187)
                ·
                  refine ⟨3818840066528551364263781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2545893377685700909509187 3818840066528551364263781)
                  ·
                    refine ⟨716032512474103380799459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3818840066528551364263781 716032512474103380799459)
                    ·
                      rfl

theorem cell23_4183405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_4183405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183405 prefixEnd_4183405 := by exact prefixLift 4183405
  have htrace : WordTrace (prefixWord ++ tailWord_4183405) baseStart_4183405 baseEnd_4183405 := by
    simpa [prefixWord, tailWord_4183405, baseEnd_4183405] using wordTrace_append hprefix tailTrace_4183405
  have hstable : (prefixWord ++ tailWord_4183405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183405).length < 2 ^ (prefixWord ++ tailWord_4183405).sum := by decide
  have hdescent : baseEnd_4183405 < baseStart_4183405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183421 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 1, 5, 2]
def baseStart_4183421 : Nat := 118140960795 + 4183421 * 2 ^ 59
def prefixEnd_4183421 : Nat := 4983230072969 + 3 ^ 40 * 4183421 * 2
def baseEnd_4183421 : Nat := 2148105753112782079798303

theorem tailTrace_4183421 : CollatzResearch.WordTrace tailWord_4183421 prefixEnd_4183421 2148105753112782079798303 := by
  unfold tailWord_4183421
  simp only [CollatzResearch.WordTrace]
  refine ⟨152581898977187663269934117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101721265984791775513289411 152581898977187663269934117)
  ·
    refine ⟨28609106058222686863112647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152581898977187663269934117 28609106058222686863112647)
    ·
      refine ⟨42913659087334030294668971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28609106058222686863112647 42913659087334030294668971)
      ·
        refine ⟨64370488631001045442003457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42913659087334030294668971 64370488631001045442003457)
        ·
          refine ⟨48277866473250784081502593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64370488631001045442003457 48277866473250784081502593)
          ·
            refine ⟨36208399854938088061126945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48277866473250784081502593 36208399854938088061126945)
            ·
              refine ⟨27156299891203566045845209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36208399854938088061126945 27156299891203566045845209)
              ·
                refine ⟨20367224918402674534383907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27156299891203566045845209 20367224918402674534383907)
                ·
                  refine ⟨30550837377604011801575861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20367224918402674534383907 30550837377604011801575861)
                  ·
                    refine ⟨2864141004150376106397737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30550837377604011801575861 2864141004150376106397737)
                    ·
                      refine ⟨2148105753112782079798303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2864141004150376106397737 2148105753112782079798303)
                      ·
                        rfl

theorem cell23_4183421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 5, 2].length) (baseStart_4183421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183421 prefixEnd_4183421 := by exact prefixLift 4183421
  have htrace : WordTrace (prefixWord ++ tailWord_4183421) baseStart_4183421 baseEnd_4183421 := by
    simpa [prefixWord, tailWord_4183421, baseEnd_4183421] using wordTrace_append hprefix tailTrace_4183421
  have hstable : (prefixWord ++ tailWord_4183421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183421).length < 2 ^ (prefixWord ++ tailWord_4183421).sum := by decide
  have hdescent : baseEnd_4183421 < baseStart_4183421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183428 : List Nat := [2, 3, 2, 1, 1, 4, 1, 2, 3, 1, 3]
def baseStart_4183428 : Nat := 118140960795 + 4183428 * 2 ^ 59
def prefixEnd_4183428 : Nat := 4983230072969 + 3 ^ 40 * 4183428 * 2
def baseEnd_4183428 : Nat := 2148109347477363552410771

theorem tailTrace_4183428 : CollatzResearch.WordTrace tailWord_4183428 prefixEnd_4183428 2148109347477363552410771 := by
  unfold tailWord_4183428
  simp only [CollatzResearch.WordTrace]
  refine ⟨76291077144081151732719469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101721436192108202310292625 76291077144081151732719469)
  ·
    refine ⟨28609153929030431899769801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76291077144081151732719469 28609153929030431899769801)
    ·
      refine ⟨21456865446772823924827351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28609153929030431899769801 21456865446772823924827351)
      ·
        refine ⟨32185298170159235887241027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21456865446772823924827351 32185298170159235887241027)
        ·
          refine ⟨48277947255238853830861541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32185298170159235887241027 48277947255238853830861541)
          ·
            refine ⟨9052115110357285093286539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48277947255238853830861541 9052115110357285093286539)
            ·
              refine ⟨13578172665535927639929809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9052115110357285093286539 13578172665535927639929809)
              ·
                refine ⟨10183629499151945729947357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13578172665535927639929809 10183629499151945729947357)
                ·
                  refine ⟨3818861062181979648730259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10183629499151945729947357 3818861062181979648730259)
                  ·
                    refine ⟨5728291593272969473095389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3818861062181979648730259 5728291593272969473095389)
                    ·
                      refine ⟨2148109347477363552410771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5728291593272969473095389 2148109347477363552410771)
                      ·
                        rfl

theorem cell23_4183428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_4183428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183428 prefixEnd_4183428 := by exact prefixLift 4183428
  have htrace : WordTrace (prefixWord ++ tailWord_4183428) baseStart_4183428 baseEnd_4183428 := by
    simpa [prefixWord, tailWord_4183428, baseEnd_4183428] using wordTrace_append hprefix tailTrace_4183428
  have hstable : (prefixWord ++ tailWord_4183428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183428).length < 2 ^ (prefixWord ++ tailWord_4183428).sum := by decide
  have hdescent : baseEnd_4183428 < baseStart_4183428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183448 : List Nat := [2, 1, 2, 5, 2, 1, 1, 3, 1, 5]
def baseStart_4183448 : Nat := 118140960795 + 4183448 * 2 ^ 59
def prefixEnd_4183448 : Nat := 4983230072969 + 3 ^ 40 * 4183448 * 2
def baseEnd_4183448 : Nat := 716039872363484491386893

theorem tailTrace_4183448 : CollatzResearch.WordTrace tailWord_4183448 prefixEnd_4183448 716039872363484491386893 := by
  unfold tailWord_4183448
  simp only [CollatzResearch.WordTrace]
  refine ⟨76291441874044923440583499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101721922498726564587444665 76291441874044923440583499)
  ·
    refine ⟨114437162811067385160875249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76291441874044923440583499 114437162811067385160875249)
    ·
      refine ⟨85827872108300538870656437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114437162811067385160875249 85827872108300538870656437)
      ·
        refine ⟨8046363010153175519124041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85827872108300538870656437 8046363010153175519124041)
        ·
          refine ⟨6034772257614881639343031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8046363010153175519124041 6034772257614881639343031)
          ·
            refine ⟨9052158386422322459014547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6034772257614881639343031 9052158386422322459014547)
            ·
              refine ⟨13578237579633483688521821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9052158386422322459014547 13578237579633483688521821)
              ·
                refine ⟨5091839092362556383195683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13578237579633483688521821 5091839092362556383195683)
                ·
                  refine ⟨7637758638543834574793525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5091839092362556383195683 7637758638543834574793525)
                  ·
                    refine ⟨716039872363484491386893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7637758638543834574793525 716039872363484491386893)
                    ·
                      rfl

theorem cell23_4183448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 1, 5].length) (baseStart_4183448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183448 prefixEnd_4183448 := by exact prefixLift 4183448
  have htrace : WordTrace (prefixWord ++ tailWord_4183448) baseStart_4183448 baseEnd_4183448 := by
    simpa [prefixWord, tailWord_4183448, baseEnd_4183448] using wordTrace_append hprefix tailTrace_4183448
  have hstable : (prefixWord ++ tailWord_4183448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183448).length < 2 ^ (prefixWord ++ tailWord_4183448).sum := by decide
  have hdescent : baseEnd_4183448 < baseStart_4183448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183461 : List Nat := [1, 3, 1, 2, 1, 1, 2, 6, 2, 4]
def baseStart_4183461 : Nat := 118140960795 + 4183461 * 2 ^ 59
def prefixEnd_4183461 : Nat := 4983230072969 + 3 ^ 40 * 4183461 * 2
def baseEnd_4183461 : Nat := 716042097446320641099373

theorem tailTrace_4183461 : CollatzResearch.WordTrace tailWord_4183461 prefixEnd_4183461 716042097446320641099373 := by
  unfold tailWord_4183461
  simp only [CollatzResearch.WordTrace]
  refine ⟨152583357897042750101390237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101722238598028500067593491 152583357897042750101390237)
  ·
    refine ⟨57218759211391031288021339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152583357897042750101390237 57218759211391031288021339)
    ·
      refine ⟨85828138817086546932032009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57218759211391031288021339 85828138817086546932032009)
      ·
        refine ⟨64371104112814910199024007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85828138817086546932032009 64371104112814910199024007)
        ·
          refine ⟨96556656169222365298536011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64371104112814910199024007 96556656169222365298536011)
          ·
            refine ⟨144834984253833547947804017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96556656169222365298536011 144834984253833547947804017)
            ·
              refine ⟨108626238190375160960853013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144834984253833547947804017 108626238190375160960853013)
              ·
                refine ⟨5091854915173835670039985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108626238190375160960853013 5091854915173835670039985)
                ·
                  refine ⟨3818891186380376752529989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5091854915173835670039985 3818891186380376752529989)
                  ·
                    refine ⟨716042097446320641099373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3818891186380376752529989 716042097446320641099373)
                    ·
                      rfl

theorem cell23_4183461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 4].length) (baseStart_4183461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183461 prefixEnd_4183461 := by exact prefixLift 4183461
  have htrace : WordTrace (prefixWord ++ tailWord_4183461) baseStart_4183461 baseEnd_4183461 := by
    simpa [prefixWord, tailWord_4183461, baseEnd_4183461] using wordTrace_append hprefix tailTrace_4183461
  have hstable : (prefixWord ++ tailWord_4183461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183461).length < 2 ^ (prefixWord ++ tailWord_4183461).sum := by decide
  have hdescent : baseEnd_4183461 < baseStart_4183461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183468 : List Nat := [2, 2, 1, 1, 1, 1, 5, 3, 3, 2, 2]
def baseStart_4183468 : Nat := 118140960795 + 4183468 * 2 ^ 59
def prefixEnd_4183468 : Nat := 4983230072969 + 3 ^ 40 * 4183468 * 2
def baseEnd_4183468 : Nat := 2148129886703543395910587

theorem tailTrace_4183468 : CollatzResearch.WordTrace tailWord_4183468 prefixEnd_4183468 2148129886703543395910587 := by
  unfold tailWord_4183468
  simp only [CollatzResearch.WordTrace]
  refine ⟨76291806604008695148447529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101722408805344926864596705 76291806604008695148447529)
  ·
    refine ⟨57218854953006521361335647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76291806604008695148447529 57218854953006521361335647)
    ·
      refine ⟨85828282429509782042003471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57218854953006521361335647 85828282429509782042003471)
      ·
        refine ⟨128742423644264673063005207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85828282429509782042003471 128742423644264673063005207)
        ·
          refine ⟨193113635466397009594507811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128742423644264673063005207 193113635466397009594507811)
          ·
            refine ⟨289670453199595514391761717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193113635466397009594507811 289670453199595514391761717)
            ·
              refine ⟨27156604987462079474227661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 289670453199595514391761717 27156604987462079474227661)
              ·
                refine ⟨10183726870298279802835373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27156604987462079474227661 10183726870298279802835373)
                ·
                  refine ⟨3818897576361854926063265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10183726870298279802835373 3818897576361854926063265)
                  ·
                    refine ⟨2864173182271391194547449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3818897576361854926063265 2864173182271391194547449)
                    ·
                      refine ⟨2148129886703543395910587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2864173182271391194547449 2148129886703543395910587)
                      ·
                        rfl

theorem cell23_4183468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 2, 2].length) (baseStart_4183468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183468 prefixEnd_4183468 := by exact prefixLift 4183468
  have htrace : WordTrace (prefixWord ++ tailWord_4183468) baseStart_4183468 baseEnd_4183468 := by
    simpa [prefixWord, tailWord_4183468, baseEnd_4183468] using wordTrace_append hprefix tailTrace_4183468
  have hstable : (prefixWord ++ tailWord_4183468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183468).length < 2 ^ (prefixWord ++ tailWord_4183468).sum := by decide
  have hdescent : baseEnd_4183468 < baseStart_4183468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183481 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 1, 1, 6]
def baseStart_4183481 : Nat := 118140960795 + 4183481 * 2 ^ 59
def prefixEnd_4183481 : Nat := 4983230072969 + 3 ^ 40 * 4183481 * 2
def baseEnd_4183481 : Nat := 2148136561952051845048027

theorem tailTrace_4183481 : CollatzResearch.WordTrace tailWord_4183481 prefixEnd_4183481 2148136561952051845048027 := by
  unfold tailWord_4183481
  simp only [CollatzResearch.WordTrace]
  refine ⟨152584087356970293517118297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101722724904646862344745531 152584087356970293517118297)
  ·
    refine ⟨114438065517727720137838723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152584087356970293517118297 114438065517727720137838723)
    ·
      refine ⟨171657098276591580206758085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114438065517727720137838723 171657098276591580206758085)
      ·
        refine ⟨32185705926860921288767141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171657098276591580206758085 32185705926860921288767141)
        ·
          refine ⟨6034819861286422741643839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32185705926860921288767141 6034819861286422741643839)
          ·
            refine ⟨9052229791929634112465759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6034819861286422741643839 9052229791929634112465759)
            ·
              refine ⟨13578344687894451168698639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9052229791929634112465759 13578344687894451168698639)
              ·
                refine ⟨20367517031841676753047959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13578344687894451168698639 20367517031841676753047959)
                ·
                  refine ⟨30551275547762515129571939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20367517031841676753047959 30551275547762515129571939)
                  ·
                    refine ⟨45826913321643772694357909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30551275547762515129571939 45826913321643772694357909)
                    ·
                      refine ⟨2148136561952051845048027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45826913321643772694357909 2148136561952051845048027)
                      ·
                        rfl

theorem cell23_4183481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_4183481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183481 prefixEnd_4183481 := by exact prefixLift 4183481
  have htrace : WordTrace (prefixWord ++ tailWord_4183481) baseStart_4183481 baseEnd_4183481 := by
    simpa [prefixWord, tailWord_4183481, baseEnd_4183481] using wordTrace_append hprefix tailTrace_4183481
  have hstable : (prefixWord ++ tailWord_4183481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183481).length < 2 ^ (prefixWord ++ tailWord_4183481).sum := by decide
  have hdescent : baseEnd_4183481 < baseStart_4183481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183502 : List Nat := [4, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2]
def baseStart_4183502 : Nat := 118140960795 + 4183502 * 2 ^ 59
def prefixEnd_4183502 : Nat := 4983230072969 + 3 ^ 40 * 4183502 * 2
def baseEnd_4183502 : Nat := 2148147345045796262885431

theorem tailTrace_4183502 : CollatzResearch.WordTrace tailWord_4183502 prefixEnd_4183502 2148147345045796262885431 := by
  unfold tailWord_4183502
  simp only [CollatzResearch.WordTrace]
  refine ⟨19073106661236776762954095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101723235526596142735755173 19073106661236776762954095)
  ·
    refine ⟨28609659991855165144431143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19073106661236776762954095 28609659991855165144431143)
    ·
      refine ⟨42914489987782747716646715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28609659991855165144431143 42914489987782747716646715)
      ·
        refine ⟨64371734981674121574970073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42914489987782747716646715 64371734981674121574970073)
        ·
          refine ⟨48278801236255591181227555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64371734981674121574970073 48278801236255591181227555)
          ·
            refine ⟨72418201854383386771841333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48278801236255591181227555 72418201854383386771841333)
            ·
              refine ⟨6789206423848442509860125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72418201854383386771841333 6789206423848442509860125)
              ·
                refine ⟨2545952408943165941197547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6789206423848442509860125 2545952408943165941197547)
                ·
                  refine ⟨3818928613414748911796321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2545952408943165941197547 3818928613414748911796321)
                  ·
                    refine ⟨2864196460061061683847241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3818928613414748911796321 2864196460061061683847241)
                    ·
                      refine ⟨2148147345045796262885431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2864196460061061683847241 2148147345045796262885431)
                      ·
                        rfl

theorem cell23_4183502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2].length) (baseStart_4183502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183502 prefixEnd_4183502 := by exact prefixLift 4183502
  have htrace : WordTrace (prefixWord ++ tailWord_4183502) baseStart_4183502 baseEnd_4183502 := by
    simpa [prefixWord, tailWord_4183502, baseEnd_4183502] using wordTrace_append hprefix tailTrace_4183502
  have hstable : (prefixWord ++ tailWord_4183502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183502).length < 2 ^ (prefixWord ++ tailWord_4183502).sum := by decide
  have hdescent : baseEnd_4183502 < baseStart_4183502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183508 : List Nat := [2, 4, 1, 2, 4, 1, 9]
def baseStart_4183508 : Nat := 118140960795 + 4183508 * 2 ^ 59
def prefixEnd_4183508 : Nat := 4983230072969 + 3 ^ 40 * 4183508 * 2
def baseEnd_4183508 : Nat := 26520375628762015301363

theorem tailTrace_4183508 : CollatzResearch.WordTrace tailWord_4183508 prefixEnd_4183508 26520375628762015301363 := by
  unfold tailWord_4183508
  simp only [CollatzResearch.WordTrace]
  refine ⟨76292536063936238564175589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101723381418581651418900785 76292536063936238564175589)
  ·
    refine ⟨14304850511988044730782923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76292536063936238564175589 14304850511988044730782923)
    ·
      refine ⟨21457275767982067096174385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14304850511988044730782923 21457275767982067096174385)
      ·
        refine ⟨16092956825986550322130789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21457275767982067096174385 16092956825986550322130789)
        ·
          refine ⟨3017429404872478185399523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16092956825986550322130789 3017429404872478185399523)
          ·
            refine ⟨4526144107308717278099285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3017429404872478185399523 4526144107308717278099285)
            ·
              refine ⟨26520375628762015301363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4526144107308717278099285 26520375628762015301363)
              ·
                rfl

theorem cell23_4183508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 9].length) (baseStart_4183508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183508 prefixEnd_4183508 := by exact prefixLift 4183508
  have htrace : WordTrace (prefixWord ++ tailWord_4183508) baseStart_4183508 baseEnd_4183508 := by
    simpa [prefixWord, tailWord_4183508, baseEnd_4183508] using wordTrace_append hprefix tailTrace_4183508
  have hstable : (prefixWord ++ tailWord_4183508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183508).length < 2 ^ (prefixWord ++ tailWord_4183508).sum := by decide
  have hdescent : baseEnd_4183508 < baseStart_4183508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183528 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 3, 3, 2]
def baseStart_4183528 : Nat := 118140960795 + 4183528 * 2 ^ 59
def prefixEnd_4183528 : Nat := 4983230072969 + 3 ^ 40 * 4183528 * 2
def baseEnd_4183528 : Nat := 2148160695542813161160311

theorem tailTrace_4183528 : CollatzResearch.WordTrace tailWord_4183528 prefixEnd_4183528 2148160695542813161160311 := by
  unfold tailWord_4183528
  simp only [CollatzResearch.WordTrace]
  refine ⟨76292900793900010272039619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101723867725200013696052825 76292900793900010272039619)
  ·
    refine ⟨114439351190850015408059429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76292900793900010272039619 114439351190850015408059429)
    ·
      refine ⟨21457378348284377889011143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114439351190850015408059429 21457378348284377889011143)
      ·
        refine ⟨32186067522426566833516715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21457378348284377889011143 32186067522426566833516715)
        ·
          refine ⟨48279101283639850250275073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32186067522426566833516715 48279101283639850250275073)
          ·
            refine ⟨36209325962729887687706305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48279101283639850250275073 36209325962729887687706305)
            ·
              refine ⟨27156994472047415765779729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36209325962729887687706305 27156994472047415765779729)
              ·
                refine ⟨20367745854035561824334797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27156994472047415765779729 20367745854035561824334797)
                ·
                  refine ⟨7637904695263335684125549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20367745854035561824334797 7637904695263335684125549)
                  ·
                    refine ⟨2864214260723750881547081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7637904695263335684125549 2864214260723750881547081)
                    ·
                      refine ⟨2148160695542813161160311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2864214260723750881547081 2148160695542813161160311)
                      ·
                        rfl

theorem cell23_4183528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_4183528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183528 prefixEnd_4183528 := by exact prefixLift 4183528
  have htrace : WordTrace (prefixWord ++ tailWord_4183528) baseStart_4183528 baseEnd_4183528 := by
    simpa [prefixWord, tailWord_4183528, baseEnd_4183528] using wordTrace_append hprefix tailTrace_4183528
  have hstable : (prefixWord ++ tailWord_4183528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183528).length < 2 ^ (prefixWord ++ tailWord_4183528).sum := by decide
  have hdescent : baseEnd_4183528 < baseStart_4183528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183535 : List Nat := [1, 1, 2, 1, 4, 1, 6, 1, 2, 1, 3]
def baseStart_4183535 : Nat := 118140960795 + 4183535 * 2 ^ 59
def prefixEnd_4183535 : Nat := 4983230072969 + 3 ^ 40 * 4183535 * 2
def baseEnd_4183535 : Nat := 2148164289907394633772779

theorem tailTrace_4183535 : CollatzResearch.WordTrace tailWord_4183535 prefixEnd_4183535 2148164289907394633772779 := by
  unfold tailWord_4183535
  simp only [CollatzResearch.WordTrace]
  refine ⟨152586056898774660739584059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101724037932516440493056039 152586056898774660739584059)
  ·
    refine ⟨228879085348161991109376089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152586056898774660739584059 228879085348161991109376089)
    ·
      refine ⟨171659314011121493332032067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228879085348161991109376089 171659314011121493332032067)
      ·
        refine ⟨257488971016682239998048101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171659314011121493332032067 257488971016682239998048101)
        ·
          refine ⟨48279182065627919999634019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257488971016682239998048101 48279182065627919999634019)
          ·
            refine ⟨72418773098441879999451029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48279182065627919999634019 72418773098441879999451029)
            ·
              refine ⟨3394629988989463124974267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72418773098441879999451029 3394629988989463124974267)
              ·
                refine ⟨5091944983484194687461401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3394629988989463124974267 5091944983484194687461401)
                ·
                  refine ⟨3818958737613146015596051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5091944983484194687461401 3818958737613146015596051)
                  ·
                    refine ⟨5728438106419719023394077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3818958737613146015596051 5728438106419719023394077)
                    ·
                      refine ⟨2148164289907394633772779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5728438106419719023394077 2148164289907394633772779)
                      ·
                        rfl

theorem cell23_4183535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 2, 1, 3].length) (baseStart_4183535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183535 prefixEnd_4183535 := by exact prefixLift 4183535
  have htrace : WordTrace (prefixWord ++ tailWord_4183535) baseStart_4183535 baseEnd_4183535 := by
    simpa [prefixWord, tailWord_4183535, baseEnd_4183535] using wordTrace_append hprefix tailTrace_4183535
  have hstable : (prefixWord ++ tailWord_4183535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183535).length < 2 ^ (prefixWord ++ tailWord_4183535).sum := by decide
  have hdescent : baseEnd_4183535 < baseStart_4183535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183562 : List Nat := [3, 1, 2, 2, 2, 3, 3, 1, 1, 3, 2]
def baseStart_4183562 : Nat := 118140960795 + 4183562 * 2 ^ 59
def prefixEnd_4183562 : Nat := 4983230072969 + 3 ^ 40 * 4183562 * 2
def baseEnd_4183562 : Nat := 2148178153885066028135155

theorem tailTrace_4183562 : CollatzResearch.WordTrace tailWord_4183562 prefixEnd_4183562 2148178153885066028135155 := by
  unfold tailWord_4183562
  simp only [CollatzResearch.WordTrace]
  refine ⟨38146760417419211087704235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101724694446451229567211293 38146760417419211087704235)
  ·
    refine ⟨57220140626128816631556353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38146760417419211087704235 57220140626128816631556353)
    ·
      refine ⟨42915105469596612473667265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57220140626128816631556353 42915105469596612473667265)
      ·
        refine ⟨32186329102197459355250449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42915105469596612473667265 32186329102197459355250449)
        ·
          refine ⟨24139746826648094516437837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32186329102197459355250449 24139746826648094516437837)
          ·
            refine ⟨9052405059993035443664189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24139746826648094516437837 9052405059993035443664189)
            ·
              refine ⟨3394651897497388291374071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9052405059993035443664189 3394651897497388291374071)
              ·
                refine ⟨5091977846246082437061107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3394651897497388291374071 5091977846246082437061107)
                ·
                  refine ⟨7637966769369123655591661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5091977846246082437061107 7637966769369123655591661)
                  ·
                    refine ⟨2864237538513421370846873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7637966769369123655591661 2864237538513421370846873)
                    ·
                      refine ⟨2148178153885066028135155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2864237538513421370846873 2148178153885066028135155)
                      ·
                        rfl

theorem cell23_4183562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_4183562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183562 prefixEnd_4183562 := by exact prefixLift 4183562
  have htrace : WordTrace (prefixWord ++ tailWord_4183562) baseStart_4183562 baseEnd_4183562 := by
    simpa [prefixWord, tailWord_4183562, baseEnd_4183562] using wordTrace_append hprefix tailTrace_4183562
  have hstable : (prefixWord ++ tailWord_4183562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183562).length < 2 ^ (prefixWord ++ tailWord_4183562).sum := by decide
  have hdescent : baseEnd_4183562 < baseStart_4183562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183581 : List Nat := [1, 4, 2, 2, 1, 1, 2, 3, 7]
def baseStart_4183581 : Nat := 118140960795 + 4183581 * 2 ^ 59
def prefixEnd_4183581 : Nat := 4983230072969 + 3 ^ 40 * 4183581 * 2
def baseEnd_4183581 : Nat := 238687545557500161533063

theorem tailTrace_4183581 : CollatzResearch.WordTrace tailWord_4183581 prefixEnd_4183581 238687545557500161533063 := by
  unfold tailWord_4183581
  simp only [CollatzResearch.WordTrace]
  refine ⟨152587734656608010595758597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101725156437738673730505731 152587734656608010595758597)
  ·
    refine ⟨28610200248114001986704737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152587734656608010595758597 28610200248114001986704737)
    ·
      refine ⟨21457650186085501490028553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28610200248114001986704737 21457650186085501490028553)
      ·
        refine ⟨16093237639564126117521415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21457650186085501490028553 16093237639564126117521415)
        ·
          refine ⟨24139856459346189176282123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16093237639564126117521415 24139856459346189176282123)
          ·
            refine ⟨36209784689019283764423185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24139856459346189176282123 36209784689019283764423185)
            ·
              refine ⟨27157338516764462823317389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36209784689019283764423185 27157338516764462823317389)
              ·
                refine ⟨10184001943786673558744021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27157338516764462823317389 10184001943786673558744021)
                ·
                  refine ⟨238687545557500161533063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10184001943786673558744021 238687545557500161533063)
                  ·
                    rfl

theorem cell23_4183581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_4183581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183581 prefixEnd_4183581 := by exact prefixLift 4183581
  have htrace : WordTrace (prefixWord ++ tailWord_4183581) baseStart_4183581 baseEnd_4183581 := by
    simpa [prefixWord, tailWord_4183581, baseEnd_4183581] using wordTrace_append hprefix tailTrace_4183581
  have hstable : (prefixWord ++ tailWord_4183581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183581).length < 2 ^ (prefixWord ++ tailWord_4183581).sum := by decide
  have hdescent : baseEnd_4183581 < baseStart_4183581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183592 : List Nat := [2, 1, 5, 2, 2, 1, 2, 1, 1, 4, 2]
def baseStart_4183592 : Nat := 118140960795 + 4183592 * 2 ^ 59
def prefixEnd_4183592 : Nat := 4983230072969 + 3 ^ 40 * 4183592 * 2
def baseEnd_4183592 : Nat := 2148193558304700910760017

theorem tailTrace_4183592 : CollatzResearch.WordTrace tailWord_4183592 prefixEnd_4183592 2148193558304700910760017 := by
  unfold tailWord_4183592
  simp only [CollatzResearch.WordTrace]
  refine ⟨76294067929784079737204515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101725423906378772982939353 76294067929784079737204515)
  ·
    refine ⟨114441101894676119605806773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76294067929784079737204515 114441101894676119605806773)
    ·
      refine ⟨10728853302625886213044385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114441101894676119605806773 10728853302625886213044385)
      ·
        refine ⟨8046639976969414659783289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10728853302625886213044385 8046639976969414659783289)
        ·
          refine ⟨6034979982727060994837467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8046639976969414659783289 6034979982727060994837467)
          ·
            refine ⟨9052469974090591492256201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6034979982727060994837467 9052469974090591492256201)
            ·
              refine ⟨6789352480567943619192151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9052469974090591492256201 6789352480567943619192151)
              ·
                refine ⟨10184028720851915428788227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6789352480567943619192151 10184028720851915428788227)
                ·
                  refine ⟨15276043081277873143182341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10184028720851915428788227 15276043081277873143182341)
                  ·
                    refine ⟨2864258077739601214346689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15276043081277873143182341 2864258077739601214346689)
                    ·
                      refine ⟨2148193558304700910760017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2864258077739601214346689 2148193558304700910760017)
                      ·
                        rfl

theorem cell23_4183592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_4183592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183592 prefixEnd_4183592 := by exact prefixLift 4183592
  have htrace : WordTrace (prefixWord ++ tailWord_4183592) baseStart_4183592 baseEnd_4183592 := by
    simpa [prefixWord, tailWord_4183592, baseEnd_4183592] using wordTrace_append hprefix tailTrace_4183592
  have hstable : (prefixWord ++ tailWord_4183592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183592).length < 2 ^ (prefixWord ++ tailWord_4183592).sum := by decide
  have hdescent : baseEnd_4183592 < baseStart_4183592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183598 : List Nat := [4, 1, 3, 1, 2, 2, 1, 2, 7]
def baseStart_4183598 : Nat := 118140960795 + 4183598 * 2 ^ 59
def prefixEnd_4183598 : Nat := 4983230072969 + 3 ^ 40 * 4183598 * 2
def baseEnd_4183598 : Nat := 238688515465403098587221

theorem tailTrace_4183598 : CollatzResearch.WordTrace tailWord_4183598 prefixEnd_4183598 238688515465403098587221 := by
  unfold tailWord_4183598
  simp only [CollatzResearch.WordTrace]
  refine ⟨19073544337193302812390931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101725569798364281666084965 19073544337193302812390931)
  ·
    refine ⟨28610316505789954218586397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19073544337193302812390931 28610316505789954218586397)
    ·
      refine ⟨10728868689671232831969899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28610316505789954218586397 10728868689671232831969899)
      ·
        refine ⟨16093303034506849247954849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10728868689671232831969899 16093303034506849247954849)
        ·
          refine ⟨12069977275880136935966137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16093303034506849247954849 12069977275880136935966137)
          ·
            refine ⟨9052482956910102701974603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12069977275880136935966137 9052482956910102701974603)
            ·
              refine ⟨13578724435365154052961905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9052482956910102701974603 13578724435365154052961905)
              ·
                refine ⟨10184043326523865539721429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13578724435365154052961905 10184043326523865539721429)
                ·
                  refine ⟨238688515465403098587221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10184043326523865539721429 238688515465403098587221)
                  ·
                    rfl

theorem cell23_4183598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_4183598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183598 prefixEnd_4183598 := by exact prefixLift 4183598
  have htrace : WordTrace (prefixWord ++ tailWord_4183598) baseStart_4183598 baseEnd_4183598 := by
    simpa [prefixWord, tailWord_4183598, baseEnd_4183598] using wordTrace_append hprefix tailTrace_4183598
  have hstable : (prefixWord ++ tailWord_4183598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183598).length < 2 ^ (prefixWord ++ tailWord_4183598).sum := by decide
  have hdescent : baseEnd_4183598 < baseStart_4183598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183631 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 4]
def baseStart_4183631 : Nat := 118140960795 + 4183631 * 2 ^ 59
def prefixEnd_4183631 : Nat := 4983230072969 + 3 ^ 40 * 4183631 * 2
def baseEnd_4183631 : Nat := 2148213584050226258172337

theorem tailTrace_4183631 : CollatzResearch.WordTrace tailWord_4183631 prefixEnd_4183631 2148213584050226258172337 := by
  unfold tailWord_4183631
  simp only [CollatzResearch.WordTrace]
  refine ⟨152589558306426869135078747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101726372204284579423385831 152589558306426869135078747)
  ·
    refine ⟨228884337459640303702618121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152589558306426869135078747 228884337459640303702618121)
    ·
      refine ⟨171663253094730227776963591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228884337459640303702618121 171663253094730227776963591)
      ·
        refine ⟨257494879642095341665445387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171663253094730227776963591 257494879642095341665445387)
        ·
          refine ⟨386242319463143012498168081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257494879642095341665445387 386242319463143012498168081)
          ·
            refine ⟨289681739597357259373626061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386242319463143012498168081 289681739597357259373626061)
            ·
              refine ⟨108630652349008972265109773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289681739597357259373626061 108630652349008972265109773)
              ·
                refine ⟨40736494630878364599416165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108630652349008972265109773 40736494630878364599416165)
                ·
                  refine ⟨7638092743289693362390531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40736494630878364599416165 7638092743289693362390531)
                  ·
                    refine ⟨11457139114934540043585797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7638092743289693362390531 11457139114934540043585797)
                    ·
                      refine ⟨2148213584050226258172337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11457139114934540043585797 2148213584050226258172337)
                      ·
                        rfl

theorem cell23_4183631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 4].length) (baseStart_4183631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183631 prefixEnd_4183631 := by exact prefixLift 4183631
  have htrace : WordTrace (prefixWord ++ tailWord_4183631) baseStart_4183631 baseEnd_4183631 := by
    simpa [prefixWord, tailWord_4183631, baseEnd_4183631] using wordTrace_append hprefix tailTrace_4183631
  have hstable : (prefixWord ++ tailWord_4183631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183631).length < 2 ^ (prefixWord ++ tailWord_4183631).sum := by decide
  have hdescent : baseEnd_4183631 < baseStart_4183631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183692 : List Nat := [2, 2, 1, 2, 1, 1, 7, 2, 1, 4]
def baseStart_4183692 : Nat := 118140960795 + 4183692 * 2 ^ 59
def prefixEnd_4183692 : Nat := 4983230072969 + 3 ^ 40 * 4183692 * 2
def baseEnd_4183692 : Nat := 716081635456716839836519

theorem tailTrace_4183692 : CollatzResearch.WordTrace tailWord_4183692 prefixEnd_4183692 716081635456716839836519 := by
  unfold tailWord_4183692
  simp only [CollatzResearch.WordTrace]
  refine ⟨76295891579602938276524665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101727855439470584368699553 76295891579602938276524665)
  ·
    refine ⟨57221918684702203707393499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76295891579602938276524665 57221918684702203707393499)
    ·
      refine ⟨85832878027053305561090249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57221918684702203707393499 85832878027053305561090249)
      ·
        refine ⟨64374658520289979170817687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85832878027053305561090249 64374658520289979170817687)
        ·
          refine ⟨96561987780434968756226531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64374658520289979170817687 96561987780434968756226531)
          ·
            refine ⟨144842981670652453134339797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96561987780434968756226531 144842981670652453134339797)
            ·
              refine ⟨3394757382905916870336089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 144842981670652453134339797 3394757382905916870336089)
              ·
                refine ⟨2546068037179437652752067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3394757382905916870336089 2546068037179437652752067)
                ·
                  refine ⟨3819102055769156479128101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2546068037179437652752067 3819102055769156479128101)
                  ·
                    refine ⟨716081635456716839836519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3819102055769156479128101 716081635456716839836519)
                    ·
                      rfl

theorem cell23_4183692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 1, 4].length) (baseStart_4183692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183692 prefixEnd_4183692 := by exact prefixLift 4183692
  have htrace : WordTrace (prefixWord ++ tailWord_4183692) baseStart_4183692 baseEnd_4183692 := by
    simpa [prefixWord, tailWord_4183692, baseEnd_4183692] using wordTrace_append hprefix tailTrace_4183692
  have hstable : (prefixWord ++ tailWord_4183692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183692).length < 2 ^ (prefixWord ++ tailWord_4183692).sum := by decide
  have hdescent : baseEnd_4183692 < baseStart_4183692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183742 : List Nat := [4, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2]
def baseStart_4183742 : Nat := 118140960795 + 4183742 * 2 ^ 59
def prefixEnd_4183742 : Nat := 4983230072969 + 3 ^ 40 * 4183742 * 2
def baseEnd_4183742 : Nat := 2148270580402875323884327

theorem tailTrace_4183742 : CollatzResearch.WordTrace tailWord_4183742 prefixEnd_4183742 2148270580402875323884327 := by
  unfold tailWord_4183742
  simp only [CollatzResearch.WordTrace]
  refine ⟨19074200851128091886546185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101729071206016490061579653 19074200851128091886546185)
  ·
    refine ⟨14305650638346068914909639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19074200851128091886546185 14305650638346068914909639)
    ·
      refine ⟨21458475957519103372364459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14305650638346068914909639 21458475957519103372364459)
      ·
        refine ⟨32187713936278655058546689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21458475957519103372364459 32187713936278655058546689)
        ·
          refine ⟨24140785452208991293910017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32187713936278655058546689 24140785452208991293910017)
          ·
            refine ⟨18105589089156743470432513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24140785452208991293910017 18105589089156743470432513)
            ·
              refine ⟨13579191816867557602824385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18105589089156743470432513 13579191816867557602824385)
              ·
                refine ⟨10184393862650668202118289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13579191816867557602824385 10184393862650668202118289)
                ·
                  refine ⟨7638295396988001151588717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10184393862650668202118289 7638295396988001151588717)
                  ·
                    refine ⟨2864360773870500431845769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7638295396988001151588717 2864360773870500431845769)
                    ·
                      refine ⟨2148270580402875323884327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2864360773870500431845769 2148270580402875323884327)
                      ·
                        rfl

theorem cell23_4183742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_4183742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183742 prefixEnd_4183742 := by exact prefixLift 4183742
  have htrace : WordTrace (prefixWord ++ tailWord_4183742) baseStart_4183742 baseEnd_4183742 := by
    simpa [prefixWord, tailWord_4183742, baseEnd_4183742] using wordTrace_append hprefix tailTrace_4183742
  have hstable : (prefixWord ++ tailWord_4183742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183742).length < 2 ^ (prefixWord ++ tailWord_4183742).sum := by decide
  have hdescent : baseEnd_4183742 < baseStart_4183742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183748 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 3, 6]
def baseStart_4183748 : Nat := 118140960795 + 4183748 * 2 ^ 59
def prefixEnd_4183748 : Nat := 4983230072969 + 3 ^ 40 * 4183748 * 2
def baseEnd_4183748 : Nat := 716091220428934100136433

theorem tailTrace_4183748 : CollatzResearch.WordTrace tailWord_4183748 prefixEnd_4183748 716091220428934100136433 := by
  unfold tailWord_4183748
  simp only [CollatzResearch.WordTrace]
  refine ⟨76296912823501499058543949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101729217098001998744725265 76296912823501499058543949)
  ·
    refine ⟨28611342308813062146953981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76296912823501499058543949 28611342308813062146953981)
    ·
      refine ⟨10729253365804898305107743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28611342308813062146953981 10729253365804898305107743)
      ·
        refine ⟨16093880048707347457661615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10729253365804898305107743 16093880048707347457661615)
        ·
          refine ⟨24140820073061021186492423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16093880048707347457661615 24140820073061021186492423)
          ·
            refine ⟨36211230109591531779738635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24140820073061021186492423 36211230109591531779738635)
            ·
              refine ⟨54316845164387297669607953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36211230109591531779738635 54316845164387297669607953)
              ·
                refine ⟨40737633873290473252205965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54316845164387297669607953 40737633873290473252205965)
                ·
                  refine ⟨15276612702483927469577237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40737633873290473252205965 15276612702483927469577237)
                  ·
                    refine ⟨716091220428934100136433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15276612702483927469577237 716091220428934100136433)
                    ·
                      rfl

theorem cell23_4183748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_4183748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183748 prefixEnd_4183748 := by exact prefixLift 4183748
  have htrace : WordTrace (prefixWord ++ tailWord_4183748) baseStart_4183748 baseEnd_4183748 := by
    simpa [prefixWord, tailWord_4183748, baseEnd_4183748] using wordTrace_append hprefix tailTrace_4183748
  have hstable : (prefixWord ++ tailWord_4183748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183748).length < 2 ^ (prefixWord ++ tailWord_4183748).sum := by decide
  have hdescent : baseEnd_4183748 < baseStart_4183748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183755 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 7, 2, 2]
def baseStart_4183755 : Nat := 118140960795 + 4183755 * 2 ^ 59
def prefixEnd_4183755 : Nat := 4983230072969 + 3 ^ 40 * 4183755 * 2
def baseEnd_4183755 : Nat := 2148277255651383773021767

theorem tailTrace_4183755 : CollatzResearch.WordTrace tailWord_4183755 prefixEnd_4183755 2148277255651383773021767 := by
  unfold tailWord_4183755
  simp only [CollatzResearch.WordTrace]
  refine ⟨152594080957977638312592719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101729387305318425541728479 152594080957977638312592719)
  ·
    refine ⟨228891121436966457468889079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152594080957977638312592719 228891121436966457468889079)
    ·
      refine ⟨343336682155449686203333619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228891121436966457468889079 343336682155449686203333619)
      ·
        refine ⟨515005023233174529305000429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343336682155449686203333619 515005023233174529305000429)
        ·
          refine ⟨193126883712440448489375161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 515005023233174529305000429 193126883712440448489375161)
          ·
            refine ⟨144845162784330336367031371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193126883712440448489375161 144845162784330336367031371)
            ·
              refine ⟨217267744176495504550547057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144845162784330336367031371 217267744176495504550547057)
              ·
                refine ⟨162950808132371628412910293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217267744176495504550547057 162950808132371628412910293)
                ·
                  refine ⟨3819159565602460040927585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 162950808132371628412910293 3819159565602460040927585)
                  ·
                    refine ⟨2864369674201845030695689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3819159565602460040927585 2864369674201845030695689)
                    ·
                      refine ⟨2148277255651383773021767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2864369674201845030695689 2148277255651383773021767)
                      ·
                        rfl

theorem cell23_4183755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 2, 2].length) (baseStart_4183755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183755 prefixEnd_4183755 := by exact prefixLift 4183755
  have htrace : WordTrace (prefixWord ++ tailWord_4183755) baseStart_4183755 baseEnd_4183755 := by
    simpa [prefixWord, tailWord_4183755, baseEnd_4183755] using wordTrace_append hprefix tailTrace_4183755
  have hstable : (prefixWord ++ tailWord_4183755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183755).length < 2 ^ (prefixWord ++ tailWord_4183755).sum := by decide
  have hdescent : baseEnd_4183755 < baseStart_4183755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183758 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5]
def baseStart_4183758 : Nat := 118140960795 + 4183758 * 2 ^ 59
def prefixEnd_4183758 : Nat := 4983230072969 + 3 ^ 40 * 4183758 * 2
def baseEnd_4183758 : Nat := 2148278796093347261284253

theorem tailTrace_4183758 : CollatzResearch.WordTrace tailWord_4183758 prefixEnd_4183758 2148278796093347261284253 := by
  unfold tailWord_4183758
  simp only [CollatzResearch.WordTrace]
  refine ⟨19074273797120846228118991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101729460251311179883301285 19074273797120846228118991)
  ·
    refine ⟨28611410695681269342178487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19074273797120846228118991 28611410695681269342178487)
    ·
      refine ⟨42917116043521904013267731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28611410695681269342178487 42917116043521904013267731)
      ·
        refine ⟨64375674065282856019901597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42917116043521904013267731 64375674065282856019901597)
        ·
          refine ⟨24140877774481071007463099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64375674065282856019901597 24140877774481071007463099)
          ·
            refine ⟨36211316661721606511194649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24140877774481071007463099 36211316661721606511194649)
            ·
              refine ⟨27158487496291204883395987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36211316661721606511194649 27158487496291204883395987)
              ·
                refine ⟨40737731244436807325093981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27158487496291204883395987 40737731244436807325093981)
                ·
                  refine ⟨15276649216663802746910243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40737731244436807325093981 15276649216663802746910243)
                  ·
                    refine ⟨22914973824995704120365365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15276649216663802746910243 22914973824995704120365365)
                    ·
                      refine ⟨2148278796093347261284253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22914973824995704120365365 2148278796093347261284253)
                      ·
                        rfl

theorem cell23_4183758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_4183758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183758 prefixEnd_4183758 := by exact prefixLift 4183758
  have htrace : WordTrace (prefixWord ++ tailWord_4183758) baseStart_4183758 baseEnd_4183758 := by
    simpa [prefixWord, tailWord_4183758, baseEnd_4183758] using wordTrace_append hprefix tailTrace_4183758
  have hstable : (prefixWord ++ tailWord_4183758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183758).length < 2 ^ (prefixWord ++ tailWord_4183758).sum := by decide
  have hdescent : baseEnd_4183758 < baseStart_4183758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183766 : List Nat := [5, 2, 1, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_4183766 : Nat := 118140960795 + 4183766 * 2 ^ 59
def prefixEnd_4183766 : Nat := 4983230072969 + 3 ^ 40 * 4183766 * 2
def baseEnd_4183766 : Nat := 2148282903938583229984217

theorem tailTrace_4183766 : CollatzResearch.WordTrace tailWord_4183766 prefixEnd_4183766 2148282903938583229984217 := by
  unfold tailWord_4183766
  simp only [CollatzResearch.WordTrace]
  refine ⟨9537155135058611699452697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101729654773958524794162101 9537155135058611699452697)
  ·
    refine ⟨7152866351293958774589523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9537155135058611699452697 7152866351293958774589523)
    ·
      refine ⟨10729299526940938161884285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7152866351293958774589523 10729299526940938161884285)
      ·
        refine ⟨4023487322602851810706607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10729299526940938161884285 4023487322602851810706607)
        ·
          refine ⟨6035230983904277716059911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4023487322602851810706607 6035230983904277716059911)
          ·
            refine ⟨9052846475856416574089867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6035230983904277716059911 9052846475856416574089867)
            ·
              refine ⟨13579269713784624861134801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9052846475856416574089867 13579269713784624861134801)
              ·
                refine ⟨10184452285338468645851101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13579269713784624861134801 10184452285338468645851101)
                ·
                  refine ⟨3819169607001925742194163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10184452285338468645851101 3819169607001925742194163)
                  ·
                    refine ⟨5728754410502888613291245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3819169607001925742194163 5728754410502888613291245)
                    ·
                      refine ⟨2148282903938583229984217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5728754410502888613291245 2148282903938583229984217)
                      ·
                        rfl

theorem cell23_4183766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_4183766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183766 prefixEnd_4183766 := by exact prefixLift 4183766
  have htrace : WordTrace (prefixWord ++ tailWord_4183766) baseStart_4183766 baseEnd_4183766 := by
    simpa [prefixWord, tailWord_4183766, baseEnd_4183766] using wordTrace_append hprefix tailTrace_4183766
  have hstable : (prefixWord ++ tailWord_4183766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183766).length < 2 ^ (prefixWord ++ tailWord_4183766).sum := by decide
  have hdescent : baseEnd_4183766 < baseStart_4183766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183775 : List Nat := [1, 1, 2, 3, 2, 2, 2, 4, 1, 2, 3]
def baseStart_4183775 : Nat := 118140960795 + 4183775 * 2 ^ 59
def prefixEnd_4183775 : Nat := 4983230072969 + 3 ^ 40 * 4183775 * 2
def baseEnd_4183775 : Nat := 2148287525264473694771675

theorem tailTrace_4183775 : CollatzResearch.WordTrace tailWord_4183775 prefixEnd_4183775 2148287525264473694771675 := by
  unfold tailWord_4183775
  simp only [CollatzResearch.WordTrace]
  refine ⟨152594810417905181728320779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101729873611936787818880519 152594810417905181728320779)
  ·
    refine ⟨228892215626857772592481169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152594810417905181728320779 228892215626857772592481169)
    ·
      refine ⟨171669161720143329444360877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228892215626857772592481169 171669161720143329444360877)
      ·
        refine ⟨64375935645053748541635329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171669161720143329444360877 64375935645053748541635329)
        ·
          refine ⟨48281951733790311406226497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64375935645053748541635329 48281951733790311406226497)
          ·
            refine ⟨36211463800342733554669873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48281951733790311406226497 36211463800342733554669873)
            ·
              refine ⟨27158597850257050166002405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36211463800342733554669873 27158597850257050166002405)
              ·
                refine ⟨5092237096923196906125451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27158597850257050166002405 5092237096923196906125451)
                ·
                  refine ⟨7638355645384795359188177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5092237096923196906125451 7638355645384795359188177)
                  ·
                    refine ⟨5728766734038596519391133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7638355645384795359188177 5728766734038596519391133)
                    ·
                      refine ⟨2148287525264473694771675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5728766734038596519391133 2148287525264473694771675)
                      ·
                        rfl

theorem cell23_4183775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_4183775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183775 prefixEnd_4183775 := by exact prefixLift 4183775
  have htrace : WordTrace (prefixWord ++ tailWord_4183775) baseStart_4183775 baseEnd_4183775 := by
    simpa [prefixWord, tailWord_4183775, baseEnd_4183775] using wordTrace_append hprefix tailTrace_4183775
  have hstable : (prefixWord ++ tailWord_4183775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183775).length < 2 ^ (prefixWord ++ tailWord_4183775).sum := by decide
  have hdescent : baseEnd_4183775 < baseStart_4183775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183789 : List Nat := [1, 5, 1, 2, 1, 4, 2, 1, 1, 1, 4]
def baseStart_4183789 : Nat := 118140960795 + 4183789 * 2 ^ 59
def prefixEnd_4183789 : Nat := 4983230072969 + 3 ^ 40 * 4183789 * 2
def baseEnd_4183789 : Nat := 2148294713993636639996611

theorem tailTrace_4183789 : CollatzResearch.WordTrace tailWord_4183789 prefixEnd_4183789 2148294713993636639996611 := by
  unfold tailWord_4183789
  simp only [CollatzResearch.WordTrace]
  refine ⟨152595321039854462119330421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101730214026569641412886947 152595321039854462119330421)
  ·
    refine ⟨14305811347486355823687227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152595321039854462119330421 14305811347486355823687227)
    ·
      refine ⟨21458717021229533735530841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14305811347486355823687227 21458717021229533735530841)
      ·
        refine ⟨16094037765922150301648131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21458717021229533735530841 16094037765922150301648131)
        ·
          refine ⟨24141056648883225452472197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16094037765922150301648131 24141056648883225452472197)
          ·
            refine ⟨4526448121665604772338537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24141056648883225452472197 4526448121665604772338537)
            ·
              refine ⟨3394836091249203579253903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4526448121665604772338537 3394836091249203579253903)
              ·
                refine ⟨5092254136873805368880855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3394836091249203579253903 5092254136873805368880855)
                ·
                  refine ⟨7638381205310708053321283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5092254136873805368880855 7638381205310708053321283)
                  ·
                    refine ⟨11457571807966062079981925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7638381205310708053321283 11457571807966062079981925)
                    ·
                      refine ⟨2148294713993636639996611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11457571807966062079981925 2148294713993636639996611)
                      ·
                        rfl

theorem cell23_4183789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_4183789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183789 prefixEnd_4183789 := by exact prefixLift 4183789
  have htrace : WordTrace (prefixWord ++ tailWord_4183789) baseStart_4183789 baseEnd_4183789 := by
    simpa [prefixWord, tailWord_4183789, baseEnd_4183789] using wordTrace_append hprefix tailTrace_4183789
  have hstable : (prefixWord ++ tailWord_4183789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183789).length < 2 ^ (prefixWord ++ tailWord_4183789).sum := by decide
  have hdescent : baseEnd_4183789 < baseStart_4183789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183806 : List Nat := [4, 2, 2, 1, 3, 1, 2, 1, 3, 2, 2]
def baseStart_4183806 : Nat := 118140960795 + 4183806 * 2 ^ 59
def prefixEnd_4183806 : Nat := 4983230072969 + 3 ^ 40 * 4183806 * 2
def baseEnd_4183806 : Nat := 2148303443164763073484033

theorem tailTrace_4183806 : CollatzResearch.WordTrace tailWord_4183806 prefixEnd_4183806 2148303443164763073484033 := by
  unfold tailWord_4183806
  simp only [CollatzResearch.WordTrace]
  refine ⟨19074492635099109252837409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101730627387195249348466181 19074492635099109252837409)
  ·
    refine ⟨14305869476324331939628057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19074492635099109252837409 14305869476324331939628057)
    ·
      refine ⟨10729402107243248954721043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14305869476324331939628057 10729402107243248954721043)
      ·
        refine ⟨16094103160864873432081565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10729402107243248954721043 16094103160864873432081565)
        ·
          refine ⟨6035288685324327537030587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16094103160864873432081565 6035288685324327537030587)
          ·
            refine ⟨9052933027986491305545881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6035288685324327537030587 9052933027986491305545881)
            ·
              refine ⟨6789699770989868479159411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9052933027986491305545881 6789699770989868479159411)
              ·
                refine ⟨10184549656484802718739117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6789699770989868479159411 10184549656484802718739117)
                ·
                  refine ⟨3819206121181801019527169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10184549656484802718739117 3819206121181801019527169)
                  ·
                    refine ⟨2864404590886350764645377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3819206121181801019527169 2864404590886350764645377)
                    ·
                      refine ⟨2148303443164763073484033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2864404590886350764645377 2148303443164763073484033)
                      ·
                        rfl

theorem cell23_4183806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_4183806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183806 prefixEnd_4183806 := by exact prefixLift 4183806
  have htrace : WordTrace (prefixWord ++ tailWord_4183806) baseStart_4183806 baseEnd_4183806 := by
    simpa [prefixWord, tailWord_4183806, baseEnd_4183806] using wordTrace_append hprefix tailTrace_4183806
  have hstable : (prefixWord ++ tailWord_4183806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183806).length < 2 ^ (prefixWord ++ tailWord_4183806).sum := by decide
  have hdescent : baseEnd_4183806 < baseStart_4183806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183822 : List Nat := [4, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3]
def baseStart_4183822 : Nat := 118140960795 + 4183822 * 2 ^ 59
def prefixEnd_4183822 : Nat := 4983230072969 + 3 ^ 40 * 4183822 * 2
def baseEnd_4183822 : Nat := 2148311658855235010883959

theorem tailTrace_4183822 : CollatzResearch.WordTrace tailWord_4183822 prefixEnd_4183822 2148311658855235010883959 := by
  unfold tailWord_4183822
  simp only [CollatzResearch.WordTrace]
  refine ⟨19074565581091863594410215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101731016432489939170187813 19074565581091863594410215)
  ·
    refine ⟨28611848371637795391615323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19074565581091863594410215 28611848371637795391615323)
    ·
      refine ⟨42917772557456693087422985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28611848371637795391615323 42917772557456693087422985)
      ·
        refine ⟨32188329418092519815567239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42917772557456693087422985 32188329418092519815567239)
        ·
          refine ⟨48282494127138779723350859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32188329418092519815567239 48282494127138779723350859)
          ·
            refine ⟨72423741190708169585026289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48282494127138779723350859 72423741190708169585026289)
            ·
              refine ⟨54317805893031127188769717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72423741190708169585026289 54317805893031127188769717)
              ·
                refine ⟨5092294302471668173947161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54317805893031127188769717 5092294302471668173947161)
                ·
                  refine ⟨3819220726853751130460371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5092294302471668173947161 3819220726853751130460371)
                  ·
                    refine ⟨5728831090280626695690557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3819220726853751130460371 5728831090280626695690557)
                    ·
                      refine ⟨2148311658855235010883959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5728831090280626695690557 2148311658855235010883959)
                      ·
                        rfl

theorem cell23_4183822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_4183822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183822 prefixEnd_4183822 := by exact prefixLift 4183822
  have htrace : WordTrace (prefixWord ++ tailWord_4183822) baseStart_4183822 baseEnd_4183822 := by
    simpa [prefixWord, tailWord_4183822, baseEnd_4183822] using wordTrace_append hprefix tailTrace_4183822
  have hstable : (prefixWord ++ tailWord_4183822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183822).length < 2 ^ (prefixWord ++ tailWord_4183822).sum := by decide
  have hdescent : baseEnd_4183822 < baseStart_4183822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183832 : List Nat := [2, 1, 2, 3, 1, 1, 3, 4, 1, 3, 2]
def baseStart_4183832 : Nat := 118140960795 + 4183832 * 2 ^ 59
def prefixEnd_4183832 : Nat := 4983230072969 + 3 ^ 40 * 4183832 * 2
def baseEnd_4183832 : Nat := 2148316793661779971758913

theorem tailTrace_4183832 : CollatzResearch.WordTrace tailWord_4183832 prefixEnd_4183832 2148316793661779971758913 := by
  unfold tailWord_4183832
  simp only [CollatzResearch.WordTrace]
  refine ⟨76298444689349340231572875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101731259585799120308763833 76298444689349340231572875)
  ·
    refine ⟨114447667034024010347359313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76298444689349340231572875 114447667034024010347359313)
    ·
      refine ⟨85835750275518007760519485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114447667034024010347359313 85835750275518007760519485)
      ·
        refine ⟨32188406353319252910194807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85835750275518007760519485 32188406353319252910194807)
        ·
          refine ⟨48282609529978879365292211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32188406353319252910194807 48282609529978879365292211)
          ·
            refine ⟨72423914294968319047938317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48282609529978879365292211 72423914294968319047938317)
            ·
              refine ⟨27158967860613119642976869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72423914294968319047938317 27158967860613119642976869)
              ·
                refine ⟨5092306473864959933058163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27158967860613119642976869 5092306473864959933058163)
                ·
                  refine ⟨7638459710797439899587245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5092306473864959933058163 7638459710797439899587245)
                  ·
                    refine ⟨2864422391549039962345217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7638459710797439899587245 2864422391549039962345217)
                    ·
                      refine ⟨2148316793661779971758913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2864422391549039962345217 2148316793661779971758913)
                      ·
                        rfl

theorem cell23_4183832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_4183832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183832 prefixEnd_4183832 := by exact prefixLift 4183832
  have htrace : WordTrace (prefixWord ++ tailWord_4183832) baseStart_4183832 baseEnd_4183832 := by
    simpa [prefixWord, tailWord_4183832, baseEnd_4183832] using wordTrace_append hprefix tailTrace_4183832
  have hstable : (prefixWord ++ tailWord_4183832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183832).length < 2 ^ (prefixWord ++ tailWord_4183832).sum := by decide
  have hdescent : baseEnd_4183832 < baseStart_4183832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183925 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_4183925 : Nat := 118140960795 + 4183925 * 2 ^ 59
def prefixEnd_4183925 : Nat := 4983230072969 + 3 ^ 40 * 4183925 * 2
def baseEnd_4183925 : Nat := 2148364547362648107895985

theorem tailTrace_4183925 : CollatzResearch.WordTrace tailWord_4183925 prefixEnd_4183925 2148364547362648107895985 := by
  unfold tailWord_4183925
  simp only [CollatzResearch.WordTrace]
  refine ⟨152600281367361757346281229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101733520911574504897520819 152600281367361757346281229)
  ·
    refine ⟨57225105512760659004855461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152600281367361757346281229 57225105512760659004855461)
    ·
      refine ⟨10729707283642623563410399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57225105512760659004855461 10729707283642623563410399)
      ·
        refine ⟨16094560925463935345115599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10729707283642623563410399 16094560925463935345115599)
        ·
          refine ⟨24141841388195903017673399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16094560925463935345115599 24141841388195903017673399)
          ·
            refine ⟨36212762082293854526510099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24141841388195903017673399 36212762082293854526510099)
            ·
              refine ⟨54319143123440781789765149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36212762082293854526510099 54319143123440781789765149)
              ·
                refine ⟨20369678671290293171161931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54319143123440781789765149 20369678671290293171161931)
                ·
                  refine ⟨30554518006935439756742897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20369678671290293171161931 30554518006935439756742897)
                  ·
                    refine ⟨22915888505201579817557173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30554518006935439756742897 22915888505201579817557173)
                    ·
                      refine ⟨2148364547362648107895985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22915888505201579817557173 2148364547362648107895985)
                      ·
                        rfl

theorem cell23_4183925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_4183925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183925 prefixEnd_4183925 := by exact prefixLift 4183925
  have htrace : WordTrace (prefixWord ++ tailWord_4183925) baseStart_4183925 baseEnd_4183925 := by
    simpa [prefixWord, tailWord_4183925, baseEnd_4183925] using wordTrace_append hprefix tailTrace_4183925
  have hstable : (prefixWord ++ tailWord_4183925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183925).length < 2 ^ (prefixWord ++ tailWord_4183925).sum := by decide
  have hdescent : baseEnd_4183925 < baseStart_4183925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183965 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_4183965 : Nat := 118140960795 + 4183965 * 2 ^ 59
def prefixEnd_4183965 : Nat := 4983230072969 + 3 ^ 40 * 4183965 * 2
def baseEnd_4183965 : Nat := 2148385086588827951395801

theorem tailTrace_4183965 : CollatzResearch.WordTrace tailWord_4183965 prefixEnd_4183965 2148385086588827951395801 := by
  unfold tailWord_4183965
  simp only [CollatzResearch.WordTrace]
  refine ⟨152601740287216844177737349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101734493524811229451824899 152601740287216844177737349)
  ·
    refine ⟨28612826303853158283325753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152601740287216844177737349 28612826303853158283325753)
    ·
      refine ⟨21459619727889868712494315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28612826303853158283325753 21459619727889868712494315)
      ·
        refine ⟨32189429591834803068741473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21459619727889868712494315 32189429591834803068741473)
        ·
          refine ⟨24142072193876102301556105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32189429591834803068741473 24142072193876102301556105)
          ·
            refine ⟨18106554145407076726167079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24142072193876102301556105 18106554145407076726167079)
            ·
              refine ⟨27159831218110615089250619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18106554145407076726167079 27159831218110615089250619)
              ·
                refine ⟨40739746827165922633875929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27159831218110615089250619 40739746827165922633875929)
                ·
                  refine ⟨30554810120374441975406947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40739746827165922633875929 30554810120374441975406947)
                  ·
                    refine ⟨45832215180561662963110421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30554810120374441975406947 45832215180561662963110421)
                    ·
                      refine ⟨2148385086588827951395801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45832215180561662963110421 2148385086588827951395801)
                      ·
                        rfl

theorem cell23_4183965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_4183965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183965 prefixEnd_4183965 := by exact prefixLift 4183965
  have htrace : WordTrace (prefixWord ++ tailWord_4183965) baseStart_4183965 baseEnd_4183965 := by
    simpa [prefixWord, tailWord_4183965, baseEnd_4183965] using wordTrace_append hprefix tailTrace_4183965
  have hstable : (prefixWord ++ tailWord_4183965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183965).length < 2 ^ (prefixWord ++ tailWord_4183965).sum := by decide
  have hdescent : baseEnd_4183965 < baseStart_4183965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183992 : List Nat := [2, 1, 2, 1, 2, 3, 5, 1, 6]
def baseStart_4183992 : Nat := 118140960795 + 4183992 * 2 ^ 59
def prefixEnd_4183992 : Nat := 4983230072969 + 3 ^ 40 * 4183992 * 2
def baseEnd_4183992 : Nat := 238710994507388816195353

theorem tailTrace_4183992 : CollatzResearch.WordTrace tailWord_4183992 prefixEnd_4183992 238710994507388816195353 := by
  unfold tailWord_4183992
  simp only [CollatzResearch.WordTrace]
  refine ⟨76301362529059513894485115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101735150038746018525980153 76301362529059513894485115)
  ·
    refine ⟨114452043793589270841727673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76301362529059513894485115 114452043793589270841727673)
    ·
      refine ⟨85839032845191953131295755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114452043793589270841727673 85839032845191953131295755)
      ·
        refine ⟨128758549267787929696943633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85839032845191953131295755 128758549267787929696943633)
        ·
          refine ⟨96568911950840947272707725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128758549267787929696943633 96568911950840947272707725)
          ·
            refine ⟨36213341981565355227265397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96568911950840947272707725 36213341981565355227265397)
            ·
              refine ⟨3395000810771752052556131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36213341981565355227265397 3395000810771752052556131)
              ·
                refine ⟨5092501216157628078834197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3395000810771752052556131 5092501216157628078834197)
                ·
                  refine ⟨238710994507388816195353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5092501216157628078834197 238710994507388816195353)
                  ·
                    rfl

theorem cell23_4183992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 6].length) (baseStart_4183992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4183992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4183992 prefixEnd_4183992 := by exact prefixLift 4183992
  have htrace : WordTrace (prefixWord ++ tailWord_4183992) baseStart_4183992 baseEnd_4183992 := by
    simpa [prefixWord, tailWord_4183992, baseEnd_4183992] using wordTrace_append hprefix tailTrace_4183992
  have hstable : (prefixWord ++ tailWord_4183992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183992).length < 2 ^ (prefixWord ++ tailWord_4183992).sum := by decide
  have hdescent : baseEnd_4183992 < baseStart_4183992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184042 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_4184042 : Nat := 118140960795 + 4184042 * 2 ^ 59
def prefixEnd_4184042 : Nat := 4983230072969 + 3 ^ 40 * 4184042 * 2
def baseEnd_4184042 : Nat := 2148424624599224150132947

theorem tailTrace_4184042 : CollatzResearch.WordTrace tailWord_4184042 prefixEnd_4184042 2148424624599224150132947 := by
  unfold tailWord_4184042
  simp only [CollatzResearch.WordTrace]
  refine ⟨38151137176984471582072595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101736365805291924218860253 38151137176984471582072595)
  ·
    refine ⟨57226705765476707373108893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38151137176984471582072595 57226705765476707373108893)
    ·
      refine ⟨21460014662053765264915835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57226705765476707373108893 21460014662053765264915835)
      ·
        refine ⟨32190021993080647897373753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21460014662053765264915835 32190021993080647897373753)
        ·
          refine ⟨24142516494810485923030315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32190021993080647897373753 24142516494810485923030315)
          ·
            refine ⟨36213774742215728884545473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24142516494810485923030315 36213774742215728884545473)
            ·
              refine ⟨27160331056661796663409105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36213774742215728884545473 27160331056661796663409105)
              ·
                refine ⟨20370248292496347497556829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27160331056661796663409105 20370248292496347497556829)
                ·
                  refine ⟨7638843109686130311583811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20370248292496347497556829 7638843109686130311583811)
                  ·
                    refine ⟨11458264664529195467375717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7638843109686130311583811 11458264664529195467375717)
                    ·
                      refine ⟨2148424624599224150132947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11458264664529195467375717 2148424624599224150132947)
                      ·
                        rfl

theorem cell23_4184042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_4184042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184042 prefixEnd_4184042 := by exact prefixLift 4184042
  have htrace : WordTrace (prefixWord ++ tailWord_4184042) baseStart_4184042 baseEnd_4184042 := by
    simpa [prefixWord, tailWord_4184042, baseEnd_4184042] using wordTrace_append hprefix tailTrace_4184042
  have hstable : (prefixWord ++ tailWord_4184042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184042).length < 2 ^ (prefixWord ++ tailWord_4184042).sum := by decide
  have hdescent : baseEnd_4184042 < baseStart_4184042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184055 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 4]
def baseStart_4184055 : Nat := 118140960795 + 4184055 * 2 ^ 59
def prefixEnd_4184055 : Nat := 4983230072969 + 3 ^ 40 * 4184055 * 2
def baseEnd_4184055 : Nat := 2148431299847732599270387

theorem tailTrace_4184055 : CollatzResearch.WordTrace tailWord_4184055 prefixEnd_4184055 2148431299847732599270387 := by
  unfold tailWord_4184055
  simp only [CollatzResearch.WordTrace]
  refine ⟨152605022856890789548513619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101736681904593859699009079 152605022856890789548513619)
  ·
    refine ⟨228907534285336184322770429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152605022856890789548513619 228907534285336184322770429)
    ·
      refine ⟨85840325357001069121038911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228907534285336184322770429 85840325357001069121038911)
      ·
        refine ⟨128760488035501603681558367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85840325357001069121038911 128760488035501603681558367)
        ·
          refine ⟨193140732053252405522337551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128760488035501603681558367 193140732053252405522337551)
          ·
            refine ⟨289711098079878608283506327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193140732053252405522337551 289711098079878608283506327)
            ·
              refine ⟨434566647119817912425259491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289711098079878608283506327 434566647119817912425259491)
              ·
                refine ⟨651849970679726868637889237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434566647119817912425259491 651849970679726868637889237)
                ·
                  refine ⟨15277733687806098483700529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 651849970679726868637889237 15277733687806098483700529)
                  ·
                    refine ⟨11458300265854573862775397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15277733687806098483700529 11458300265854573862775397)
                    ·
                      refine ⟨2148431299847732599270387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11458300265854573862775397 2148431299847732599270387)
                      ·
                        rfl

theorem cell23_4184055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_4184055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184055 prefixEnd_4184055 := by exact prefixLift 4184055
  have htrace : WordTrace (prefixWord ++ tailWord_4184055) baseStart_4184055 baseEnd_4184055 := by
    simpa [prefixWord, tailWord_4184055, baseEnd_4184055] using wordTrace_append hprefix tailTrace_4184055
  have hstable : (prefixWord ++ tailWord_4184055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184055).length < 2 ^ (prefixWord ++ tailWord_4184055).sum := by decide
  have hdescent : baseEnd_4184055 < baseStart_4184055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184059 : List Nat := [1, 1, 1, 1, 1, 3, 4, 4, 3, 2, 2]
def baseStart_4184059 : Nat := 118140960795 + 4184059 * 2 ^ 59
def prefixEnd_4184059 : Nat := 4983230072969 + 3 ^ 40 * 4184059 * 2
def baseEnd_4184059 : Nat := 2148433353770350583620369

theorem tailTrace_4184059 : CollatzResearch.WordTrace tailWord_4184059 prefixEnd_4184059 2148433353770350583620369 := by
  unfold tailWord_4184059
  simp only [CollatzResearch.WordTrace]
  refine ⟨152605168748876298231659231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101736779165917532154439487 152605168748876298231659231)
  ·
    refine ⟨228907753123314447347488847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152605168748876298231659231 228907753123314447347488847)
    ·
      refine ⟨343361629684971671021233271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228907753123314447347488847 343361629684971671021233271)
      ·
        refine ⟨515042444527457506531849907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343361629684971671021233271 515042444527457506531849907)
        ·
          refine ⟨772563666791186259797774861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515042444527457506531849907 772563666791186259797774861)
          ·
            refine ⟨289711375046694847424165573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 772563666791186259797774861 289711375046694847424165573)
            ·
              refine ⟨54320882821255283892031045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289711375046694847424165573 54320882821255283892031045)
              ·
                refine ⟨10185165528985365729755821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54320882821255283892031045 10185165528985365729755821)
                ·
                  refine ⟨3819437073369512148658433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10185165528985365729755821 3819437073369512148658433)
                  ·
                    refine ⟨2864577805027134111493825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3819437073369512148658433 2864577805027134111493825)
                    ·
                      refine ⟨2148433353770350583620369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2864577805027134111493825 2148433353770350583620369)
                      ·
                        rfl

theorem cell23_4184059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 2, 2].length) (baseStart_4184059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184059 prefixEnd_4184059 := by exact prefixLift 4184059
  have htrace : WordTrace (prefixWord ++ tailWord_4184059) baseStart_4184059 baseEnd_4184059 := by
    simpa [prefixWord, tailWord_4184059, baseEnd_4184059] using wordTrace_append hprefix tailTrace_4184059
  have hstable : (prefixWord ++ tailWord_4184059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184059).length < 2 ^ (prefixWord ++ tailWord_4184059).sum := by decide
  have hdescent : baseEnd_4184059 < baseStart_4184059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184065 : List Nat := [1, 2, 4, 1, 2, 1, 1, 11]
def baseStart_4184065 : Nat := 118140960795 + 4184065 * 2 ^ 59
def prefixEnd_4184065 : Nat := 4983230072969 + 3 ^ 40 * 4184065 * 2
def baseEnd_4184065 : Nat := 79571719802010280005383

theorem tailTrace_4184065 : CollatzResearch.WordTrace tailWord_4184065 prefixEnd_4184065 79571719802010280005383 := by
  unfold tailWord_4184065
  simp only [CollatzResearch.WordTrace]
  refine ⟨152605387586854561256377649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101736925057903040837585099 152605387586854561256377649)
  ·
    refine ⟨114454040690140920942283237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152605387586854561256377649 114454040690140920942283237)
    ·
      refine ⟨21460132629401422676678107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114454040690140920942283237 21460132629401422676678107)
      ·
        refine ⟨32190198944102134015017161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21460132629401422676678107 32190198944102134015017161)
        ·
          refine ⟨24142649208076600511262871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32190198944102134015017161 24142649208076600511262871)
          ·
            refine ⟨36213973812114900766894307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24142649208076600511262871 36213973812114900766894307)
            ·
              refine ⟨54320960718172351150341461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36213973812114900766894307 54320960718172351150341461)
              ·
                refine ⟨79571719802010280005383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 54320960718172351150341461 79571719802010280005383)
                ·
                  rfl

theorem cell23_4184065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 11].length) (baseStart_4184065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184065 prefixEnd_4184065 := by exact prefixLift 4184065
  have htrace : WordTrace (prefixWord ++ tailWord_4184065) baseStart_4184065 baseEnd_4184065 := by
    simpa [prefixWord, tailWord_4184065, baseEnd_4184065] using wordTrace_append hprefix tailTrace_4184065
  have hstable : (prefixWord ++ tailWord_4184065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184065).length < 2 ^ (prefixWord ++ tailWord_4184065).sum := by decide
  have hdescent : baseEnd_4184065 < baseStart_4184065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184072 : List Nat := [2, 1, 3, 2, 1, 2, 3, 2, 1, 2, 4]
def baseStart_4184072 : Nat := 118140960795 + 4184072 * 2 ^ 59
def prefixEnd_4184072 : Nat := 4983230072969 + 3 ^ 40 * 4184072 * 2
def baseEnd_4184072 : Nat := 2148440029018859032757809

theorem tailTrace_4184072 : CollatzResearch.WordTrace tailWord_4184072 prefixEnd_4184072 2148440029018859032757809 := by
  unfold tailWord_4184072
  simp only [CollatzResearch.WordTrace]
  refine ⟨76302821448914600725941235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101737095265219467634588313 76302821448914600725941235)
  ·
    refine ⟨114454232173371901088911853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76302821448914600725941235 114454232173371901088911853)
    ·
      refine ⟨42920337065014462908341945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114454232173371901088911853 42920337065014462908341945)
      ·
        refine ⟨32190252798760847181256459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42920337065014462908341945 32190252798760847181256459)
        ·
          refine ⟨48285379198141270771884689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32190252798760847181256459 48285379198141270771884689)
          ·
            refine ⟨36214034398605953078913517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48285379198141270771884689 36214034398605953078913517)
            ·
              refine ⟨13580262899477232404592569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36214034398605953078913517 13580262899477232404592569)
              ·
                refine ⟨10185197174607924303444427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13580262899477232404592569 10185197174607924303444427)
                ·
                  refine ⟨15277795761911886455166641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10185197174607924303444427 15277795761911886455166641)
                  ·
                    refine ⟨11458346821433914841374981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15277795761911886455166641 11458346821433914841374981)
                    ·
                      refine ⟨2148440029018859032757809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11458346821433914841374981 2148440029018859032757809)
                      ·
                        rfl

theorem cell23_4184072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_4184072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184072 prefixEnd_4184072 := by exact prefixLift 4184072
  have htrace : WordTrace (prefixWord ++ tailWord_4184072) baseStart_4184072 baseEnd_4184072 := by
    simpa [prefixWord, tailWord_4184072, baseEnd_4184072] using wordTrace_append hprefix tailTrace_4184072
  have hstable : (prefixWord ++ tailWord_4184072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184072).length < 2 ^ (prefixWord ++ tailWord_4184072).sum := by decide
  have hdescent : baseEnd_4184072 < baseStart_4184072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184082 : List Nat := [3, 2, 5, 13]
def baseStart_4184082 : Nat := 118140960795 + 4184082 * 2 ^ 59
def prefixEnd_4184082 : Nat := 4983230072969 + 3 ^ 40 * 4184082 * 2
def baseEnd_4184082 : Nat := 982370902526476448849

theorem tailTrace_4184082 : CollatzResearch.WordTrace tailWord_4184082 prefixEnd_4184082 982370902526476448849 := by
  unfold tailWord_4184082
  simp only [CollatzResearch.WordTrace]
  refine ⟨38151501906948243289936625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101737338418528648773164333 38151501906948243289936625)
  ·
    refine ⟨28613626430211182467452469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38151501906948243289936625 28613626430211182467452469)
    ·
      refine ⟨2682527477832298356323669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28613626430211182467452469 2682527477832298356323669)
      ·
        refine ⟨982370902526476448849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 2682527477832298356323669 982370902526476448849)
        ·
          rfl

theorem cell23_4184082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 13].length) (baseStart_4184082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184082 prefixEnd_4184082 := by exact prefixLift 4184082
  have htrace : WordTrace (prefixWord ++ tailWord_4184082) baseStart_4184082 baseEnd_4184082 := by
    simpa [prefixWord, tailWord_4184082, baseEnd_4184082] using wordTrace_append hprefix tailTrace_4184082
  have hstable : (prefixWord ++ tailWord_4184082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184082).length < 2 ^ (prefixWord ++ tailWord_4184082).sum := by decide
  have hdescent : baseEnd_4184082 < baseStart_4184082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184087 : List Nat := [1, 1, 3, 5, 3, 1, 2, 2, 1, 1, 3]
def baseStart_4184087 : Nat := 118140960795 + 4184087 * 2 ^ 59
def prefixEnd_4184087 : Nat := 4983230072969 + 3 ^ 40 * 4184087 * 2
def baseEnd_4184087 : Nat := 2148447731228676474070241

theorem tailTrace_4184087 : CollatzResearch.WordTrace tailWord_4184087 prefixEnd_4184087 2148447731228676474070241 := by
  unfold tailWord_4184087
  simp only [CollatzResearch.WordTrace]
  refine ⟨152606189992774859013678515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101737459995183239342452343 152606189992774859013678515)
  ·
    refine ⟨228909284989162288520517773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152606189992774859013678515 228909284989162288520517773)
    ·
      refine ⟨85840981870935858195194165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228909284989162288520517773 85840981870935858195194165)
      ·
        refine ⟨8047592050400236705799453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85840981870935858195194165 8047592050400236705799453)
        ·
          refine ⟨3017847018900088764674795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8047592050400236705799453 3017847018900088764674795)
          ·
            refine ⟨4526770528350133147012193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3017847018900088764674795 4526770528350133147012193)
            ·
              refine ⟨3395077896262599860259145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4526770528350133147012193 3395077896262599860259145)
              ·
                refine ⟨2546308422196949895194359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3395077896262599860259145 2546308422196949895194359)
                ·
                  refine ⟨3819462633295424842791539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2546308422196949895194359 3819462633295424842791539)
                  ·
                    refine ⟨5729193949943137264187309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3819462633295424842791539 5729193949943137264187309)
                    ·
                      refine ⟨2148447731228676474070241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5729193949943137264187309 2148447731228676474070241)
                      ·
                        rfl

theorem cell23_4184087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_4184087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184087 prefixEnd_4184087 := by exact prefixLift 4184087
  have htrace : WordTrace (prefixWord ++ tailWord_4184087) baseStart_4184087 baseEnd_4184087 := by
    simpa [prefixWord, tailWord_4184087, baseEnd_4184087] using wordTrace_append hprefix tailTrace_4184087
  have hstable : (prefixWord ++ tailWord_4184087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184087).length < 2 ^ (prefixWord ++ tailWord_4184087).sum := by decide
  have hdescent : baseEnd_4184087 < baseStart_4184087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184095 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 1, 9]
def baseStart_4184095 : Nat := 118140960795 + 4184095 * 2 ^ 59
def prefixEnd_4184095 : Nat := 4983230072969 + 3 ^ 40 * 4184095 * 2
def baseEnd_4184095 : Nat := 716150613024637480923401

theorem tailTrace_4184095 : CollatzResearch.WordTrace tailWord_4184095 prefixEnd_4184095 716150613024637480923401 := by
  unfold tailWord_4184095
  simp only [CollatzResearch.WordTrace]
  refine ⟨152606481776745876379969739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101737654517830584253313159 152606481776745876379969739)
  ·
    refine ⟨228909722665118814569954609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152606481776745876379969739 228909722665118814569954609)
    ·
      refine ⟨171682291998839110927465957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228909722665118814569954609 171682291998839110927465957)
      ·
        refine ⟨32190429749782333298899867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171682291998839110927465957 32190429749782333298899867)
        ·
          refine ⟨48285644624673499948349801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32190429749782333298899867 48285644624673499948349801)
          ·
            refine ⟨36214233468505124961262351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48285644624673499948349801 36214233468505124961262351)
            ·
              refine ⟨54321350202757687441893527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36214233468505124961262351 54321350202757687441893527)
              ·
                refine ⟨81482025304136531162840291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54321350202757687441893527 81482025304136531162840291)
                ·
                  refine ⟨122223037956204796744260437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81482025304136531162840291 122223037956204796744260437)
                  ·
                    refine ⟨716150613024637480923401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 122223037956204796744260437 716150613024637480923401)
                    ·
                      rfl

theorem cell23_4184095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 9].length) (baseStart_4184095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184095 prefixEnd_4184095 := by exact prefixLift 4184095
  have htrace : WordTrace (prefixWord ++ tailWord_4184095) baseStart_4184095 baseEnd_4184095 := by
    simpa [prefixWord, tailWord_4184095, baseEnd_4184095] using wordTrace_append hprefix tailTrace_4184095
  have hstable : (prefixWord ++ tailWord_4184095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184095).length < 2 ^ (prefixWord ++ tailWord_4184095).sum := by decide
  have hdescent : baseEnd_4184095 < baseStart_4184095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184116 : List Nat := [2, 5, 1, 2, 2, 1, 3, 7]
def baseStart_4184116 : Nat := 118140960795 + 4184116 * 2 ^ 59
def prefixEnd_4184116 : Nat := 4983230072969 + 3 ^ 40 * 4184116 * 2
def baseEnd_4184116 : Nat := 79572689709913217059541

theorem tailTrace_4184116 : CollatzResearch.WordTrace tailWord_4184116 prefixEnd_4184116 79572689709913217059541 := by
  unfold tailWord_4184116
  simp only [CollatzResearch.WordTrace]
  refine ⟨76303623854834898483242101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101738165139779864644322801 76303623854834898483242101)
  ·
    refine ⟨7153464736390771732803947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76303623854834898483242101 7153464736390771732803947)
    ·
      refine ⟨10730197104586157599205921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7153464736390771732803947 10730197104586157599205921)
      ·
        refine ⟨8047647828439618199404441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10730197104586157599205921 8047647828439618199404441)
        ·
          refine ⟨6035735871329713649553331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8047647828439618199404441 6035735871329713649553331)
          ·
            refine ⟨9053603806994570474329997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6035735871329713649553331 9053603806994570474329997)
            ·
              refine ⟨3395101427622963927873749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9053603806994570474329997 3395101427622963927873749)
              ·
                refine ⟨79572689709913217059541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3395101427622963927873749 79572689709913217059541)
                ·
                  rfl

theorem cell23_4184116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 7].length) (baseStart_4184116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184116 prefixEnd_4184116 := by exact prefixLift 4184116
  have htrace : WordTrace (prefixWord ++ tailWord_4184116) baseStart_4184116 baseEnd_4184116 := by
    simpa [prefixWord, tailWord_4184116, baseEnd_4184116] using wordTrace_append hprefix tailTrace_4184116
  have hstable : (prefixWord ++ tailWord_4184116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184116).length < 2 ^ (prefixWord ++ tailWord_4184116).sum := by decide
  have hdescent : baseEnd_4184116 < baseStart_4184116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184119 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 3, 3, 2]
def baseStart_4184119 : Nat := 118140960795 + 4184119 * 2 ^ 59
def prefixEnd_4184119 : Nat := 4983230072969 + 3 ^ 40 * 4184119 * 2
def baseEnd_4184119 : Nat := 2148464162609620348870093

theorem tailTrace_4184119 : CollatzResearch.WordTrace tailWord_4184119 prefixEnd_4184119 2148464162609620348870093 := by
  unfold tailWord_4184119
  simp only [CollatzResearch.WordTrace]
  refine ⟨152607357128658928478843411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101738238085772618985895607 152607357128658928478843411)
  ·
    refine ⟨228911035692988392718265117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152607357128658928478843411 228911035692988392718265117)
    ·
      refine ⟨85841638384870647269349419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228911035692988392718265117 85841638384870647269349419)
      ·
        refine ⟨128762457577305970904024129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85841638384870647269349419 128762457577305970904024129)
        ·
          refine ⟨96571843182979478178018097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128762457577305970904024129 96571843182979478178018097)
          ·
            refine ⟨72428882387234608633513573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96571843182979478178018097 72428882387234608633513573)
            ·
              refine ⟨13580415447606489118783795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72428882387234608633513573 13580415447606489118783795)
              ·
                refine ⟨20370623171409733678175693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13580415447606489118783795 20370623171409733678175693)
                ·
                  refine ⟨7638983689278650129315885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20370623171409733678175693 7638983689278650129315885)
                  ·
                    refine ⟨2864618883479493798493457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7638983689278650129315885 2864618883479493798493457)
                    ·
                      refine ⟨2148464162609620348870093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2864618883479493798493457 2148464162609620348870093)
                      ·
                        rfl

theorem cell23_4184119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 3, 2].length) (baseStart_4184119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184119 prefixEnd_4184119 := by exact prefixLift 4184119
  have htrace : WordTrace (prefixWord ++ tailWord_4184119) baseStart_4184119 baseEnd_4184119 := by
    simpa [prefixWord, tailWord_4184119, baseEnd_4184119] using wordTrace_append hprefix tailTrace_4184119
  have hstable : (prefixWord ++ tailWord_4184119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184119).length < 2 ^ (prefixWord ++ tailWord_4184119).sum := by decide
  have hdescent : baseEnd_4184119 < baseStart_4184119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184142 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 2, 6]
def baseStart_4184142 : Nat := 118140960795 + 4184142 * 2 ^ 59
def prefixEnd_4184142 : Nat := 4983230072969 + 3 ^ 40 * 4184142 * 2
def baseEnd_4184142 : Nat := 716158657554891252960829

theorem tailTrace_4184142 : CollatzResearch.WordTrace tailWord_4184142 prefixEnd_4184142 716158657554891252960829 := by
  unfold tailWord_4184142
  simp only [CollatzResearch.WordTrace]
  refine ⟨19076024500946950425866335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101738797338383735604620453 19076024500946950425866335)
  ·
    refine ⟨28614036751420425638799503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19076024500946950425866335 28614036751420425638799503)
    ·
      refine ⟨42921055127130638458199255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28614036751420425638799503 42921055127130638458199255)
      ·
        refine ⟨64381582690695957687298883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42921055127130638458199255 64381582690695957687298883)
        ·
          refine ⟨96572374036043936530948325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64381582690695957687298883 96572374036043936530948325)
          ·
            refine ⟨18107320131758238099552811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96572374036043936530948325 18107320131758238099552811)
            ·
              refine ⟨27160980197637357149329217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18107320131758238099552811 27160980197637357149329217)
              ·
                refine ⟨20370735148228017861996913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27160980197637357149329217 20370735148228017861996913)
                ·
                  refine ⟨15278051361171013396497685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20370735148228017861996913 15278051361171013396497685)
                  ·
                    refine ⟨716158657554891252960829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15278051361171013396497685 716158657554891252960829)
                    ·
                      rfl

theorem cell23_4184142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_4184142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184142 prefixEnd_4184142 := by exact prefixLift 4184142
  have htrace : WordTrace (prefixWord ++ tailWord_4184142) baseStart_4184142 baseEnd_4184142 := by
    simpa [prefixWord, tailWord_4184142, baseEnd_4184142] using wordTrace_append hprefix tailTrace_4184142
  have hstable : (prefixWord ++ tailWord_4184142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184142).length < 2 ^ (prefixWord ++ tailWord_4184142).sum := by decide
  have hdescent : baseEnd_4184142 < baseStart_4184142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184172 : List Nat := [2, 2, 1, 1, 3, 3, 2, 2, 7]
def baseStart_4184172 : Nat := 118140960795 + 4184172 * 2 ^ 59
def prefixEnd_4184172 : Nat := 4983230072969 + 3 ^ 40 * 4184172 * 2
def baseEnd_4184172 : Nat := 238721264120478737945261

theorem tailTrace_4184172 : CollatzResearch.WordTrace tailWord_4184172 prefixEnd_4184172 238721264120478737945261 := by
  unfold tailWord_4184172
  simp only [CollatzResearch.WordTrace]
  refine ⟨76304645098733459265261385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101739526798311279020348513 76304645098733459265261385)
  ·
    refine ⟨57228483824050094448946039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76304645098733459265261385 57228483824050094448946039)
    ·
      refine ⟨85842725736075141673419059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57228483824050094448946039 85842725736075141673419059)
      ·
        refine ⟨128764088604112712510128589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85842725736075141673419059 128764088604112712510128589)
        ·
          refine ⟨48286533226542267191298221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128764088604112712510128589 48286533226542267191298221)
          ·
            refine ⟨18107449959953350196736833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48286533226542267191298221 18107449959953350196736833)
            ·
              refine ⟨13580587469965012647552625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18107449959953350196736833 13580587469965012647552625)
              ·
                refine ⟨10185440602473759485664469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13580587469965012647552625 10185440602473759485664469)
                ·
                  refine ⟨238721264120478737945261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10185440602473759485664469 238721264120478737945261)
                  ·
                    rfl

theorem cell23_4184172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 7].length) (baseStart_4184172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184172 prefixEnd_4184172 := by exact prefixLift 4184172
  have htrace : WordTrace (prefixWord ++ tailWord_4184172) baseStart_4184172 baseEnd_4184172 := by
    simpa [prefixWord, tailWord_4184172, baseEnd_4184172] using wordTrace_append hprefix tailTrace_4184172
  have hstable : (prefixWord ++ tailWord_4184172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184172).length < 2 ^ (prefixWord ++ tailWord_4184172).sum := by decide
  have hdescent : baseEnd_4184172 < baseStart_4184172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184206 : List Nat := [4, 1, 1, 3, 3, 2, 1, 1, 7]
def baseStart_4184206 : Nat := 118140960795 + 4184206 * 2 ^ 59
def prefixEnd_4184206 : Nat := 4983230072969 + 3 ^ 40 * 4184206 * 2
def baseEnd_4184206 : Nat := 238723203936284612053577

theorem tailTrace_4184206 : CollatzResearch.WordTrace tailWord_4184206 prefixEnd_4184206 238723203936284612053577 := by
  unfold tailWord_4184206
  simp only [CollatzResearch.WordTrace]
  refine ⟨19076316284917967792157559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101740353519562494891506981 19076316284917967792157559)
  ·
    refine ⟨28614474427376951688236339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19076316284917967792157559 28614474427376951688236339)
    ·
      refine ⟨42921711641065427532354509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28614474427376951688236339 42921711641065427532354509)
      ·
        refine ⟨16095641865399535324632941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42921711641065427532354509 16095641865399535324632941)
        ·
          refine ⟨6035865699524825746737353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16095641865399535324632941 6035865699524825746737353)
          ·
            refine ⟨4526899274643619310053015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6035865699524825746737353 4526899274643619310053015)
            ·
              refine ⟨6790348911965428965079523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4526899274643619310053015 6790348911965428965079523)
              ·
                refine ⟨10185523367948143447619285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6790348911965428965079523 10185523367948143447619285)
                ·
                  refine ⟨238723203936284612053577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10185523367948143447619285 238723203936284612053577)
                  ·
                    rfl

theorem cell23_4184206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_4184206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184206 prefixEnd_4184206 := by exact prefixLift 4184206
  have htrace : WordTrace (prefixWord ++ tailWord_4184206) baseStart_4184206 baseEnd_4184206 := by
    simpa [prefixWord, tailWord_4184206, baseEnd_4184206] using wordTrace_append hprefix tailTrace_4184206
  have hstable : (prefixWord ++ tailWord_4184206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184206).length < 2 ^ (prefixWord ++ tailWord_4184206).sum := by decide
  have hdescent : baseEnd_4184206 < baseStart_4184206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184239 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 4, 4, 2]
def baseStart_4184239 : Nat := 118140960795 + 4184239 * 2 ^ 59
def prefixEnd_4184239 : Nat := 4983230072969 + 3 ^ 40 * 4184239 * 2
def baseEnd_4184239 : Nat := 2148525780288159879369541

theorem tailTrace_4184239 : CollatzResearch.WordTrace tailWord_4184239 prefixEnd_4184239 2148525780288159879369541 := by
  unfold tailWord_4184239
  simp only [CollatzResearch.WordTrace]
  refine ⟨152611733888224188973211771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101741155925482792648807847 152611733888224188973211771)
  ·
    refine ⟨228917600832336283459817657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152611733888224188973211771 228917600832336283459817657)
    ·
      refine ⟨171688200624252212594863243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228917600832336283459817657 171688200624252212594863243)
      ·
        refine ⟨257532300936378318892294865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171688200624252212594863243 257532300936378318892294865)
        ·
          refine ⟨193149225702283739169221149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257532300936378318892294865 193149225702283739169221149)
          ·
            refine ⟨72430959638356402188457931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193149225702283739169221149 72430959638356402188457931)
            ·
              refine ⟨108646439457534603282686897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72430959638356402188457931 108646439457534603282686897)
              ·
                refine ⟨81484829593150952462015173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108646439457534603282686897 81484829593150952462015173)
                ·
                  refine ⟨15278405548715803586627845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81484829593150952462015173 15278405548715803586627845)
                  ·
                    refine ⟨2864701040384213172492721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15278405548715803586627845 2864701040384213172492721)
                    ·
                      refine ⟨2148525780288159879369541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2864701040384213172492721 2148525780288159879369541)
                      ·
                        rfl

theorem cell23_4184239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 4, 2].length) (baseStart_4184239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184239 prefixEnd_4184239 := by exact prefixLift 4184239
  have htrace : WordTrace (prefixWord ++ tailWord_4184239) baseStart_4184239 baseEnd_4184239 := by
    simpa [prefixWord, tailWord_4184239, baseEnd_4184239] using wordTrace_append hprefix tailTrace_4184239
  have hstable : (prefixWord ++ tailWord_4184239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184239).length < 2 ^ (prefixWord ++ tailWord_4184239).sum := by decide
  have hdescent : baseEnd_4184239 < baseStart_4184239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184257 : List Nat := [1, 2, 6, 1, 3, 1, 2, 2, 5]
def baseStart_4184257 : Nat := 118140960795 + 4184257 * 2 ^ 59
def prefixEnd_4184257 : Nat := 4983230072969 + 3 ^ 40 * 4184257 * 2
def baseEnd_4184257 : Nat := 238726113659993423216051

theorem tailTrace_4184257 : CollatzResearch.WordTrace tailWord_4184257 prefixEnd_4184257 238726113659993423216051 := by
  unfold tailWord_4184257
  simp only [CollatzResearch.WordTrace]
  refine ⟨152612390402158978047367025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101741593601439318698244683 152612390402158978047367025)
  ·
    refine ⟨114459292801619233535525269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152612390402158978047367025 114459292801619233535525269)
    ·
      refine ⟨5365279350075901571977747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 114459292801619233535525269 5365279350075901571977747)
      ·
        refine ⟨8047919025113852357966621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5365279350075901571977747 8047919025113852357966621)
        ·
          refine ⟨3017969634417694634237483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8047919025113852357966621 3017969634417694634237483)
          ·
            refine ⟨4526954451626541951356225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3017969634417694634237483 4526954451626541951356225)
            ·
              refine ⟨3395215838719906463517169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4526954451626541951356225 3395215838719906463517169)
              ·
                refine ⟨2546411879039929847637877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3395215838719906463517169 2546411879039929847637877)
                ·
                  refine ⟨238726113659993423216051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2546411879039929847637877 238726113659993423216051)
                  ·
                    rfl

theorem cell23_4184257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 5].length) (baseStart_4184257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184257 prefixEnd_4184257 := by exact prefixLift 4184257
  have htrace : WordTrace (prefixWord ++ tailWord_4184257) baseStart_4184257 baseEnd_4184257 := by
    simpa [prefixWord, tailWord_4184257, baseEnd_4184257] using wordTrace_append hprefix tailTrace_4184257
  have hstable : (prefixWord ++ tailWord_4184257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184257).length < 2 ^ (prefixWord ++ tailWord_4184257).sum := by decide
  have hdescent : baseEnd_4184257 < baseStart_4184257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184290 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_4184290 : Nat := 118140960795 + 4184290 * 2 ^ 59
def prefixEnd_4184290 : Nat := 4983230072969 + 3 ^ 40 * 4184290 * 2
def baseEnd_4184290 : Nat := 2148551967801539179831807

theorem tailTrace_4184290 : CollatzResearch.WordTrace tailWord_4184290 prefixEnd_4184290 2148551967801539179831807 := by
  unfold tailWord_4184290
  simp only [CollatzResearch.WordTrace]
  refine ⟨38153398502759856170829581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101742396007359616455545549 38153398502759856170829581)
  ·
    refine ⟨14307524438534946064061093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38153398502759856170829581 14307524438534946064061093)
    ·
      refine ⟨2682660832225302387011455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14307524438534946064061093 2682660832225302387011455)
      ·
        refine ⟨4023991248337953580517183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2682660832225302387011455 4023991248337953580517183)
        ·
          refine ⟨6035986872506930370775775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4023991248337953580517183 6035986872506930370775775)
          ·
            refine ⟨9053980308760395556163663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6035986872506930370775775 9053980308760395556163663)
            ·
              refine ⟨13580970463140593334245495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9053980308760395556163663 13580970463140593334245495)
              ·
                refine ⟨20371455694710890001368243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13580970463140593334245495 20371455694710890001368243)
                ·
                  refine ⟨30557183542066335002052365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20371455694710890001368243 30557183542066335002052365)
                  ·
                    refine ⟨11458943828274875625769637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30557183542066335002052365 11458943828274875625769637)
                    ·
                      refine ⟨2148551967801539179831807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11458943828274875625769637 2148551967801539179831807)
                      ·
                        rfl

theorem cell23_4184290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_4184290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184290 prefixEnd_4184290 := by exact prefixLift 4184290
  have htrace : WordTrace (prefixWord ++ tailWord_4184290) baseStart_4184290 baseEnd_4184290 := by
    simpa [prefixWord, tailWord_4184290, baseEnd_4184290] using wordTrace_append hprefix tailTrace_4184290
  have hstable : (prefixWord ++ tailWord_4184290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184290).length < 2 ^ (prefixWord ++ tailWord_4184290).sum := by decide
  have hdescent : baseEnd_4184290 < baseStart_4184290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184293 : List Nat := [1, 3, 1, 4, 2, 3, 1, 1, 2, 2, 3]
def baseStart_4184293 : Nat := 118140960795 + 4184293 * 2 ^ 59
def prefixEnd_4184293 : Nat := 4983230072969 + 3 ^ 40 * 4184293 * 2
def baseEnd_4184293 : Nat := 2148553508243502668094293

theorem tailTrace_4184293 : CollatzResearch.WordTrace tailWord_4184293 prefixEnd_4184293 2148553508243502668094293 := by
  unfold tailWord_4184293
  simp only [CollatzResearch.WordTrace]
  refine ⟨152613703430028556195677533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101742468953352370797118355 152613703430028556195677533)
  ·
    refine ⟨57230138786260708573379075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152613703430028556195677533 57230138786260708573379075)
    ·
      refine ⟨85845208179391062860068613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57230138786260708573379075 85845208179391062860068613)
      ·
        refine ⟨16095976533635824286262865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85845208179391062860068613 16095976533635824286262865)
        ·
          refine ⟨12071982400226868214697149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16095976533635824286262865 12071982400226868214697149)
          ·
            refine ⟨4526993400085075580511431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12071982400226868214697149 4526993400085075580511431)
            ·
              refine ⟨6790490100127613370767147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4526993400085075580511431 6790490100127613370767147)
              ·
                refine ⟨10185735150191420056150721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6790490100127613370767147 10185735150191420056150721)
                ·
                  refine ⟨7639301362643565042113041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10185735150191420056150721 7639301362643565042113041)
                  ·
                    refine ⟨5729476021982673781584781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7639301362643565042113041 5729476021982673781584781)
                    ·
                      refine ⟨2148553508243502668094293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5729476021982673781584781 2148553508243502668094293)
                      ·
                        rfl

theorem cell23_4184293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_4184293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184293 prefixEnd_4184293 := by exact prefixLift 4184293
  have htrace : WordTrace (prefixWord ++ tailWord_4184293) baseStart_4184293 baseEnd_4184293 := by
    simpa [prefixWord, tailWord_4184293, baseEnd_4184293] using wordTrace_append hprefix tailTrace_4184293
  have hstable : (prefixWord ++ tailWord_4184293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184293).length < 2 ^ (prefixWord ++ tailWord_4184293).sum := by decide
  have hdescent : baseEnd_4184293 < baseStart_4184293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184323 : List Nat := [1, 1, 1, 3, 2, 3, 1, 6, 1, 1, 3]
def baseStart_4184323 : Nat := 118140960795 + 4184323 * 2 ^ 59
def prefixEnd_4184323 : Nat := 4983230072969 + 3 ^ 40 * 4184323 * 2
def baseEnd_4184323 : Nat := 2148568912663137550719155

theorem tailTrace_4184323 : CollatzResearch.WordTrace tailWord_4184323 prefixEnd_4184323 2148568912663137550719155 := by
  unfold tailWord_4184323
  simp only [CollatzResearch.WordTrace]
  refine ⟨152614797619919871319269623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101743198413279914212846415 152614797619919871319269623)
  ·
    refine ⟨228922196429879806978904435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152614797619919871319269623 228922196429879806978904435)
    ·
      refine ⟨343383294644819710468356653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228922196429879806978904435 343383294644819710468356653)
      ·
        refine ⟨128768735491807391425633745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343383294644819710468356653 128768735491807391425633745)
        ·
          refine ⟨96576551618855543569225309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128768735491807391425633745 96576551618855543569225309)
          ·
            refine ⟨36216206857070828838459491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96576551618855543569225309 36216206857070828838459491)
            ·
              refine ⟨54324310285606243257689237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36216206857070828838459491 54324310285606243257689237)
              ·
                refine ⟨2546452044637792652704183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54324310285606243257689237 2546452044637792652704183)
                ·
                  refine ⟨3819678066956688979056275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2546452044637792652704183 3819678066956688979056275)
                  ·
                    refine ⟨5729517100435033468584413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3819678066956688979056275 5729517100435033468584413)
                    ·
                      refine ⟨2148568912663137550719155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5729517100435033468584413 2148568912663137550719155)
                      ·
                        rfl

theorem cell23_4184323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 1, 1, 3].length) (baseStart_4184323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184323 prefixEnd_4184323 := by exact prefixLift 4184323
  have htrace : WordTrace (prefixWord ++ tailWord_4184323) baseStart_4184323 baseEnd_4184323 := by
    simpa [prefixWord, tailWord_4184323, baseEnd_4184323] using wordTrace_append hprefix tailTrace_4184323
  have hstable : (prefixWord ++ tailWord_4184323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184323).length < 2 ^ (prefixWord ++ tailWord_4184323).sum := by decide
  have hdescent : baseEnd_4184323 < baseStart_4184323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184350 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_4184350 : Nat := 118140960795 + 4184350 * 2 ^ 59
def prefixEnd_4184350 : Nat := 4983230072969 + 3 ^ 40 * 4184350 * 2
def baseEnd_4184350 : Nat := 2148582776640808945081531

theorem tailTrace_4184350 : CollatzResearch.WordTrace tailWord_4184350 prefixEnd_4184350 2148582776640808945081531 := by
  unfold tailWord_4184350
  simp only [CollatzResearch.WordTrace]
  refine ⟨19076972798852756866312813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101743854927214703287001669 19076972798852756866312813)
  ·
    refine ⟨7153864799569783824867305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19076972798852756866312813 7153864799569783824867305)
    ·
      refine ⟨5365398599677337868650479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7153864799569783824867305 5365398599677337868650479)
      ·
        refine ⟨8048097899516006802975719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5365398599677337868650479 8048097899516006802975719)
        ·
          refine ⟨12072146849274010204463579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8048097899516006802975719 12072146849274010204463579)
          ·
            refine ⟨18108220273911015306695369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12072146849274010204463579 18108220273911015306695369)
            ·
              refine ⟨13581165205433261480021527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18108220273911015306695369 13581165205433261480021527)
              ·
                refine ⟨20371747808149892220032291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13581165205433261480021527 20371747808149892220032291)
                ·
                  refine ⟨30557621712224838330048437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20371747808149892220032291 30557621712224838330048437)
                  ·
                    refine ⟨2864777035521078593442041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30557621712224838330048437 2864777035521078593442041)
                    ·
                      refine ⟨2148582776640808945081531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2864777035521078593442041 2148582776640808945081531)
                      ·
                        rfl

theorem cell23_4184350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_4184350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184350 prefixEnd_4184350 := by exact prefixLift 4184350
  have htrace : WordTrace (prefixWord ++ tailWord_4184350) baseStart_4184350 baseEnd_4184350 := by
    simpa [prefixWord, tailWord_4184350, baseEnd_4184350] using wordTrace_append hprefix tailTrace_4184350
  have hstable : (prefixWord ++ tailWord_4184350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184350).length < 2 ^ (prefixWord ++ tailWord_4184350).sum := by decide
  have hdescent : baseEnd_4184350 < baseStart_4184350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184356 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 4, 4]
def baseStart_4184356 : Nat := 118140960795 + 4184356 * 2 ^ 59
def prefixEnd_4184356 : Nat := 4983230072969 + 3 ^ 40 * 4184356 * 2
def baseEnd_4184356 : Nat := 716195285841578640535501

theorem tailTrace_4184356 : CollatzResearch.WordTrace tailWord_4184356 prefixEnd_4184356 716195285841578640535501 := by
  unfold tailWord_4184356
  simp only [CollatzResearch.WordTrace]
  refine ⟨76308000614400158977610461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101744000819200211970147281 76308000614400158977610461)
  ·
    refine ⟨28615500230400059616603923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76308000614400158977610461 28615500230400059616603923)
    ·
      refine ⟨42923250345600089424905885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28615500230400059616603923 42923250345600089424905885)
      ·
        refine ⟨16096218879600033534339707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42923250345600089424905885 16096218879600033534339707)
        ·
          refine ⟨24144328319400050301509561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16096218879600033534339707 24144328319400050301509561)
          ·
            refine ⟨18108246239550037726132171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24144328319400050301509561 18108246239550037726132171)
            ·
              refine ⟨27162369359325056589198257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18108246239550037726132171 27162369359325056589198257)
              ·
                refine ⟨20371777019493792441898693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27162369359325056589198257 20371777019493792441898693)
                ·
                  refine ⟨3819708191155086082856005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20371777019493792441898693 3819708191155086082856005)
                  ·
                    refine ⟨716195285841578640535501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3819708191155086082856005 716195285841578640535501)
                    ·
                      rfl

theorem cell23_4184356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_4184356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184356 prefixEnd_4184356 := by exact prefixLift 4184356
  have htrace : WordTrace (prefixWord ++ tailWord_4184356) baseStart_4184356 baseEnd_4184356 := by
    simpa [prefixWord, tailWord_4184356, baseEnd_4184356] using wordTrace_append hprefix tailTrace_4184356
  have hstable : (prefixWord ++ tailWord_4184356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184356).length < 2 ^ (prefixWord ++ tailWord_4184356).sum := by decide
  have hdescent : baseEnd_4184356 < baseStart_4184356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184357 : List Nat := [1, 3, 1, 2, 5, 2, 1, 3, 1, 1, 3]
def baseStart_4184357 : Nat := 118140960795 + 4184357 * 2 ^ 59
def prefixEnd_4184357 : Nat := 4983230072969 + 3 ^ 40 * 4184357 * 2
def baseEnd_4184357 : Nat := 2148586371005390417693999

theorem tailTrace_4184357 : CollatzResearch.WordTrace tailWord_4184357 prefixEnd_4184357 2148586371005390417693999 := by
  unfold tailWord_4184357
  simp only [CollatzResearch.WordTrace]
  refine ⟨152616037701796695126007325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101744025134531130084004883 152616037701796695126007325)
  ·
    refine ⟨57231014138173760672252747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152616037701796695126007325 57231014138173760672252747)
    ·
      refine ⟨85846521207260641008379121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57231014138173760672252747 85846521207260641008379121)
      ·
        refine ⟨64384890905445480756284341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85846521207260641008379121 64384890905445480756284341)
        ·
          refine ⟨6036083522385513820901657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64384890905445480756284341 6036083522385513820901657)
          ·
            refine ⟨4527062641789135365676243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6036083522385513820901657 4527062641789135365676243)
            ·
              refine ⟨6790593962683703048514365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4527062641789135365676243 6790593962683703048514365)
              ·
                refine ⟨2546472736006388643192887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6790593962683703048514365 2546472736006388643192887)
                ·
                  refine ⟨3819709104009582964789331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2546472736006388643192887 3819709104009582964789331)
                  ·
                    refine ⟨5729563656014374447183997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3819709104009582964789331 5729563656014374447183997)
                    ·
                      refine ⟨2148586371005390417693999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5729563656014374447183997 2148586371005390417693999)
                      ·
                        rfl

theorem cell23_4184357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 1, 1, 3].length) (baseStart_4184357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184357 prefixEnd_4184357 := by exact prefixLift 4184357
  have htrace : WordTrace (prefixWord ++ tailWord_4184357) baseStart_4184357 baseEnd_4184357 := by
    simpa [prefixWord, tailWord_4184357, baseEnd_4184357] using wordTrace_append hprefix tailTrace_4184357
  have hstable : (prefixWord ++ tailWord_4184357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184357).length < 2 ^ (prefixWord ++ tailWord_4184357).sum := by decide
  have hdescent : baseEnd_4184357 < baseStart_4184357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184396 : List Nat := [2, 2, 1, 3, 2, 1, 2, 3, 1, 3, 3]
def baseStart_4184396 : Nat := 118140960795 + 4184396 * 2 ^ 59
def prefixEnd_4184396 : Nat := 4983230072969 + 3 ^ 40 * 4184396 * 2
def baseEnd_4184396 : Nat := 2148606396750915765106319

theorem tailTrace_4184396 : CollatzResearch.WordTrace tailWord_4184396 prefixEnd_4184396 2148606396750915765106319 := by
  unfold tailWord_4184396
  simp only [CollatzResearch.WordTrace]
  refine ⟨76308730074327702393338521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101744973432436936524451361 76308730074327702393338521)
  ·
    refine ⟨57231547555745776795003891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76308730074327702393338521 57231547555745776795003891)
    ·
      refine ⟨85847321333618665192505837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57231547555745776795003891 85847321333618665192505837)
      ·
        refine ⟨32192745500106999447189689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85847321333618665192505837 32192745500106999447189689)
        ·
          refine ⟨24144559125080249585392267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32192745500106999447189689 24144559125080249585392267)
          ·
            refine ⟨36216838687620374378088401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24144559125080249585392267 36216838687620374378088401)
            ·
              refine ⟨27162629015715280783566301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36216838687620374378088401 27162629015715280783566301)
              ·
                refine ⟨10185985880893230293837363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27162629015715280783566301 10185985880893230293837363)
                ·
                  refine ⟨15278978821339845440756045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10185985880893230293837363 15278978821339845440756045)
                  ·
                    refine ⟨5729617058002442040283517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15278978821339845440756045 5729617058002442040283517)
                    ·
                      refine ⟨2148606396750915765106319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5729617058002442040283517 2148606396750915765106319)
                      ·
                        rfl

theorem cell23_4184396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_4184396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184396 prefixEnd_4184396 := by exact prefixLift 4184396
  have htrace : WordTrace (prefixWord ++ tailWord_4184396) baseStart_4184396 baseEnd_4184396 := by
    simpa [prefixWord, tailWord_4184396, baseEnd_4184396] using wordTrace_append hprefix tailTrace_4184396
  have hstable : (prefixWord ++ tailWord_4184396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184396).length < 2 ^ (prefixWord ++ tailWord_4184396).sum := by decide
  have hdescent : baseEnd_4184396 < baseStart_4184396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184439 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 5]
def baseStart_4184439 : Nat := 118140960795 + 4184439 * 2 ^ 59
def prefixEnd_4184439 : Nat := 4983230072969 + 3 ^ 40 * 4184439 * 2
def baseEnd_4184439 : Nat := 2148628476419059096868621

theorem tailTrace_4184439 : CollatzResearch.WordTrace tailWord_4184439 prefixEnd_4184439 2148628476419059096868621 := by
  unfold tailWord_4184439
  simp only [CollatzResearch.WordTrace]
  refine ⟨152619028487499623130492371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101746018991666415420328247 152619028487499623130492371)
  ·
    refine ⟨228928542731249434695738557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152619028487499623130492371 228928542731249434695738557)
    ·
      refine ⟨85848203524218538010901959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228928542731249434695738557 85848203524218538010901959)
      ·
        refine ⟨128772305286327807016352939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85848203524218538010901959 128772305286327807016352939)
        ·
          refine ⟨193158457929491710524529409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128772305286327807016352939 193158457929491710524529409)
          ·
            refine ⟨144868843447118782893397057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193158457929491710524529409 144868843447118782893397057)
            ·
              refine ⟨108651632585339087170047793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144868843447118782893397057 108651632585339087170047793)
              ·
                refine ⟨81488724439004315377535845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108651632585339087170047793 81488724439004315377535845)
                ·
                  refine ⟨15279135832313309133287971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81488724439004315377535845 15279135832313309133287971)
                  ·
                    refine ⟨22918703748469963699931957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15279135832313309133287971 22918703748469963699931957)
                    ·
                      refine ⟨2148628476419059096868621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22918703748469963699931957 2148628476419059096868621)
                      ·
                        rfl

theorem cell23_4184439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_4184439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184439 prefixEnd_4184439 := by exact prefixLift 4184439
  have htrace : WordTrace (prefixWord ++ tailWord_4184439) baseStart_4184439 baseEnd_4184439 := by
    simpa [prefixWord, tailWord_4184439, baseEnd_4184439] using wordTrace_append hprefix tailTrace_4184439
  have hstable : (prefixWord ++ tailWord_4184439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184439).length < 2 ^ (prefixWord ++ tailWord_4184439).sum := by decide
  have hdescent : baseEnd_4184439 < baseStart_4184439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184453 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 6, 2, 2]
def baseStart_4184453 : Nat := 118140960795 + 4184453 * 2 ^ 59
def prefixEnd_4184453 : Nat := 4983230072969 + 3 ^ 40 * 4184453 * 2
def baseEnd_4184453 : Nat := 2148635665148222042093557

theorem tailTrace_4184453 : CollatzResearch.WordTrace tailWord_4184453 prefixEnd_4184453 2148635665148222042093557 := by
  unfold tailWord_4184453
  simp only [CollatzResearch.WordTrace]
  refine ⟨152619539109448903521502013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101746359406299269014334675 152619539109448903521502013)
  ·
    refine ⟨57232327166043338820563255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152619539109448903521502013 57232327166043338820563255)
    ·
      refine ⟨85848490749065008230844883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57232327166043338820563255 85848490749065008230844883)
      ·
        refine ⟨128772736123597512346267325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85848490749065008230844883 128772736123597512346267325)
        ·
          refine ⟨48289776046349067129850247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128772736123597512346267325 48289776046349067129850247)
          ·
            refine ⟨72434664069523600694775371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48289776046349067129850247 72434664069523600694775371)
            ·
              refine ⟨108651996104285401042163057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72434664069523600694775371 108651996104285401042163057)
              ·
                refine ⟨81488997078214050781622293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108651996104285401042163057 81488997078214050781622293)
                ·
                  refine ⟨3819796738041283630388545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81488997078214050781622293 3819796738041283630388545)
                  ·
                    refine ⟨2864847553530962722791409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3819796738041283630388545 2864847553530962722791409)
                    ·
                      refine ⟨2148635665148222042093557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2864847553530962722791409 2148635665148222042093557)
                      ·
                        rfl

theorem cell23_4184453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 2, 2].length) (baseStart_4184453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184453 prefixEnd_4184453 := by exact prefixLift 4184453
  have htrace : WordTrace (prefixWord ++ tailWord_4184453) baseStart_4184453 baseEnd_4184453 := by
    simpa [prefixWord, tailWord_4184453, baseEnd_4184453] using wordTrace_append hprefix tailTrace_4184453
  have hstable : (prefixWord ++ tailWord_4184453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184453).length < 2 ^ (prefixWord ++ tailWord_4184453).sum := by decide
  have hdescent : baseEnd_4184453 < baseStart_4184453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184456 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 2, 4, 3]
def baseStart_4184456 : Nat := 118140960795 + 4184456 * 2 ^ 59
def prefixEnd_4184456 : Nat := 4983230072969 + 3 ^ 40 * 4184456 * 2
def baseEnd_4184456 : Nat := 2148637205590185530356043

theorem tailTrace_4184456 : CollatzResearch.WordTrace tailWord_4184456 prefixEnd_4184456 2148637205590185530356043 := by
  unfold tailWord_4184456
  simp only [CollatzResearch.WordTrace]
  refine ⟨76309824264219017516930611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101746432352292023355907481 76309824264219017516930611)
  ·
    refine ⟨114464736396328526275395917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76309824264219017516930611 114464736396328526275395917)
    ·
      refine ⟨42924276148623197353273469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114464736396328526275395917 42924276148623197353273469)
      ·
        refine ⟨16096603555733699007477551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42924276148623197353273469 16096603555733699007477551)
        ·
          refine ⟨24144905333600548511216327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16096603555733699007477551 24144905333600548511216327)
          ·
            refine ⟨36217358000400822766824491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24144905333600548511216327 36217358000400822766824491)
            ·
              refine ⟨54326037000601234150236737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36217358000400822766824491 54326037000601234150236737)
              ·
                refine ⟨40744527750450925612677553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54326037000601234150236737 40744527750450925612677553)
                ·
                  refine ⟨30558395812838194209508165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40744527750450925612677553 30558395812838194209508165)
                  ·
                    refine ⟨5729699214907161414282781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30558395812838194209508165 5729699214907161414282781)
                    ·
                      refine ⟨2148637205590185530356043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5729699214907161414282781 2148637205590185530356043)
                      ·
                        rfl

theorem cell23_4184456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_4184456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184456 prefixEnd_4184456 := by exact prefixLift 4184456
  have htrace : WordTrace (prefixWord ++ tailWord_4184456) baseStart_4184456 baseEnd_4184456 := by
    simpa [prefixWord, tailWord_4184456, baseEnd_4184456] using wordTrace_append hprefix tailTrace_4184456
  have hstable : (prefixWord ++ tailWord_4184456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184456).length < 2 ^ (prefixWord ++ tailWord_4184456).sum := by decide
  have hdescent : baseEnd_4184456 < baseStart_4184456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184459 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 9]
def baseStart_4184459 : Nat := 118140960795 + 4184459 * 2 ^ 59
def prefixEnd_4184459 : Nat := 4983230072969 + 3 ^ 40 * 4184459 * 2
def baseEnd_4184459 : Nat := 238737638448016557624281

theorem tailTrace_4184459 : CollatzResearch.WordTrace tailWord_4184459 prefixEnd_4184459 238737638448016557624281 := by
  unfold tailWord_4184459
  simp only [CollatzResearch.WordTrace]
  refine ⟨152619757947427166546220431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101746505298284777697480287 152619757947427166546220431)
  ·
    refine ⟨228929636921140749819330647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152619757947427166546220431 228929636921140749819330647)
    ·
      refine ⟨343394455381711124728995971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228929636921140749819330647 343394455381711124728995971)
      ·
        refine ⟨515091683072566687093493957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343394455381711124728995971 515091683072566687093493957)
        ·
          refine ⟨96579690576106253830030117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 515091683072566687093493957 96579690576106253830030117)
          ·
            refine ⟨18108691983019922593130647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96579690576106253830030117 18108691983019922593130647)
            ·
              refine ⟨27163037974529883889695971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18108691983019922593130647 27163037974529883889695971)
              ·
                refine ⟨40744556961794825834543957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27163037974529883889695971 40744556961794825834543957)
                ·
                  refine ⟨238737638448016557624281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40744556961794825834543957 238737638448016557624281)
                  ·
                    rfl

theorem cell23_4184459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 9].length) (baseStart_4184459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184459 prefixEnd_4184459 := by exact prefixLift 4184459
  have htrace : WordTrace (prefixWord ++ tailWord_4184459) baseStart_4184459 baseEnd_4184459 := by
    simpa [prefixWord, tailWord_4184459, baseEnd_4184459] using wordTrace_append hprefix tailTrace_4184459
  have hstable : (prefixWord ++ tailWord_4184459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184459).length < 2 ^ (prefixWord ++ tailWord_4184459).sum := by decide
  have hdescent : baseEnd_4184459 < baseStart_4184459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184469 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 1, 2, 7]
def baseStart_4184469 : Nat := 118140960795 + 4184469 * 2 ^ 59
def prefixEnd_4184469 : Nat := 4983230072969 + 3 ^ 40 * 4184469 * 2
def baseEnd_4184469 : Nat := 2148643880838693979493483

theorem tailTrace_4184469 : CollatzResearch.WordTrace tailWord_4184469 prefixEnd_4184469 2148643880838693979493483 := by
  unfold tailWord_4184469
  simp only [CollatzResearch.WordTrace]
  refine ⟨152620122677390938254084461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101746748451593958836056307 152620122677390938254084461)
  ·
    refine ⟨57232546004021601845281673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152620122677390938254084461 57232546004021601845281673)
    ·
      refine ⟨42924409503016201383961255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57232546004021601845281673 42924409503016201383961255)
      ·
        refine ⟨64386614254524302075941883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42924409503016201383961255 64386614254524302075941883)
        ·
          refine ⟨96579921381786453113912825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64386614254524302075941883 96579921381786453113912825)
          ·
            refine ⟨72434941036339839835434619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96579921381786453113912825 72434941036339839835434619)
            ·
              refine ⟨108652411554509759753151929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72434941036339839835434619 108652411554509759753151929)
              ·
                refine ⟨81489308665882319814863947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108652411554509759753151929 81489308665882319814863947)
                ·
                  refine ⟨122233962998823479722295921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81489308665882319814863947 122233962998823479722295921)
                  ·
                    refine ⟨91675472249117609791721941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122233962998823479722295921 91675472249117609791721941)
                    ·
                      refine ⟨2148643880838693979493483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91675472249117609791721941 2148643880838693979493483)
                      ·
                        rfl

theorem cell23_4184469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_4184469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184469 prefixEnd_4184469 := by exact prefixLift 4184469
  have htrace : WordTrace (prefixWord ++ tailWord_4184469) baseStart_4184469 baseEnd_4184469 := by
    simpa [prefixWord, tailWord_4184469, baseEnd_4184469] using wordTrace_append hprefix tailTrace_4184469
  have hstable : (prefixWord ++ tailWord_4184469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184469).length < 2 ^ (prefixWord ++ tailWord_4184469).sum := by decide
  have hdescent : baseEnd_4184469 < baseStart_4184469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184487 : List Nat := [1, 1, 6, 1, 1, 2, 3, 2, 2, 2, 2]
def baseStart_4184487 : Nat := 118140960795 + 4184487 * 2 ^ 59
def prefixEnd_4184487 : Nat := 4983230072969 + 3 ^ 40 * 4184487 * 2
def baseEnd_4184487 : Nat := 2148653123490474909068401

theorem tailTrace_4184487 : CollatzResearch.WordTrace tailWord_4184487 prefixEnd_4184487 2148653123490474909068401 := by
  unfold tailWord_4184487
  simp only [CollatzResearch.WordTrace]
  refine ⟨152620779191325727328239715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101747186127550484885493143 152620779191325727328239715)
  ·
    refine ⟨228931168786988590992359573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152620779191325727328239715 228931168786988590992359573)
    ·
      refine ⟨10731148536890090202766855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 228931168786988590992359573 10731148536890090202766855)
      ·
        refine ⟨16096722805335135304150283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10731148536890090202766855 16096722805335135304150283)
        ·
          refine ⟨24145084208002702956225425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16096722805335135304150283 24145084208002702956225425)
          ·
            refine ⟨18108813156002027217169069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24145084208002702956225425 18108813156002027217169069)
            ·
              refine ⟨6790804933500760206438401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18108813156002027217169069 6790804933500760206438401)
              ·
                refine ⟨5093103700125570154828801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6790804933500760206438401 5093103700125570154828801)
                ·
                  refine ⟨3819827775094177616121601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5093103700125570154828801 3819827775094177616121601)
                  ·
                    refine ⟨2864870831320633212091201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3819827775094177616121601 2864870831320633212091201)
                    ·
                      refine ⟨2148653123490474909068401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2864870831320633212091201 2148653123490474909068401)
                      ·
                        rfl

theorem cell23_4184487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_4184487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184487 prefixEnd_4184487 := by exact prefixLift 4184487
  have htrace : WordTrace (prefixWord ++ tailWord_4184487) baseStart_4184487 baseEnd_4184487 := by
    simpa [prefixWord, tailWord_4184487, baseEnd_4184487] using wordTrace_append hprefix tailTrace_4184487
  have hstable : (prefixWord ++ tailWord_4184487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184487).length < 2 ^ (prefixWord ++ tailWord_4184487).sum := by decide
  have hdescent : baseEnd_4184487 < baseStart_4184487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184539 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 10]
def baseStart_4184539 : Nat := 118140960795 + 4184539 * 2 ^ 59
def prefixEnd_4184539 : Nat := 4983230072969 + 3 ^ 40 * 4184539 * 2
def baseEnd_4184539 : Nat := 2148679824484508705618161

theorem tailTrace_4184539 : CollatzResearch.WordTrace tailWord_4184539 prefixEnd_4184539 2148679824484508705618161 := by
  unfold tailWord_4184539
  simp only [CollatzResearch.WordTrace]
  refine ⟨152622675787137340209132671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101748450524758226806088447 152622675787137340209132671)
  ·
    refine ⟨228934013680706010313699007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152622675787137340209132671 228934013680706010313699007)
    ·
      refine ⟨343401020521059015470548511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228934013680706010313699007 343401020521059015470548511)
      ·
        refine ⟨515101530781588523205822767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343401020521059015470548511 515101530781588523205822767)
        ·
          refine ⟨772652296172382784808734151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515101530781588523205822767 772652296172382784808734151)
          ·
            refine ⟨1158978444258574177213101227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772652296172382784808734151 1158978444258574177213101227)
            ·
              refine ⟨1738467666387861265819651841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158978444258574177213101227 1738467666387861265819651841)
              ·
                refine ⟨1303850749790895949364738881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1738467666387861265819651841 1303850749790895949364738881)
                ·
                  refine ⟨977888062343171962023554161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1303850749790895949364738881 977888062343171962023554161)
                  ·
                    refine ⟨733416046757378971517665621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 977888062343171962023554161 733416046757378971517665621)
                    ·
                      refine ⟨2148679824484508705618161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 733416046757378971517665621 2148679824484508705618161)
                      ·
                        rfl

theorem cell23_4184539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 10].length) (baseStart_4184539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184539 prefixEnd_4184539 := by exact prefixLift 4184539
  have htrace : WordTrace (prefixWord ++ tailWord_4184539) baseStart_4184539 baseEnd_4184539 := by
    simpa [prefixWord, tailWord_4184539, baseEnd_4184539] using wordTrace_append hprefix tailTrace_4184539
  have hstable : (prefixWord ++ tailWord_4184539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184539).length < 2 ^ (prefixWord ++ tailWord_4184539).sum := by decide
  have hdescent : baseEnd_4184539 < baseStart_4184539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184543 : List Nat := [1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 4]
def baseStart_4184543 : Nat := 118140960795 + 4184543 * 2 ^ 59
def prefixEnd_4184543 : Nat := 4983230072969 + 3 ^ 40 * 4184543 * 2
def baseEnd_4184543 : Nat := 2148681878407126689968143

theorem tailTrace_4184543 : CollatzResearch.WordTrace tailWord_4184543 prefixEnd_4184543 2148681878407126689968143 := by
  unfold tailWord_4184543
  simp only [CollatzResearch.WordTrace]
  refine ⟨152622821679122848892278283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101748547786081899261518855 152622821679122848892278283)
  ·
    refine ⟨228934232518684273338417425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152622821679122848892278283 228934232518684273338417425)
    ·
      refine ⟨171700674389013205003813069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228934232518684273338417425 171700674389013205003813069)
      ·
        refine ⟨64387752895879951876429901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171700674389013205003813069 64387752895879951876429901)
        ·
          refine ⟨24145407335954981953661213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64387752895879951876429901 24145407335954981953661213)
          ·
            refine ⟨9054527750983118232622955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24145407335954981953661213 9054527750983118232622955)
            ·
              refine ⟨13581791626474677348934433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9054527750983118232622955 13581791626474677348934433)
              ·
                refine ⟨10186343719856008011700825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13581791626474677348934433 10186343719856008011700825)
                ·
                  refine ⟨7639757789892006008775619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10186343719856008011700825 7639757789892006008775619)
                  ·
                    refine ⟨11459636684838009013163429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7639757789892006008775619 11459636684838009013163429)
                    ·
                      refine ⟨2148681878407126689968143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11459636684838009013163429 2148681878407126689968143)
                      ·
                        rfl

theorem cell23_4184543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_4184543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184543 prefixEnd_4184543 := by exact prefixLift 4184543
  have htrace : WordTrace (prefixWord ++ tailWord_4184543) baseStart_4184543 baseEnd_4184543 := by
    simpa [prefixWord, tailWord_4184543, baseEnd_4184543] using wordTrace_append hprefix tailTrace_4184543
  have hstable : (prefixWord ++ tailWord_4184543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184543).length < 2 ^ (prefixWord ++ tailWord_4184543).sum := by decide
  have hdescent : baseEnd_4184543 < baseStart_4184543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184580 : List Nat := [2, 3, 2, 3, 1, 1, 1, 3, 2, 2, 3]
def baseStart_4184580 : Nat := 118140960795 + 4184580 * 2 ^ 59
def prefixEnd_4184580 : Nat := 4983230072969 + 3 ^ 40 * 4184580 * 2
def baseEnd_4184580 : Nat := 2148700877191343045205473

theorem tailTrace_4184580 : CollatzResearch.WordTrace tailWord_4184580 prefixEnd_4184580 2148700877191343045205473 := by
  unfold tailWord_4184580
  simp only [CollatzResearch.WordTrace]
  refine ⟨76312085589994402105687597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101749447453325869474250129 76312085589994402105687597)
  ·
    refine ⟨28617032096247900789632849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76312085589994402105687597 28617032096247900789632849)
    ·
      refine ⟨21462774072185925592224637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28617032096247900789632849 21462774072185925592224637)
      ·
        refine ⟨8048540277069722097084239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21462774072185925592224637 8048540277069722097084239)
        ·
          refine ⟨12072810415604583145626359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8048540277069722097084239 12072810415604583145626359)
          ·
            refine ⟨18109215623406874718439539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12072810415604583145626359 18109215623406874718439539)
            ·
              refine ⟨27163823435110312077659309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18109215623406874718439539 27163823435110312077659309)
              ·
                refine ⟨10186433788166367029122241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27163823435110312077659309 10186433788166367029122241)
                ·
                  refine ⟨7639825341124775271841681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10186433788166367029122241 7639825341124775271841681)
                  ·
                    refine ⟨5729869005843581453881261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7639825341124775271841681 5729869005843581453881261)
                    ·
                      refine ⟨2148700877191343045205473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5729869005843581453881261 2148700877191343045205473)
                      ·
                        rfl

theorem cell23_4184580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_4184580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184580 prefixEnd_4184580 := by exact prefixLift 4184580
  have htrace : WordTrace (prefixWord ++ tailWord_4184580) baseStart_4184580 baseEnd_4184580 := by
    simpa [prefixWord, tailWord_4184580, baseEnd_4184580] using wordTrace_append hprefix tailTrace_4184580
  have hstable : (prefixWord ++ tailWord_4184580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184580).length < 2 ^ (prefixWord ++ tailWord_4184580).sum := by decide
  have hdescent : baseEnd_4184580 < baseStart_4184580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184593 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 7, 1, 3]
def baseStart_4184593 : Nat := 118140960795 + 4184593 * 2 ^ 59
def prefixEnd_4184593 : Nat := 4983230072969 + 3 ^ 40 * 4184593 * 2
def baseEnd_4184593 : Nat := 2148707552439851494342913

theorem tailTrace_4184593 : CollatzResearch.WordTrace tailWord_4184593 prefixEnd_4184593 2148707552439851494342913 := by
  unfold tailWord_4184593
  simp only [CollatzResearch.WordTrace]
  refine ⟨152624645328941707431598433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101749763552627804954398955 152624645328941707431598433)
  ·
    refine ⟨114468483996706280573698825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152624645328941707431598433 114468483996706280573698825)
    ·
      refine ⟨85851362997529710430274119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114468483996706280573698825 85851362997529710430274119)
      ·
        refine ⟨128777044496294565645411179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85851362997529710430274119 128777044496294565645411179)
        ·
          refine ⟨193165566744441848468116769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128777044496294565645411179 193165566744441848468116769)
          ·
            refine ⟨144874175058331386351087577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193165566744441848468116769 144874175058331386351087577)
            ·
              refine ⟨108655631293748539763315683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144874175058331386351087577 108655631293748539763315683)
              ·
                refine ⟨162983446940622809644973525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108655631293748539763315683 162983446940622809644973525)
                ·
                  refine ⟨3819924537670847101054067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 162983446940622809644973525 3819924537670847101054067)
                  ·
                    refine ⟨5729886806506270651581101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3819924537670847101054067 5729886806506270651581101)
                    ·
                      refine ⟨2148707552439851494342913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5729886806506270651581101 2148707552439851494342913)
                      ·
                        rfl

theorem cell23_4184593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 1, 3].length) (baseStart_4184593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184593 prefixEnd_4184593 := by exact prefixLift 4184593
  have htrace : WordTrace (prefixWord ++ tailWord_4184593) baseStart_4184593 baseEnd_4184593 := by
    simpa [prefixWord, tailWord_4184593, baseEnd_4184593] using wordTrace_append hprefix tailTrace_4184593
  have hstable : (prefixWord ++ tailWord_4184593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184593).length < 2 ^ (prefixWord ++ tailWord_4184593).sum := by decide
  have hdescent : baseEnd_4184593 < baseStart_4184593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184604 : List Nat := [2, 2, 3, 1, 2, 4, 2, 2, 1, 4]
def baseStart_4184604 : Nat := 118140960795 + 4184604 * 2 ^ 59
def prefixEnd_4184604 : Nat := 4983230072969 + 3 ^ 40 * 4184604 * 2
def baseEnd_4184604 : Nat := 716237733575683650435121

theorem tailTrace_4184604 : CollatzResearch.WordTrace tailWord_4184604 prefixEnd_4184604 716237733575683650435121 := by
  unfold tailWord_4184604
  simp only [CollatzResearch.WordTrace]
  refine ⟨76312523265950928155124433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101750031021267904206832577 76312523265950928155124433)
  ·
    refine ⟨57234392449463196116343325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76312523265950928155124433 57234392449463196116343325)
    ·
      refine ⟨21462897168548698543628747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57234392449463196116343325 21462897168548698543628747)
      ·
        refine ⟨32194345752823047815443121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21462897168548698543628747 32194345752823047815443121)
        ·
          refine ⟨24145759314617285861582341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32194345752823047815443121 24145759314617285861582341)
          ·
            refine ⟨4527329871490741099046689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24145759314617285861582341 4527329871490741099046689)
            ·
              refine ⟨3395497403618055824285017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4527329871490741099046689 3395497403618055824285017)
              ·
                refine ⟨2546623052713541868213763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3395497403618055824285017 2546623052713541868213763)
                ·
                  refine ⟨3819934579070312802320645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2546623052713541868213763 3819934579070312802320645)
                  ·
                    refine ⟨716237733575683650435121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3819934579070312802320645 716237733575683650435121)
                    ·
                      rfl

theorem cell23_4184604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_4184604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184604 prefixEnd_4184604 := by exact prefixLift 4184604
  have htrace : WordTrace (prefixWord ++ tailWord_4184604) baseStart_4184604 baseEnd_4184604 := by
    simpa [prefixWord, tailWord_4184604, baseEnd_4184604] using wordTrace_append hprefix tailTrace_4184604
  have hstable : (prefixWord ++ tailWord_4184604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184604).length < 2 ^ (prefixWord ++ tailWord_4184604).sum := by decide
  have hdescent : baseEnd_4184604 < baseStart_4184604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184610 : List Nat := [3, 3, 1, 1, 1, 1, 1, 5, 3, 1, 3]
def baseStart_4184610 : Nat := 118140960795 + 4184610 * 2 ^ 59
def prefixEnd_4184610 : Nat := 4983230072969 + 3 ^ 40 * 4184610 * 2
def baseEnd_4184610 : Nat := 2148716281610977927830335

theorem tailTrace_4184610 : CollatzResearch.WordTrace tailWord_4184610 prefixEnd_4184610 2148716281610977927830335 := by
  unfold tailWord_4184610
  simp only [CollatzResearch.WordTrace]
  refine ⟨38156316342470029833741821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101750176913253412889978189 38156316342470029833741821)
  ·
    refine ⟨14308618628426261187653183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38156316342470029833741821 14308618628426261187653183)
    ·
      refine ⟨21462927942639391781479775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14308618628426261187653183 21462927942639391781479775)
      ·
        refine ⟨32194391913959087672219663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21462927942639391781479775 32194391913959087672219663)
        ·
          refine ⟨48291587870938631508329495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32194391913959087672219663 48291587870938631508329495)
          ·
            refine ⟨72437381806407947262494243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48291587870938631508329495 72437381806407947262494243)
            ·
              refine ⟨108656072709611920893741365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72437381806407947262494243 108656072709611920893741365)
              ·
                refine ⟨10186506816526117583788253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108656072709611920893741365 10186506816526117583788253)
                ·
                  refine ⟨3819940056197294093920595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10186506816526117583788253 3819940056197294093920595)
                  ·
                    refine ⟨5729910084295941140880893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3819940056197294093920595 5729910084295941140880893)
                    ·
                      refine ⟨2148716281610977927830335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5729910084295941140880893 2148716281610977927830335)
                      ·
                        rfl

theorem cell23_4184610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_4184610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184610 prefixEnd_4184610 := by exact prefixLift 4184610
  have htrace : WordTrace (prefixWord ++ tailWord_4184610) baseStart_4184610 baseEnd_4184610 := by
    simpa [prefixWord, tailWord_4184610, baseEnd_4184610] using wordTrace_append hprefix tailTrace_4184610
  have hstable : (prefixWord ++ tailWord_4184610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184610).length < 2 ^ (prefixWord ++ tailWord_4184610).sum := by decide
  have hdescent : baseEnd_4184610 < baseStart_4184610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184630 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 3, 5]
def baseStart_4184630 : Nat := 118140960795 + 4184630 * 2 ^ 59
def prefixEnd_4184630 : Nat := 4983230072969 + 3 ^ 40 * 4184630 * 2
def baseEnd_4184630 : Nat := 716242183741355949860081

theorem tailTrace_4184630 : CollatzResearch.WordTrace tailWord_4184630 prefixEnd_4184630 716242183741355949860081 := by
  unfold tailWord_4184630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9539124676862978921918459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101750663219871775167130229 9539124676862978921918459)
  ·
    refine ⟨14308687015294468382877689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9539124676862978921918459 14308687015294468382877689)
    ·
      refine ⟨10731515261470851287158267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14308687015294468382877689 10731515261470851287158267)
      ·
        refine ⟨16097272892206276930737401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10731515261470851287158267 16097272892206276930737401)
        ·
          refine ⟨12072954669154707698053051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16097272892206276930737401 12072954669154707698053051)
          ·
            refine ⟨18109432003732061547079577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12072954669154707698053051 18109432003732061547079577)
            ·
              refine ⟨13582074002799046160309683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18109432003732061547079577 13582074002799046160309683)
              ·
                refine ⟨20373111004198569240464525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13582074002799046160309683 20373111004198569240464525)
                ·
                  refine ⟨7639916626574463465174197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20373111004198569240464525 7639916626574463465174197)
                  ·
                    refine ⟨716242183741355949860081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7639916626574463465174197 716242183741355949860081)
                    ·
                      rfl

theorem cell23_4184630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_4184630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184630 prefixEnd_4184630 := by exact prefixLift 4184630
  have htrace : WordTrace (prefixWord ++ tailWord_4184630) baseStart_4184630 baseEnd_4184630 := by
    simpa [prefixWord, tailWord_4184630, baseEnd_4184630] using wordTrace_append hprefix tailTrace_4184630
  have hstable : (prefixWord ++ tailWord_4184630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184630).length < 2 ^ (prefixWord ++ tailWord_4184630).sum := by decide
  have hdescent : baseEnd_4184630 < baseStart_4184630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184633 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 3, 1, 4]
def baseStart_4184633 : Nat := 118140960795 + 4184633 * 2 ^ 59
def prefixEnd_4184633 : Nat := 4983230072969 + 3 ^ 40 * 4184633 * 2
def baseEnd_4184633 : Nat := 2148728091666031337842729

theorem tailTrace_4184633 : CollatzResearch.WordTrace tailWord_4184633 prefixEnd_4184633 2148728091666031337842729 := by
  unfold tailWord_4184633
  simp only [CollatzResearch.WordTrace]
  refine ⟨152626104248796794263054553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101750736165864529508703035 152626104248796794263054553)
  ·
    refine ⟨114469578186597595697290915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152626104248796794263054553 114469578186597595697290915)
    ·
      refine ⟨171704367279896393545936373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114469578186597595697290915 171704367279896393545936373)
      ·
        refine ⟨16097284432490286894931535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171704367279896393545936373 16097284432490286894931535)
        ·
          refine ⟨24145926648735430342397303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16097284432490286894931535 24145926648735430342397303)
          ·
            refine ⟨36218889973103145513595955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24145926648735430342397303 36218889973103145513595955)
            ·
              refine ⟨54328334959654718270393933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36218889973103145513595955 54328334959654718270393933)
              ·
                refine ⟨20373125609870519351397725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54328334959654718270393933 20373125609870519351397725)
                ·
                  refine ⟨7639922103701444756774147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20373125609870519351397725 7639922103701444756774147)
                  ·
                    refine ⟨11459883155552167135161221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7639922103701444756774147 11459883155552167135161221)
                    ·
                      refine ⟨2148728091666031337842729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11459883155552167135161221 2148728091666031337842729)
                      ·
                        rfl

theorem cell23_4184633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_4184633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184633 prefixEnd_4184633 := by exact prefixLift 4184633
  have htrace : WordTrace (prefixWord ++ tailWord_4184633) baseStart_4184633 baseEnd_4184633 := by
    simpa [prefixWord, tailWord_4184633, baseEnd_4184633] using wordTrace_append hprefix tailTrace_4184633
  have hstable : (prefixWord ++ tailWord_4184633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184633).length < 2 ^ (prefixWord ++ tailWord_4184633).sum := by decide
  have hdescent : baseEnd_4184633 < baseStart_4184633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184637 : List Nat := [1, 4, 1, 3, 2, 1, 3, 1, 2, 3, 2]
def baseStart_4184637 : Nat := 118140960795 + 4184637 * 2 ^ 59
def prefixEnd_4184637 : Nat := 4983230072969 + 3 ^ 40 * 4184637 * 2
def baseEnd_4184637 : Nat := 2148730145588649322192711

theorem tailTrace_4184637 : CollatzResearch.WordTrace tailWord_4184637 prefixEnd_4184637 2148730145588649322192711 := by
  unfold tailWord_4184637
  simp only [CollatzResearch.WordTrace]
  refine ⟨152626250140782302946200165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101750833427188201964133443 152626250140782302946200165)
  ·
    refine ⟨28617421901396681802412531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152626250140782302946200165 28617421901396681802412531)
    ·
      refine ⟨42926132852095022703618797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28617421901396681802412531 42926132852095022703618797)
      ·
        refine ⟨16097299819535633513857049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42926132852095022703618797 16097299819535633513857049)
        ·
          refine ⟨12072974864651725135392787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16097299819535633513857049 12072974864651725135392787)
          ·
            refine ⟨18109462296977587703089181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12072974864651725135392787 18109462296977587703089181)
            ·
              refine ⟨6791048361366595388658443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18109462296977587703089181 6791048361366595388658443)
              ·
                refine ⟨10186572542049893082987665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6791048361366595388658443 10186572542049893082987665)
                ·
                  refine ⟨7639929406537419812240749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10186572542049893082987665 7639929406537419812240749)
                  ·
                    refine ⟨2864973527451532429590281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7639929406537419812240749 2864973527451532429590281)
                    ·
                      refine ⟨2148730145588649322192711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2864973527451532429590281 2148730145588649322192711)
                      ·
                        rfl

theorem cell23_4184637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_4184637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184637 prefixEnd_4184637 := by exact prefixLift 4184637
  have htrace : WordTrace (prefixWord ++ tailWord_4184637) baseStart_4184637 baseEnd_4184637 := by
    simpa [prefixWord, tailWord_4184637, baseEnd_4184637] using wordTrace_append hprefix tailTrace_4184637
  have hstable : (prefixWord ++ tailWord_4184637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184637).length < 2 ^ (prefixWord ++ tailWord_4184637).sum := by decide
  have hdescent : baseEnd_4184637 < baseStart_4184637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184647 : List Nat := [1, 1, 4, 1, 4, 3, 2, 1, 1, 5]
def baseStart_4184647 : Nat := 118140960795 + 4184647 * 2 ^ 59
def prefixEnd_4184647 : Nat := 4983230072969 + 3 ^ 40 * 4184647 * 2
def baseEnd_4184647 : Nat := 716245093465064761022555

theorem tailTrace_4184647 : CollatzResearch.WordTrace tailWord_4184647 prefixEnd_4184647 716245093465064761022555 := by
  unfold tailWord_4184647
  simp only [CollatzResearch.WordTrace]
  refine ⟨152626614870746074654064195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101751076580497383102709463 152626614870746074654064195)
  ·
    refine ⟨228939922306119111981096293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152626614870746074654064195 228939922306119111981096293)
    ·
      refine ⟨42926235432397333496455555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228939922306119111981096293 42926235432397333496455555)
      ·
        refine ⟨64389353148596000244683333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42926235432397333496455555 64389353148596000244683333)
        ·
          refine ⟨12073003715361750045878125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64389353148596000244683333 12073003715361750045878125)
          ·
            refine ⟨4527376393260656267204297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12073003715361750045878125 4527376393260656267204297)
            ·
              refine ⟨3395532294945492200403223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4527376393260656267204297 3395532294945492200403223)
              ·
                refine ⟨5093298442418238300604835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3395532294945492200403223 5093298442418238300604835)
                ·
                  refine ⟨7639947663627357450907253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5093298442418238300604835 7639947663627357450907253)
                  ·
                    refine ⟨716245093465064761022555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7639947663627357450907253 716245093465064761022555)
                    ·
                      rfl

theorem cell23_4184647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_4184647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184647 prefixEnd_4184647 := by exact prefixLift 4184647
  have htrace : WordTrace (prefixWord ++ tailWord_4184647) baseStart_4184647 baseEnd_4184647 := by
    simpa [prefixWord, tailWord_4184647, baseEnd_4184647] using wordTrace_append hprefix tailTrace_4184647
  have hstable : (prefixWord ++ tailWord_4184647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184647).length < 2 ^ (prefixWord ++ tailWord_4184647).sum := by decide
  have hdescent : baseEnd_4184647 < baseStart_4184647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184650 : List Nat := [3, 1, 2, 1, 1, 5, 1, 3, 1, 1, 4]
def baseStart_4184650 : Nat := 118140960795 + 4184650 * 2 ^ 59
def prefixEnd_4184650 : Nat := 4983230072969 + 3 ^ 40 * 4184650 * 2
def baseEnd_4184650 : Nat := 2148736820837157771330151

theorem tailTrace_4184650 : CollatzResearch.WordTrace tailWord_4184650 prefixEnd_4184650 2148736820837157771330151 := by
  unfold tailWord_4184650
  simp only [CollatzResearch.WordTrace]
  refine ⟨38156681072433801541605851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101751149526490137444282269 38156681072433801541605851)
  ·
    refine ⟨57235021608650702312408777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38156681072433801541605851 57235021608650702312408777)
    ·
      refine ⟨42926266206488026734306583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57235021608650702312408777 42926266206488026734306583)
      ·
        refine ⟨64389399309732040101459875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42926266206488026734306583 64389399309732040101459875)
        ·
          refine ⟨96584098964598060152189813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64389399309732040101459875 96584098964598060152189813)
          ·
            refine ⟨9054759277931068139267795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96584098964598060152189813 9054759277931068139267795)
            ·
              refine ⟨13582138916896602208901693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9054759277931068139267795 13582138916896602208901693)
              ·
                refine ⟨5093302093836225828338135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13582138916896602208901693 5093302093836225828338135)
                ·
                  refine ⟨7639953140754338742507203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5093302093836225828338135 7639953140754338742507203)
                  ·
                    refine ⟨11459929711131508113760805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7639953140754338742507203 11459929711131508113760805)
                    ·
                      refine ⟨2148736820837157771330151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11459929711131508113760805 2148736820837157771330151)
                      ·
                        rfl

theorem cell23_4184650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_4184650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184650 prefixEnd_4184650 := by exact prefixLift 4184650
  have htrace : WordTrace (prefixWord ++ tailWord_4184650) baseStart_4184650 baseEnd_4184650 := by
    simpa [prefixWord, tailWord_4184650, baseEnd_4184650] using wordTrace_append hprefix tailTrace_4184650
  have hstable : (prefixWord ++ tailWord_4184650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184650).length < 2 ^ (prefixWord ++ tailWord_4184650).sum := by decide
  have hdescent : baseEnd_4184650 < baseStart_4184650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184660 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 4, 4]
def baseStart_4184660 : Nat := 118140960795 + 4184660 * 2 ^ 59
def prefixEnd_4184660 : Nat := 4983230072969 + 3 ^ 40 * 4184660 * 2
def baseEnd_4184660 : Nat := 716247318547900910735035

theorem tailTrace_4184660 : CollatzResearch.WordTrace tailWord_4184660 prefixEnd_4184660 716247318547900910735035 := by
  unfold tailWord_4184660
  simp only [CollatzResearch.WordTrace]
  refine ⟨76313544509849488937143717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101751392679799318582858289 76313544509849488937143717)
  ·
    refine ⟨14308789595596779175714447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76313544509849488937143717 14308789595596779175714447)
    ·
      refine ⟨21463184393395168763571671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14308789595596779175714447 21463184393395168763571671)
      ·
        refine ⟨32194776590092753145357507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21463184393395168763571671 32194776590092753145357507)
        ·
          refine ⟨48292164885139129718036261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32194776590092753145357507 48292164885139129718036261)
          ·
            refine ⟨9054780915963586822131799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48292164885139129718036261 9054780915963586822131799)
            ·
              refine ⟨13582171373945380233197699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9054780915963586822131799 13582171373945380233197699)
              ·
                refine ⟨20373257060918070349796549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13582171373945380233197699 20373257060918070349796549)
                ·
                  refine ⟨3819985698922138190586853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20373257060918070349796549 3819985698922138190586853)
                  ·
                    refine ⟨716247318547900910735035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3819985698922138190586853 716247318547900910735035)
                    ·
                      rfl

theorem cell23_4184660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_4184660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184660 prefixEnd_4184660 := by exact prefixLift 4184660
  have htrace : WordTrace (prefixWord ++ tailWord_4184660) baseStart_4184660 baseEnd_4184660 := by
    simpa [prefixWord, tailWord_4184660, baseEnd_4184660] using wordTrace_append hprefix tailTrace_4184660
  have hstable : (prefixWord ++ tailWord_4184660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184660).length < 2 ^ (prefixWord ++ tailWord_4184660).sum := by decide
  have hdescent : baseEnd_4184660 < baseStart_4184660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184666 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7]
def baseStart_4184666 : Nat := 118140960795 + 4184666 * 2 ^ 59
def prefixEnd_4184666 : Nat := 4983230072969 + 3 ^ 40 * 4184666 * 2
def baseEnd_4184666 : Nat := 2148745036527629708730077

theorem tailTrace_4184666 : CollatzResearch.WordTrace tailWord_4184666 prefixEnd_4184666 2148745036527629708730077 := by
  unfold tailWord_4184666
  simp only [CollatzResearch.WordTrace]
  refine ⟨38156826964419310224751463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101751538571784827266003901 38156826964419310224751463)
  ·
    refine ⟨57235240446628965337127195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38156826964419310224751463 57235240446628965337127195)
    ·
      refine ⟨85852860669943448005690793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57235240446628965337127195 85852860669943448005690793)
      ·
        refine ⟨64389645502457586004268095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85852860669943448005690793 64389645502457586004268095)
        ·
          refine ⟨96584468253686379006402143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64389645502457586004268095 96584468253686379006402143)
          ·
            refine ⟨144876702380529568509603215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96584468253686379006402143 144876702380529568509603215)
            ·
              refine ⟨217315053570794352764404823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144876702380529568509603215 217315053570794352764404823)
              ·
                refine ⟨325972580356191529146607235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217315053570794352764404823 325972580356191529146607235)
                ·
                  refine ⟨488958870534287293719910853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325972580356191529146607235 488958870534287293719910853)
                  ·
                    refine ⟨91679788225178867572483285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 488958870534287293719910853 91679788225178867572483285)
                    ·
                      refine ⟨2148745036527629708730077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91679788225178867572483285 2148745036527629708730077)
                      ·
                        rfl

theorem cell23_4184666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_4184666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184666 prefixEnd_4184666 := by exact prefixLift 4184666
  have htrace : WordTrace (prefixWord ++ tailWord_4184666) baseStart_4184666 baseEnd_4184666 := by
    simpa [prefixWord, tailWord_4184666, baseEnd_4184666] using wordTrace_append hprefix tailTrace_4184666
  have hstable : (prefixWord ++ tailWord_4184666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184666).length < 2 ^ (prefixWord ++ tailWord_4184666).sum := by decide
  have hdescent : baseEnd_4184666 < baseStart_4184666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184677 : List Nat := [1, 3, 1, 3, 5, 1, 1, 1, 1, 6]
def baseStart_4184677 : Nat := 118140960795 + 4184677 * 2 ^ 59
def prefixEnd_4184677 : Nat := 4983230072969 + 3 ^ 40 * 4184677 * 2
def baseEnd_4184677 : Nat := 716250228271609721897509

theorem tailTrace_4184677 : CollatzResearch.WordTrace tailWord_4184677 prefixEnd_4184677 716250228271609721897509 := by
  unfold tailWord_4184677
  simp only [CollatzResearch.WordTrace]
  refine ⟨152627709060637389777656285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101751806040424926518437523 152627709060637389777656285)
  ·
    refine ⟨57235390897739021166621107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152627709060637389777656285 57235390897739021166621107)
    ·
      refine ⟨85853086346608531749931661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57235390897739021166621107 85853086346608531749931661)
      ·
        refine ⟨32194907379978199406224373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85853086346608531749931661 32194907379978199406224373)
        ·
          refine ⟨3018272566872956194333535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32194907379978199406224373 3018272566872956194333535)
          ·
            refine ⟨4527408850309434291500303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3018272566872956194333535 4527408850309434291500303)
            ·
              refine ⟨6791113275464151437250455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4527408850309434291500303 6791113275464151437250455)
              ·
                refine ⟨10186669913196227155875683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6791113275464151437250455 10186669913196227155875683)
                ·
                  refine ⟨15280004869794340733813525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10186669913196227155875683 15280004869794340733813525)
                  ·
                    refine ⟨716250228271609721897509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15280004869794340733813525 716250228271609721897509)
                    ·
                      rfl

theorem cell23_4184677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 1, 6].length) (baseStart_4184677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184677 prefixEnd_4184677 := by exact prefixLift 4184677
  have htrace : WordTrace (prefixWord ++ tailWord_4184677) baseStart_4184677 baseEnd_4184677 := by
    simpa [prefixWord, tailWord_4184677, baseEnd_4184677] using wordTrace_append hprefix tailTrace_4184677
  have hstable : (prefixWord ++ tailWord_4184677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184677).length < 2 ^ (prefixWord ++ tailWord_4184677).sum := by decide
  have hdescent : baseEnd_4184677 < baseStart_4184677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184680 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 1, 1, 6]
def baseStart_4184680 : Nat := 118140960795 + 4184680 * 2 ^ 59
def prefixEnd_4184680 : Nat := 4983230072969 + 3 ^ 40 * 4184680 * 2
def baseEnd_4184680 : Nat := 2148752225256792653955013

theorem tailTrace_4184680 : CollatzResearch.WordTrace tailWord_4184680 prefixEnd_4184680 2148752225256792653955013 := by
  unfold tailWord_4184680
  simp only [CollatzResearch.WordTrace]
  refine ⟨76313909239813260645007747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101751878986417680860010329 76313909239813260645007747)
  ·
    refine ⟨114470863859719890967511621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76313909239813260645007747 114470863859719890967511621)
    ·
      refine ⟨21463286973697479556408429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114470863859719890967511621 21463286973697479556408429)
      ·
        refine ⟨8048732615136554833653161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21463286973697479556408429 8048732615136554833653161)
        ·
          refine ⟨6036549461352416125239871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8048732615136554833653161 6036549461352416125239871)
          ·
            refine ⟨9054824192028624187859807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6036549461352416125239871 9054824192028624187859807)
            ·
              refine ⟨13582236288042936281789711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9054824192028624187859807 13582236288042936281789711)
              ·
                refine ⟨20373354432064404422684567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13582236288042936281789711 20373354432064404422684567)
                ·
                  refine ⟨30560031648096606634026851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20373354432064404422684567 30560031648096606634026851)
                  ·
                    refine ⟨45840047472144909951040277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30560031648096606634026851 45840047472144909951040277)
                    ·
                      refine ⟨2148752225256792653955013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45840047472144909951040277 2148752225256792653955013)
                      ·
                        rfl

theorem cell23_4184680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_4184680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184680 prefixEnd_4184680 := by exact prefixLift 4184680
  have htrace : WordTrace (prefixWord ++ tailWord_4184680) baseStart_4184680 baseEnd_4184680 := by
    simpa [prefixWord, tailWord_4184680, baseEnd_4184680] using wordTrace_append hprefix tailTrace_4184680
  have hstable : (prefixWord ++ tailWord_4184680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184680).length < 2 ^ (prefixWord ++ tailWord_4184680).sum := by decide
  have hdescent : baseEnd_4184680 < baseStart_4184680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184683 : List Nat := [1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 3]
def baseStart_4184683 : Nat := 118140960795 + 4184683 * 2 ^ 59
def prefixEnd_4184683 : Nat := 4983230072969 + 3 ^ 40 * 4184683 * 2
def baseEnd_4184683 : Nat := 2148753765698756142217499

theorem tailTrace_4184683 : CollatzResearch.WordTrace tailWord_4184683 prefixEnd_4184683 2148753765698756142217499 := by
  unfold tailWord_4184683
  simp only [CollatzResearch.WordTrace]
  refine ⟨152627927898615652802374703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101751951932410435201583135 152627927898615652802374703)
  ·
    refine ⟨228941891847923479203562055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152627927898615652802374703 228941891847923479203562055)
    ·
      refine ⟨343412837771885218805343083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228941891847923479203562055 343412837771885218805343083)
      ·
        refine ⟨515119256657827828208014625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343412837771885218805343083 515119256657827828208014625)
        ·
          refine ⟨386339442493370871156010969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515119256657827828208014625 386339442493370871156010969)
          ·
            refine ⟨289754581870028153367008227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386339442493370871156010969 289754581870028153367008227)
            ·
              refine ⟨434631872805042230050512341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289754581870028153367008227 434631872805042230050512341)
              ·
                refine ⟨10186684518868177266808883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 434631872805042230050512341 10186684518868177266808883)
                ·
                  refine ⟨15280026778302265900213325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10186684518868177266808883 15280026778302265900213325)
                  ·
                    refine ⟨5730010041863349712579997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15280026778302265900213325 5730010041863349712579997)
                    ·
                      refine ⟨2148753765698756142217499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5730010041863349712579997 2148753765698756142217499)
                      ·
                        rfl

theorem cell23_4184683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 3].length) (baseStart_4184683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184683 prefixEnd_4184683 := by exact prefixLift 4184683
  have htrace : WordTrace (prefixWord ++ tailWord_4184683) baseStart_4184683 baseEnd_4184683 := by
    simpa [prefixWord, tailWord_4184683, baseEnd_4184683] using wordTrace_append hprefix tailTrace_4184683
  have hstable : (prefixWord ++ tailWord_4184683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184683).length < 2 ^ (prefixWord ++ tailWord_4184683).sum := by decide
  have hdescent : baseEnd_4184683 < baseStart_4184683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184700 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 4, 1, 3]
def baseStart_4184700 : Nat := 118140960795 + 4184700 * 2 ^ 59
def prefixEnd_4184700 : Nat := 4983230072969 + 3 ^ 40 * 4184700 * 2
def baseEnd_4184700 : Nat := 2148762494869882575704921

theorem tailTrace_4184700 : CollatzResearch.WordTrace tailWord_4184700 prefixEnd_4184700 2148762494869882575704921 := by
  unfold tailWord_4184700
  simp only [CollatzResearch.WordTrace]
  refine ⟨76314273969777032352871777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101752365293036043137162369 76314273969777032352871777)
  ·
    refine ⟨57235705477332774264653833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76314273969777032352871777 57235705477332774264653833)
    ·
      refine ⟨42926779107999580698490375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57235705477332774264653833 42926779107999580698490375)
      ·
        refine ⟨64390168661999371047735563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42926779107999580698490375 64390168661999371047735563)
        ·
          refine ⟨96585252992999056571603345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64390168661999371047735563 96585252992999056571603345)
          ·
            refine ⟨72438939744749292428702509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96585252992999056571603345 72438939744749292428702509)
            ·
              refine ⟨27164602404280984660763441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72438939744749292428702509 27164602404280984660763441)
              ·
                refine ⟨20373451803210738495572581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27164602404280984660763441 20373451803210738495572581)
                ·
                  refine ⟨3820022213102013467919859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20373451803210738495572581 3820022213102013467919859)
                  ·
                    refine ⟨5730033319653020201879789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3820022213102013467919859 5730033319653020201879789)
                    ·
                      refine ⟨2148762494869882575704921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5730033319653020201879789 2148762494869882575704921)
                      ·
                        rfl

theorem cell23_4184700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_4184700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184700 prefixEnd_4184700 := by exact prefixLift 4184700
  have htrace : WordTrace (prefixWord ++ tailWord_4184700) baseStart_4184700 baseEnd_4184700 := by
    simpa [prefixWord, tailWord_4184700, baseEnd_4184700] using wordTrace_append hprefix tailTrace_4184700
  have hstable : (prefixWord ++ tailWord_4184700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184700).length < 2 ^ (prefixWord ++ tailWord_4184700).sum := by decide
  have hdescent : baseEnd_4184700 < baseStart_4184700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184733 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 2, 6]
def baseStart_4184733 : Nat := 118140960795 + 4184733 * 2 ^ 59
def prefixEnd_4184733 : Nat := 4983230072969 + 3 ^ 40 * 4184733 * 2
def baseEnd_4184733 : Nat := 716259813243826982197423

theorem tailTrace_4184733 : CollatzResearch.WordTrace tailWord_4184733 prefixEnd_4184733 716259813243826982197423 := by
  unfold tailWord_4184733
  simp only [CollatzResearch.WordTrace]
  refine ⟨152629751548434511341694853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101753167698956340894463235 152629751548434511341694853)
  ·
    refine ⟨28618078415331470876567785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152629751548434511341694853 28618078415331470876567785)
    ·
      refine ⟨21463558811498603157425839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28618078415331470876567785 21463558811498603157425839)
      ·
        refine ⟨32195338217247904736138759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21463558811498603157425839 32195338217247904736138759)
        ·
          refine ⟨48293007325871857104208139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32195338217247904736138759 48293007325871857104208139)
          ·
            refine ⟨72439510988807785656312209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48293007325871857104208139 72439510988807785656312209)
            ·
              refine ⟨54329633241605839242234157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72439510988807785656312209 54329633241605839242234157)
              ·
                refine ⟨20373612465602189715837809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54329633241605839242234157 20373612465602189715837809)
                ·
                  refine ⟨15280209349201642286878357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20373612465602189715837809 15280209349201642286878357)
                  ·
                    refine ⟨716259813243826982197423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15280209349201642286878357 716259813243826982197423)
                    ·
                      rfl

theorem cell23_4184733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_4184733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184733 prefixEnd_4184733 := by exact prefixLift 4184733
  have htrace : WordTrace (prefixWord ++ tailWord_4184733) baseStart_4184733 baseEnd_4184733 := by
    simpa [prefixWord, tailWord_4184733, baseEnd_4184733] using wordTrace_append hprefix tailTrace_4184733
  have hstable : (prefixWord ++ tailWord_4184733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184733).length < 2 ^ (prefixWord ++ tailWord_4184733).sum := by decide
  have hdescent : baseEnd_4184733 < baseStart_4184733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184734 : List Nat := [4, 3, 1, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_4184734 : Nat := 118140960795 + 4184734 * 2 ^ 59
def prefixEnd_4184734 : Nat := 4983230072969 + 3 ^ 40 * 4184734 * 2
def baseEnd_4184734 : Nat := 2148779953212135442679765

theorem tailTrace_4184734 : CollatzResearch.WordTrace tailWord_4184734 prefixEnd_4184734 2148779953212135442679765 := by
  unfold tailWord_4184734
  simp only [CollatzResearch.WordTrace]
  refine ⟨19078723502678861064060157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101753192014287259008320837 19078723502678861064060157)
  ·
    refine ⟨7154521313504572899022559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19078723502678861064060157 7154521313504572899022559)
    ·
      refine ⟨10731781970256859348533839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7154521313504572899022559 10731781970256859348533839)
      ·
        refine ⟨16097672955385289022800759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10731781970256859348533839 16097672955385289022800759)
        ·
          refine ⟨24146509433077933534201139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16097672955385289022800759 24146509433077933534201139)
          ·
            refine ⟨36219764149616900301301709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24146509433077933534201139 36219764149616900301301709)
            ·
              refine ⟨13582411556106337612988141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36219764149616900301301709 13582411556106337612988141)
              ·
                refine ⟨5093404333539876604870553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13582411556106337612988141 5093404333539876604870553)
                ·
                  refine ⟨3820053250154907453652915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5093404333539876604870553 3820053250154907453652915)
                  ·
                    refine ⟨5730079875232361180479373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3820053250154907453652915 5730079875232361180479373)
                    ·
                      refine ⟨2148779953212135442679765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5730079875232361180479373 2148779953212135442679765)
                      ·
                        rfl

theorem cell23_4184734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_4184734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184734 prefixEnd_4184734 := by exact prefixLift 4184734
  have htrace : WordTrace (prefixWord ++ tailWord_4184734) baseStart_4184734 baseEnd_4184734 := by
    simpa [prefixWord, tailWord_4184734, baseEnd_4184734] using wordTrace_append hprefix tailTrace_4184734
  have hstable : (prefixWord ++ tailWord_4184734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184734).length < 2 ^ (prefixWord ++ tailWord_4184734).sum := by decide
  have hdescent : baseEnd_4184734 < baseStart_4184734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184757 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 3, 4, 2]
def baseStart_4184757 : Nat := 118140960795 + 4184757 * 2 ^ 59
def prefixEnd_4184757 : Nat := 4983230072969 + 3 ^ 40 * 4184757 * 2
def baseEnd_4184757 : Nat := 2148791763267188852692159

theorem tailTrace_4184757 : CollatzResearch.WordTrace tailWord_4184757 prefixEnd_4184757 2148791763267188852692159 := by
  unfold tailWord_4184757
  simp only [CollatzResearch.WordTrace]
  refine ⟨152630626900347563440568525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101753751266898375627045683 152630626900347563440568525)
  ·
    refine ⟨57236485087630336290213197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152630626900347563440568525 57236485087630336290213197)
    ·
      refine ⟨21463681907861376108829949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57236485087630336290213197 21463681907861376108829949)
      ·
        refine ⟨8048880715448016040811231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21463681907861376108829949 8048880715448016040811231)
        ·
          refine ⟨12073321073172024061216847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8048880715448016040811231 12073321073172024061216847)
          ·
            refine ⟨18109981609758036091825271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12073321073172024061216847 18109981609758036091825271)
            ·
              refine ⟨27164972414637054137737907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18109981609758036091825271 27164972414637054137737907)
              ·
                refine ⟨40747458621955581206606861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27164972414637054137737907 40747458621955581206606861)
                ·
                  refine ⟨15280296983233342952477573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40747458621955581206606861 15280296983233342952477573)
                  ·
                    refine ⟨2865055684356251803589545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15280296983233342952477573 2865055684356251803589545)
                    ·
                      refine ⟨2148791763267188852692159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2865055684356251803589545 2148791763267188852692159)
                      ·
                        rfl

theorem cell23_4184757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_4184757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184757 prefixEnd_4184757 := by exact prefixLift 4184757
  have htrace : WordTrace (prefixWord ++ tailWord_4184757) baseStart_4184757 baseEnd_4184757 := by
    simpa [prefixWord, tailWord_4184757, baseEnd_4184757] using wordTrace_append hprefix tailTrace_4184757
  have hstable : (prefixWord ++ tailWord_4184757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184757).length < 2 ^ (prefixWord ++ tailWord_4184757).sum := by decide
  have hdescent : baseEnd_4184757 < baseStart_4184757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184793 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 1, 7]
def baseStart_4184793 : Nat := 118140960795 + 4184793 * 2 ^ 59
def prefixEnd_4184793 : Nat := 4983230072969 + 3 ^ 40 * 4184793 * 2
def baseEnd_4184793 : Nat := 716270082856916903947331

theorem tailTrace_4184793 : CollatzResearch.WordTrace tailWord_4184793 prefixEnd_4184793 716270082856916903947331 := by
  unfold tailWord_4184793
  simp only [CollatzResearch.WordTrace]
  refine ⟨152631939928217141588879033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101754626618811427725919355 152631939928217141588879033)
  ·
    refine ⟨114473954946162856191659275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152631939928217141588879033 114473954946162856191659275)
    ·
      refine ⟨171710932419244284287488913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114473954946162856191659275 171710932419244284287488913)
      ·
        refine ⟨128783199314433213215616685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171710932419244284287488913 128783199314433213215616685)
        ·
          refine ⟨48293699742912454955856257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128783199314433213215616685 48293699742912454955856257)
          ·
            refine ⟨36220274807184341216892193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48293699742912454955856257 36220274807184341216892193)
            ·
              refine ⟨27165206105388255912669145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36220274807184341216892193 27165206105388255912669145)
              ·
                refine ⟨20373904579041191934501859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27165206105388255912669145 20373904579041191934501859)
                ·
                  refine ⟨30560856868561787901752789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20373904579041191934501859 30560856868561787901752789)
                  ·
                    refine ⟨716270082856916903947331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30560856868561787901752789 716270082856916903947331)
                    ·
                      rfl

theorem cell23_4184793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 7].length) (baseStart_4184793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184793 prefixEnd_4184793 := by exact prefixLift 4184793
  have htrace : WordTrace (prefixWord ++ tailWord_4184793) baseStart_4184793 baseEnd_4184793 := by
    simpa [prefixWord, tailWord_4184793, baseEnd_4184793] using wordTrace_append hprefix tailTrace_4184793
  have hstable : (prefixWord ++ tailWord_4184793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184793).length < 2 ^ (prefixWord ++ tailWord_4184793).sum := by decide
  have hdescent : baseEnd_4184793 < baseStart_4184793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184800 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 4, 5, 2]
def baseStart_4184800 : Nat := 118140960795 + 4184800 * 2 ^ 59
def prefixEnd_4184800 : Nat := 4983230072969 + 3 ^ 40 * 4184800 * 2
def baseEnd_4184800 : Nat := 2148813842935332184454461

theorem tailTrace_4184800 : CollatzResearch.WordTrace tailWord_4184800 prefixEnd_4184800 2148813842935332184454461 := by
  unfold tailWord_4184800
  simp only [CollatzResearch.WordTrace]
  refine ⟨76316097619595890892191927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101754796826127854522922569 76316097619595890892191927)
  ·
    refine ⟨114474146429393836338287891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76316097619595890892191927 114474146429393836338287891)
    ·
      refine ⟨171711219644090754507431837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114474146429393836338287891 171711219644090754507431837)
      ·
        refine ⟨64391707366534032940286939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171711219644090754507431837 64391707366534032940286939)
        ·
          refine ⟨96587561049801049410430409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64391707366534032940286939 96587561049801049410430409)
          ·
            refine ⟨72440670787350787057822807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96587561049801049410430409 72440670787350787057822807)
            ·
              refine ⟨108661006181026180586734211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72440670787350787057822807 108661006181026180586734211)
              ·
                refine ⟨162991509271539270880101317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108661006181026180586734211 162991509271539270880101317)
                ·
                  refine ⟨30560907988413613290018997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162991509271539270880101317 30560907988413613290018997)
                  ·
                    refine ⟨2865085123913776245939281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30560907988413613290018997 2865085123913776245939281)
                    ·
                      refine ⟨2148813842935332184454461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2865085123913776245939281 2148813842935332184454461)
                      ·
                        rfl

theorem cell23_4184800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 4, 5, 2].length) (baseStart_4184800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184800 prefixEnd_4184800 := by exact prefixLift 4184800
  have htrace : WordTrace (prefixWord ++ tailWord_4184800) baseStart_4184800 baseEnd_4184800 := by
    simpa [prefixWord, tailWord_4184800, baseEnd_4184800] using wordTrace_append hprefix tailTrace_4184800
  have hstable : (prefixWord ++ tailWord_4184800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184800).length < 2 ^ (prefixWord ++ tailWord_4184800).sum := by decide
  have hdescent : baseEnd_4184800 < baseStart_4184800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184843 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 6]
def baseStart_4184843 : Nat := 118140960795 + 4184843 * 2 ^ 59
def prefixEnd_4184843 : Nat := 4983230072969 + 3 ^ 40 * 4184843 * 2
def baseEnd_4184843 : Nat := 2148835922603475516216763

theorem tailTrace_4184843 : CollatzResearch.WordTrace tailWord_4184843 prefixEnd_4184843 2148835922603475516216763 := by
  unfold tailWord_4184843
  simp only [CollatzResearch.WordTrace]
  refine ⟨152633763578036000128199183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101755842385357333418799455 152633763578036000128199183)
  ·
    refine ⟨228950645367054000192298775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152633763578036000128199183 228950645367054000192298775)
    ·
      refine ⟨343425968050581000288448163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228950645367054000192298775 343425968050581000288448163)
      ·
        refine ⟨515138952075871500432672245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343425968050581000288448163 515138952075871500432672245)
        ·
          refine ⟨48294276757112953165563023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 515138952075871500432672245 48294276757112953165563023)
          ·
            refine ⟨72441415135669429748344535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48294276757112953165563023 72441415135669429748344535)
            ·
              refine ⟨108662122703504144622516803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72441415135669429748344535 108662122703504144622516803)
              ·
                refine ⟨162993184055256216933775205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108662122703504144622516803 162993184055256216933775205)
                ·
                  refine ⟨30561222010360540675082851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162993184055256216933775205 30561222010360540675082851)
                  ·
                    refine ⟨45841833015540811012624277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30561222010360540675082851 45841833015540811012624277)
                    ·
                      refine ⟨2148835922603475516216763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45841833015540811012624277 2148835922603475516216763)
                      ·
                        rfl

theorem cell23_4184843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 6].length) (baseStart_4184843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184843 prefixEnd_4184843 := by exact prefixLift 4184843
  have htrace : WordTrace (prefixWord ++ tailWord_4184843) baseStart_4184843 baseEnd_4184843 := by
    simpa [prefixWord, tailWord_4184843, baseEnd_4184843] using wordTrace_append hprefix tailTrace_4184843
  have hstable : (prefixWord ++ tailWord_4184843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184843).length < 2 ^ (prefixWord ++ tailWord_4184843).sum := by decide
  have hdescent : baseEnd_4184843 < baseStart_4184843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184873 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 3, 2, 6]
def baseStart_4184873 : Nat := 118140960795 + 4184873 * 2 ^ 59
def prefixEnd_4184873 : Nat := 4983230072969 + 3 ^ 40 * 4184873 * 2
def baseEnd_4184873 : Nat := 2148851327023110398841625

theorem tailTrace_4184873 : CollatzResearch.WordTrace tailWord_4184873 prefixEnd_4184873 2148851327023110398841625 := by
  unfold tailWord_4184873
  simp only [CollatzResearch.WordTrace]
  refine ⟨152634857767927315251791273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101756571845284876834527515 152634857767927315251791273)
  ·
    refine ⟨114476143325945486438843455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152634857767927315251791273 114476143325945486438843455)
    ·
      refine ⟨171714214988918229658265183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114476143325945486438843455 171714214988918229658265183)
      ·
        refine ⟨257571322483377344487397775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171714214988918229658265183 257571322483377344487397775)
        ·
          refine ⟨386356983725066016731096663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257571322483377344487397775 386356983725066016731096663)
          ·
            refine ⟨579535475587599025096644995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386356983725066016731096663 579535475587599025096644995)
            ·
              refine ⟨869303213381398537644967493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579535475587599025096644995 869303213381398537644967493)
              ·
                refine ⟨162994352509012225808431405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 869303213381398537644967493 162994352509012225808431405)
                ·
                  refine ⟨61122882190879584678161777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162994352509012225808431405 61122882190879584678161777)
                  ·
                    refine ⟨45842161643159688508621333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61122882190879584678161777 45842161643159688508621333)
                    ·
                      refine ⟨2148851327023110398841625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45842161643159688508621333 2148851327023110398841625)
                      ·
                        rfl

theorem cell23_4184873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_4184873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184873 prefixEnd_4184873 := by exact prefixLift 4184873
  have htrace : WordTrace (prefixWord ++ tailWord_4184873) baseStart_4184873 baseEnd_4184873 := by
    simpa [prefixWord, tailWord_4184873, baseEnd_4184873] using wordTrace_append hprefix tailTrace_4184873
  have hstable : (prefixWord ++ tailWord_4184873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184873).length < 2 ^ (prefixWord ++ tailWord_4184873).sum := by decide
  have hdescent : baseEnd_4184873 < baseStart_4184873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184947 : List Nat := [1, 1, 1, 2, 2, 1, 5, 4, 2, 4]
def baseStart_4184947 : Nat := 118140960795 + 4184947 * 2 ^ 59
def prefixEnd_4184947 : Nat := 4983230072969 + 3 ^ 40 * 4184947 * 2
def baseEnd_4184947 : Nat := 716296441530514369772095

theorem tailTrace_4184947 : CollatzResearch.WordTrace tailWord_4184947 prefixEnd_4184947 716296441530514369772095 := by
  unfold tailWord_4184947
  simp only [CollatzResearch.WordTrace]
  refine ⟨152637556769659225889985095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101758371179772817259990063 152637556769659225889985095)
  ·
    refine ⟨228956335154488838834977643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152637556769659225889985095 228956335154488838834977643)
    ·
      refine ⟨343434502731733258252466465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228956335154488838834977643 343434502731733258252466465)
      ·
        refine ⟨257575877048799943689349849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343434502731733258252466465 257575877048799943689349849)
        ·
          refine ⟨193181907786599957767012387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257575877048799943689349849 193181907786599957767012387)
          ·
            refine ⟨289772861679899936650518581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193181907786599957767012387 289772861679899936650518581)
            ·
              refine ⟨27166205782490619060986117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 289772861679899936650518581 27166205782490619060986117)
              ·
                refine ⟨5093663584216991073934897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27166205782490619060986117 5093663584216991073934897)
                ·
                  refine ⟨3820247688162743305451173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5093663584216991073934897 3820247688162743305451173)
                  ·
                    refine ⟨716296441530514369772095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3820247688162743305451173 716296441530514369772095)
                    ·
                      rfl

theorem cell23_4184947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 4].length) (baseStart_4184947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184947 prefixEnd_4184947 := by exact prefixLift 4184947
  have htrace : WordTrace (prefixWord ++ tailWord_4184947) baseStart_4184947 baseEnd_4184947 := by
    simpa [prefixWord, tailWord_4184947, baseEnd_4184947] using wordTrace_append hprefix tailTrace_4184947
  have hstable : (prefixWord ++ tailWord_4184947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184947).length < 2 ^ (prefixWord ++ tailWord_4184947).sum := by decide
  have hdescent : baseEnd_4184947 < baseStart_4184947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184954 : List Nat := [3, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2]
def baseStart_4184954 : Nat := 118140960795 + 4184954 * 2 ^ 59
def prefixEnd_4184954 : Nat := 4983230072969 + 3 ^ 40 * 4184954 * 2
def baseEnd_4184954 : Nat := 2148892918956124581928753

theorem tailTrace_4184954 : CollatzResearch.WordTrace tailWord_4184954 prefixEnd_4184954 2148892918956124581928753 := by
  unfold tailWord_4184954
  simp only [CollatzResearch.WordTrace]
  refine ⟨38159453020158466521372479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101758541387089244056993277 38159453020158466521372479)
  ·
    refine ⟨57239179530237699782058719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38159453020158466521372479 57239179530237699782058719)
    ·
      refine ⟨85858769295356549673088079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57239179530237699782058719 85858769295356549673088079)
      ·
        refine ⟨128788153943034824509632119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85858769295356549673088079 128788153943034824509632119)
        ·
          refine ⟨193182230914552236764448179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128788153943034824509632119 193182230914552236764448179)
          ·
            refine ⟨289773346371828355146672269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193182230914552236764448179 289773346371828355146672269)
            ·
              refine ⟨108665004889435633180002101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289773346371828355146672269 108665004889435633180002101)
              ·
                refine ⟨10187344208384590610625197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108665004889435633180002101 10187344208384590610625197)
                ·
                  refine ⟨3820254078144221478984449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10187344208384590610625197 3820254078144221478984449)
                  ·
                    refine ⟨2865190558608166109238337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3820254078144221478984449 2865190558608166109238337)
                    ·
                      refine ⟨2148892918956124581928753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2865190558608166109238337 2148892918956124581928753)
                      ·
                        rfl

theorem cell23_4184954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2].length) (baseStart_4184954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184954 prefixEnd_4184954 := by exact prefixLift 4184954
  have htrace : WordTrace (prefixWord ++ tailWord_4184954) baseStart_4184954 baseEnd_4184954 := by
    simpa [prefixWord, tailWord_4184954, baseEnd_4184954] using wordTrace_append hprefix tailTrace_4184954
  have hstable : (prefixWord ++ tailWord_4184954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184954).length < 2 ^ (prefixWord ++ tailWord_4184954).sum := by decide
  have hdescent : baseEnd_4184954 < baseStart_4184954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184957 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 3, 2, 3]
def baseStart_4184957 : Nat := 118140960795 + 4184957 * 2 ^ 59
def prefixEnd_4184957 : Nat := 4983230072969 + 3 ^ 40 * 4184957 * 2
def baseEnd_4184957 : Nat := 2148894459398088070191239

theorem tailTrace_4184957 : CollatzResearch.WordTrace tailWord_4184957 prefixEnd_4184957 2148894459398088070191239 := by
  unfold tailWord_4184957
  simp only [CollatzResearch.WordTrace]
  refine ⟨152637921499622997597849125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101758614333081998398566083 152637921499622997597849125)
  ·
    refine ⟨28619610281179312049596711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152637921499622997597849125 28619610281179312049596711)
    ·
      refine ⟨42929415421768968074395067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28619610281179312049596711 42929415421768968074395067)
      ·
        refine ⟨64394123132653452111592601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42929415421768968074395067 64394123132653452111592601)
        ·
          refine ⟨48295592349490089083694451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64394123132653452111592601 48295592349490089083694451)
          ·
            refine ⟨72443388524235133625541677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48295592349490089083694451 72443388524235133625541677)
            ·
              refine ⟨27166270696588175109578129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72443388524235133625541677 27166270696588175109578129)
              ·
                refine ⟨20374703022441131332183597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27166270696588175109578129 20374703022441131332183597)
                ·
                  refine ⟨7640513633415424249568849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20374703022441131332183597 7640513633415424249568849)
                  ·
                    refine ⟨5730385225061568187176637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7640513633415424249568849 5730385225061568187176637)
                    ·
                      refine ⟨2148894459398088070191239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5730385225061568187176637 2148894459398088070191239)
                      ·
                        rfl

theorem cell23_4184957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_4184957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184957 prefixEnd_4184957 := by exact prefixLift 4184957
  have htrace : WordTrace (prefixWord ++ tailWord_4184957) baseStart_4184957 baseEnd_4184957 := by
    simpa [prefixWord, tailWord_4184957, baseEnd_4184957] using wordTrace_append hprefix tailTrace_4184957
  have hstable : (prefixWord ++ tailWord_4184957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184957).length < 2 ^ (prefixWord ++ tailWord_4184957).sum := by decide
  have hdescent : baseEnd_4184957 < baseStart_4184957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184967 : List Nat := [1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 4]
def baseStart_4184967 : Nat := 118140960795 + 4184967 * 2 ^ 59
def prefixEnd_4184967 : Nat := 4983230072969 + 3 ^ 40 * 4184967 * 2
def baseEnd_4184967 : Nat := 2148899594204633031066193

theorem tailTrace_4184967 : CollatzResearch.WordTrace tailWord_4184967 prefixEnd_4184967 2148899594204633031066193 := by
  unfold tailWord_4184967
  simp only [CollatzResearch.WordTrace]
  refine ⟨152638286229586769305713155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101758857486391179537142103 152638286229586769305713155)
  ·
    refine ⟨228957429344380153958569733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152638286229586769305713155 228957429344380153958569733)
    ·
      refine ⟨42929518002071278867231825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228957429344380153958569733 42929518002071278867231825)
      ·
        refine ⟨32197138501553459150423869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42929518002071278867231825 32197138501553459150423869)
        ·
          refine ⟨12073926938082547181408951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32197138501553459150423869 12073926938082547181408951)
          ·
            refine ⟨18110890407123820772113427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12073926938082547181408951 18110890407123820772113427)
            ·
              refine ⟨27166335610685731158170141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18110890407123820772113427 27166335610685731158170141)
              ·
                refine ⟨10187375854007149184313803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27166335610685731158170141 10187375854007149184313803)
                ·
                  refine ⟨15281063781010723776470705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10187375854007149184313803 15281063781010723776470705)
                  ·
                    refine ⟨11460797835758042832353029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15281063781010723776470705 11460797835758042832353029)
                    ·
                      refine ⟨2148899594204633031066193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11460797835758042832353029 2148899594204633031066193)
                      ·
                        rfl

theorem cell23_4184967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_4184967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184967 prefixEnd_4184967 := by exact prefixLift 4184967
  have htrace : WordTrace (prefixWord ++ tailWord_4184967) baseStart_4184967 baseEnd_4184967 := by
    simpa [prefixWord, tailWord_4184967, baseEnd_4184967] using wordTrace_append hprefix tailTrace_4184967
  have hstable : (prefixWord ++ tailWord_4184967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184967).length < 2 ^ (prefixWord ++ tailWord_4184967).sum := by decide
  have hdescent : baseEnd_4184967 < baseStart_4184967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184982 : List Nat := [5, 3, 1, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_4184982 : Nat := 118140960795 + 4184982 * 2 ^ 59
def prefixEnd_4184982 : Nat := 4983230072969 + 3 ^ 40 * 4184982 * 2
def baseEnd_4184982 : Nat := 2148907296414450472378625

theorem tailTrace_4184982 : CollatzResearch.WordTrace tailWord_4184982 prefixEnd_4184982 2148907296414450472378625 := by
  unfold tailWord_4184982
  simp only [CollatzResearch.WordTrace]
  refine ⟨9539927082783276679219325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101759222216354951245006133 9539927082783276679219325)
  ·
    refine ⟨3577472656043728754707247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9539927082783276679219325 3577472656043728754707247)
    ·
      refine ⟨5366208984065593132060871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3577472656043728754707247 5366208984065593132060871)
      ·
        refine ⟨8049313476098389698091307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5366208984065593132060871 8049313476098389698091307)
        ·
          refine ⟨12073970214147584547136961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8049313476098389698091307 12073970214147584547136961)
          ·
            refine ⟨9055477660610688410352721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12073970214147584547136961 9055477660610688410352721)
            ·
              refine ⟨6791608245458016307764541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9055477660610688410352721 6791608245458016307764541)
              ·
                refine ⟨2546853092046756115411703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6791608245458016307764541 2546853092046756115411703)
                ·
                  refine ⟨3820279638070134173117555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2546853092046756115411703 3820279638070134173117555)
                  ·
                    refine ⟨5730419457105201259676333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3820279638070134173117555 5730419457105201259676333)
                    ·
                      refine ⟨2148907296414450472378625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5730419457105201259676333 2148907296414450472378625)
                      ·
                        rfl

theorem cell23_4184982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_4184982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184982 prefixEnd_4184982 := by exact prefixLift 4184982
  have htrace : WordTrace (prefixWord ++ tailWord_4184982) baseStart_4184982 baseEnd_4184982 := by
    simpa [prefixWord, tailWord_4184982, baseEnd_4184982] using wordTrace_append hprefix tailTrace_4184982
  have hstable : (prefixWord ++ tailWord_4184982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184982).length < 2 ^ (prefixWord ++ tailWord_4184982).sum := by decide
  have hdescent : baseEnd_4184982 < baseStart_4184982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184988 : List Nat := [2, 2, 3, 3, 2, 2, 2, 1, 1, 1, 4]
def baseStart_4184988 : Nat := 118140960795 + 4184988 * 2 ^ 59
def prefixEnd_4184988 : Nat := 4983230072969 + 3 ^ 40 * 4184988 * 2
def baseEnd_4184988 : Nat := 2148910377298377448903597

theorem tailTrace_4184988 : CollatzResearch.WordTrace tailWord_4184988 prefixEnd_4184988 2148910377298377448903597 := by
  unfold tailWord_4184988
  simp only [CollatzResearch.WordTrace]
  refine ⟨76319526081255344946113809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101759368108340459928151745 76319526081255344946113809)
  ·
    refine ⟨57239644560941508709585357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76319526081255344946113809 57239644560941508709585357)
    ·
      refine ⟨21464866710353065766094509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57239644560941508709585357 21464866710353065766094509)
      ·
        refine ⟨8049325016382399662285441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21464866710353065766094509 8049325016382399662285441)
        ·
          refine ⟨6036993762286799746714081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8049325016382399662285441 6036993762286799746714081)
          ·
            refine ⟨4527745321715099810035561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6036993762286799746714081 4527745321715099810035561)
            ·
              refine ⟨3395808991286324857526671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4527745321715099810035561 3395808991286324857526671)
              ·
                refine ⟨5093713486929487286290007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3395808991286324857526671 5093713486929487286290007)
                ·
                  refine ⟨7640570230394230929435011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5093713486929487286290007 7640570230394230929435011)
                  ·
                    refine ⟨11460855345591346394152517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7640570230394230929435011 11460855345591346394152517)
                    ·
                      refine ⟨2148910377298377448903597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11460855345591346394152517 2148910377298377448903597)
                      ·
                        rfl

theorem cell23_4184988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_4184988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184988 prefixEnd_4184988 := by exact prefixLift 4184988
  have htrace : WordTrace (prefixWord ++ tailWord_4184988) baseStart_4184988 baseEnd_4184988 := by
    simpa [prefixWord, tailWord_4184988, baseEnd_4184988] using wordTrace_append hprefix tailTrace_4184988
  have hstable : (prefixWord ++ tailWord_4184988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184988).length < 2 ^ (prefixWord ++ tailWord_4184988).sum := by decide
  have hdescent : baseEnd_4184988 < baseStart_4184988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184991 : List Nat := [1, 1, 2, 5, 2, 1, 4, 1, 1, 2, 3]
def baseStart_4184991 : Nat := 118140960795 + 4184991 * 2 ^ 59
def prefixEnd_4184991 : Nat := 4983230072969 + 3 ^ 40 * 4184991 * 2
def baseEnd_4184991 : Nat := 2148911917740340937166083

theorem tailTrace_4184991 : CollatzResearch.WordTrace tailWord_4184991 prefixEnd_4184991 2148911917740340937166083 := by
  unfold tailWord_4184991
  simp only [CollatzResearch.WordTrace]
  refine ⟨152639161581499821404586827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101759441054333214269724551 152639161581499821404586827)
  ·
    refine ⟨228958742372249732106880241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152639161581499821404586827 228958742372249732106880241)
    ·
      refine ⟨171719056779187299080160181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228958742372249732106880241 171719056779187299080160181)
      ·
        refine ⟨16098661573048809288765017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171719056779187299080160181 16098661573048809288765017)
        ·
          refine ⟨12073996179786606966573763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16098661573048809288765017 12073996179786606966573763)
          ·
            refine ⟨18110994269679910449860645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12073996179786606966573763 18110994269679910449860645)
            ·
              refine ⟨3395811425564983209348871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18110994269679910449860645 3395811425564983209348871)
              ·
                refine ⟨5093717138347474814023307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3395811425564983209348871 5093717138347474814023307)
                ·
                  refine ⟨7640575707521212221034961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5093717138347474814023307 7640575707521212221034961)
                  ·
                    refine ⟨5730431780640909165776221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7640575707521212221034961 5730431780640909165776221)
                    ·
                      refine ⟨2148911917740340937166083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5730431780640909165776221 2148911917740340937166083)
                      ·
                        rfl

theorem cell23_4184991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_4184991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4184991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4184991 prefixEnd_4184991 := by exact prefixLift 4184991
  have htrace : WordTrace (prefixWord ++ tailWord_4184991) baseStart_4184991 baseEnd_4184991 := by
    simpa [prefixWord, tailWord_4184991, baseEnd_4184991] using wordTrace_append hprefix tailTrace_4184991
  have hstable : (prefixWord ++ tailWord_4184991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184991).length < 2 ^ (prefixWord ++ tailWord_4184991).sum := by decide
  have hdescent : baseEnd_4184991 < baseStart_4184991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185005 : List Nat := [1, 5, 2, 3, 1, 1, 2, 1, 3, 2, 2]
def baseStart_4185005 : Nat := 118140960795 + 4185005 * 2 ^ 59
def prefixEnd_4185005 : Nat := 4983230072969 + 3 ^ 40 * 4185005 * 2
def baseEnd_4185005 : Nat := 2148919106469503882391019

theorem tailTrace_4185005 : CollatzResearch.WordTrace tailWord_4185005 prefixEnd_4185005 2148919106469503882391019 := by
  unfold tailWord_4185005
  simp only [CollatzResearch.WordTrace]
  refine ⟨152639672203449101795596469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101759781468966067863730979 152639672203449101795596469)
  ·
    refine ⟨14309969269073353293337169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152639672203449101795596469 14309969269073353293337169)
    ·
      refine ⟨10732476951805014970002877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14309969269073353293337169 10732476951805014970002877)
      ·
        refine ⟨4024678856926880613751079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10732476951805014970002877 4024678856926880613751079)
        ·
          refine ⟨6037018285390320920626619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4024678856926880613751079 6037018285390320920626619)
          ·
            refine ⟨9055527428085481380939929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6037018285390320920626619 9055527428085481380939929)
            ·
              refine ⟨6791645571064111035704947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9055527428085481380939929 6791645571064111035704947)
              ·
                refine ⟨10187468356596166553557421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6791645571064111035704947 10187468356596166553557421)
                ·
                  refine ⟨3820300633723562457584033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10187468356596166553557421 3820300633723562457584033)
                  ·
                    refine ⟨2865225475292671843188025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3820300633723562457584033 2865225475292671843188025)
                    ·
                      refine ⟨2148919106469503882391019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2865225475292671843188025 2148919106469503882391019)
                      ·
                        rfl

theorem cell23_4185005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_4185005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185005 prefixEnd_4185005 := by exact prefixLift 4185005
  have htrace : WordTrace (prefixWord ++ tailWord_4185005) baseStart_4185005 baseEnd_4185005 := by
    simpa [prefixWord, tailWord_4185005, baseEnd_4185005] using wordTrace_append hprefix tailTrace_4185005
  have hstable : (prefixWord ++ tailWord_4185005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185005).length < 2 ^ (prefixWord ++ tailWord_4185005).sum := by decide
  have hdescent : baseEnd_4185005 < baseStart_4185005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185021 : List Nat := [1, 4, 1, 2, 4, 2, 1, 1, 1, 3, 3]
def baseStart_4185021 : Nat := 118140960795 + 4185021 * 2 ^ 59
def prefixEnd_4185021 : Nat := 4983230072969 + 3 ^ 40 * 4185021 * 2
def baseEnd_4185021 : Nat := 2148927322159975819790945

theorem tailTrace_4185021 : CollatzResearch.WordTrace tailWord_4185021 prefixEnd_4185021 2148927322159975819790945 := by
  unfold tailWord_4185021
  simp only [CollatzResearch.WordTrace]
  refine ⟨152640255771391136528178917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101760170514260757685452611 152640255771391136528178917)
  ·
    refine ⟨28620047957135838099033547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152640255771391136528178917 28620047957135838099033547)
    ·
      refine ⟨42930071935703757148550321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28620047957135838099033547 42930071935703757148550321)
      ·
        refine ⟨32197553951777817861412741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42930071935703757148550321 32197553951777817861412741)
        ·
          refine ⟨6037041365958340849014889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32197553951777817861412741 6037041365958340849014889)
          ·
            refine ⟨4527781024468755636761167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6037041365958340849014889 4527781024468755636761167)
            ·
              refine ⟨6791671536703133455141751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4527781024468755636761167 6791671536703133455141751)
              ·
                refine ⟨10187507305054700182712627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6791671536703133455141751 10187507305054700182712627)
                ·
                  refine ⟨15281260957582050274068941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10187507305054700182712627 15281260957582050274068941)
                  ·
                    refine ⟨5730472859093268852775853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15281260957582050274068941 5730472859093268852775853)
                    ·
                      refine ⟨2148927322159975819790945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5730472859093268852775853 2148927322159975819790945)
                      ·
                        rfl

theorem cell23_4185021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_4185021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185021 prefixEnd_4185021 := by exact prefixLift 4185021
  have htrace : WordTrace (prefixWord ++ tailWord_4185021) baseStart_4185021 baseEnd_4185021 := by
    simpa [prefixWord, tailWord_4185021, baseEnd_4185021] using wordTrace_append hprefix tailTrace_4185021
  have hstable : (prefixWord ++ tailWord_4185021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185021).length < 2 ^ (prefixWord ++ tailWord_4185021).sum := by decide
  have hdescent : baseEnd_4185021 < baseStart_4185021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185028 : List Nat := [2, 3, 3, 3, 2, 1, 2, 7]
def baseStart_4185028 : Nat := 118140960795 + 4185028 * 2 ^ 59
def prefixEnd_4185028 : Nat := 4983230072969 + 3 ^ 40 * 4185028 * 2
def baseEnd_4185028 : Nat := 79590033945353973792719

theorem tailTrace_4185028 : CollatzResearch.WordTrace tailWord_4185028 prefixEnd_4185028 79590033945353973792719 := by
  unfold tailWord_4185028
  simp only [CollatzResearch.WordTrace]
  refine ⟨76320255541182888361841869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101760340721577184482455825 76320255541182888361841869)
  ·
    refine ⟨28620095827943583135690701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76320255541182888361841869 28620095827943583135690701)
    ·
      refine ⟨10732535935478843675884013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28620095827943583135690701 10732535935478843675884013)
      ·
        refine ⟨4024700975804566378456505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10732535935478843675884013 4024700975804566378456505)
        ·
          refine ⟨3018525731853424783842379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4024700975804566378456505 3018525731853424783842379)
          ·
            refine ⟨4527788597780137175763569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3018525731853424783842379 4527788597780137175763569)
            ·
              refine ⟨3395841448335102881822677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4527788597780137175763569 3395841448335102881822677)
              ·
                refine ⟨79590033945353973792719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3395841448335102881822677 79590033945353973792719)
                ·
                  rfl

theorem cell23_4185028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 7].length) (baseStart_4185028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185028 prefixEnd_4185028 := by exact prefixLift 4185028
  have htrace : WordTrace (prefixWord ++ tailWord_4185028) baseStart_4185028 baseEnd_4185028 := by
    simpa [prefixWord, tailWord_4185028, baseEnd_4185028] using wordTrace_append hprefix tailTrace_4185028
  have hstable : (prefixWord ++ tailWord_4185028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185028).length < 2 ^ (prefixWord ++ tailWord_4185028).sum := by decide
  have hdescent : baseEnd_4185028 < baseStart_4185028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185124 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 1, 2, 5]
def baseStart_4185124 : Nat := 118140960795 + 4185124 * 2 ^ 59
def prefixEnd_4185124 : Nat := 4983230072969 + 3 ^ 40 * 4185124 * 2
def baseEnd_4185124 : Nat := 2148980210667388916802971

theorem tailTrace_4185124 : CollatzResearch.WordTrace tailWord_4185124 prefixEnd_4185124 2148980210667388916802971 := by
  unfold tailWord_4185124
  simp only [CollatzResearch.WordTrace]
  refine ⟨76322006245008992559589213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101762674993345323412785617 76322006245008992559589213)
  ·
    refine ⟨28620752341878372209845955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76322006245008992559589213 28620752341878372209845955)
    ·
      refine ⟨42931128512817558314768933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28620752341878372209845955 42931128512817558314768933)
      ·
        refine ⟨8049586596153292184019175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42931128512817558314768933 8049586596153292184019175)
        ·
          refine ⟨12074379894229938276028763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8049586596153292184019175 12074379894229938276028763)
          ·
            refine ⟨18111569841344907414043145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12074379894229938276028763 18111569841344907414043145)
            ·
              refine ⟨13583677381008680560532359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18111569841344907414043145 13583677381008680560532359)
              ·
                refine ⟨20375516071513020840798539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13583677381008680560532359 20375516071513020840798539)
                ·
                  refine ⟨30563274107269531261197809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20375516071513020840798539 30563274107269531261197809)
                  ·
                    refine ⟨22922455580452148445898357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30563274107269531261197809 22922455580452148445898357)
                    ·
                      refine ⟨2148980210667388916802971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22922455580452148445898357 2148980210667388916802971)
                      ·
                        rfl

theorem cell23_4185124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_4185124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185124 prefixEnd_4185124 := by exact prefixLift 4185124
  have htrace : WordTrace (prefixWord ++ tailWord_4185124) baseStart_4185124 baseEnd_4185124 := by
    simpa [prefixWord, tailWord_4185124, baseEnd_4185124] using wordTrace_append hprefix tailTrace_4185124
  have hstable : (prefixWord ++ tailWord_4185124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185124).length < 2 ^ (prefixWord ++ tailWord_4185124).sum := by decide
  have hdescent : baseEnd_4185124 < baseStart_4185124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185134 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_4185134 : Nat := 118140960795 + 4185134 * 2 ^ 59
def prefixEnd_4185134 : Nat := 4983230072969 + 3 ^ 40 * 4185134 * 2
def baseEnd_4185134 : Nat := 2148985345473933877677925

theorem tailTrace_4185134 : CollatzResearch.WordTrace tailWord_4185134 prefixEnd_4185134 2148985345473933877677925 := by
  unfold tailWord_4185134
  simp only [CollatzResearch.WordTrace]
  refine ⟨19080547152497719603380307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101762918146654504551361637 19080547152497719603380307)
  ·
    refine ⟨28620820728746579405070461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19080547152497719603380307 28620820728746579405070461)
    ·
      refine ⟨10732807773279967276901423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28620820728746579405070461 10732807773279967276901423)
      ·
        refine ⟨16099211659919950915352135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10732807773279967276901423 16099211659919950915352135)
        ·
          refine ⟨24148817489879926373028203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16099211659919950915352135 24148817489879926373028203)
          ·
            refine ⟨36223226234819889559542305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24148817489879926373028203 36223226234819889559542305)
            ·
              refine ⟨27167419676114917169656729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36223226234819889559542305 27167419676114917169656729)
              ·
                refine ⟨20375564757086187877242547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27167419676114917169656729 20375564757086187877242547)
                ·
                  refine ⟨30563347135629281815863821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20375564757086187877242547 30563347135629281815863821)
                  ·
                    refine ⟨11461255175860980680948933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30563347135629281815863821 11461255175860980680948933)
                    ·
                      refine ⟨2148985345473933877677925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11461255175860980680948933 2148985345473933877677925)
                      ·
                        rfl

theorem cell23_4185134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_4185134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185134 prefixEnd_4185134 := by exact prefixLift 4185134
  have htrace : WordTrace (prefixWord ++ tailWord_4185134) baseStart_4185134 baseEnd_4185134 := by
    simpa [prefixWord, tailWord_4185134, baseEnd_4185134] using wordTrace_append hprefix tailTrace_4185134
  have hstable : (prefixWord ++ tailWord_4185134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185134).length < 2 ^ (prefixWord ++ tailWord_4185134).sum := by decide
  have hdescent : baseEnd_4185134 < baseStart_4185134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185144 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 5, 4]
def baseStart_4185144 : Nat := 118140960795 + 4185144 * 2 ^ 59
def prefixEnd_4185144 : Nat := 4983230072969 + 3 ^ 40 * 4185144 * 2
def baseEnd_4185144 : Nat := 716330160093492946184293

theorem tailTrace_4185144 : CollatzResearch.WordTrace tailWord_4185144 prefixEnd_4185144 716330160093492946184293 := by
  unfold tailWord_4185144
  simp only [CollatzResearch.WordTrace]
  refine ⟨76322370974972764267453243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101763161299963685689937657 76322370974972764267453243)
  ·
    refine ⟨114483556462459146401179865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76322370974972764267453243 114483556462459146401179865)
    ·
      refine ⟨85862667346844359800884899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114483556462459146401179865 85862667346844359800884899)
      ·
        refine ⟨128794001020266539701327349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85862667346844359800884899 128794001020266539701327349)
        ·
          refine ⟨12074437595649988096999439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128794001020266539701327349 12074437595649988096999439)
          ·
            refine ⟨18111656393474982145499159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12074437595649988096999439 18111656393474982145499159)
            ·
              refine ⟨27167484590212473218248739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18111656393474982145499159 27167484590212473218248739)
              ·
                refine ⟨40751226885318709827373109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27167484590212473218248739 40751226885318709827373109)
                ·
                  refine ⟨3820427520498629046316229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40751226885318709827373109 3820427520498629046316229)
                  ·
                    refine ⟨716330160093492946184293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3820427520498629046316229 716330160093492946184293)
                    ·
                      rfl

theorem cell23_4185144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 5, 4].length) (baseStart_4185144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185144 prefixEnd_4185144 := by exact prefixLift 4185144
  have htrace : WordTrace (prefixWord ++ tailWord_4185144) baseStart_4185144 baseEnd_4185144 := by
    simpa [prefixWord, tailWord_4185144, baseEnd_4185144] using wordTrace_append hprefix tailTrace_4185144
  have hstable : (prefixWord ++ tailWord_4185144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185144).length < 2 ^ (prefixWord ++ tailWord_4185144).sum := by decide
  have hdescent : baseEnd_4185144 < baseStart_4185144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185191 : List Nat := [1, 1, 5, 1, 1, 4, 3, 1, 6]
def baseStart_4185191 : Nat := 118140960795 + 4185191 * 2 ^ 59
def prefixEnd_4185191 : Nat := 4983230072969 + 3 ^ 40 * 4185191 * 2
def baseEnd_4185191 : Nat := 238779401541248906073907

theorem tailTrace_4185191 : CollatzResearch.WordTrace tailWord_4185191 prefixEnd_4185191 238779401541248906073907 := by
  unfold tailWord_4185191
  simp only [CollatzResearch.WordTrace]
  refine ⟨152646456180775255561867427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101764304120516837041244951 152646456180775255561867427)
  ·
    refine ⟨228969684271162883342801141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152646456180775255561867427 228969684271162883342801141)
    ·
      refine ⟨21465907900421520313387607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228969684271162883342801141 21465907900421520313387607)
      ·
        refine ⟨32198861850632280470081411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21465907900421520313387607 32198861850632280470081411)
        ·
          refine ⟨48298292775948420705122117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32198861850632280470081411 48298292775948420705122117)
          ·
            refine ⟨9055929895490328882210397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48298292775948420705122117 9055929895490328882210397)
            ·
              refine ⟨3395973710808873330828899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9055929895490328882210397 3395973710808873330828899)
              ·
                refine ⟨5093960566213309996243349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3395973710808873330828899 5093960566213309996243349)
                ·
                  refine ⟨238779401541248906073907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5093960566213309996243349 238779401541248906073907)
                  ·
                    rfl

theorem cell23_4185191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 6].length) (baseStart_4185191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185191 prefixEnd_4185191 := by exact prefixLift 4185191
  have htrace : WordTrace (prefixWord ++ tailWord_4185191) baseStart_4185191 baseEnd_4185191 := by
    simpa [prefixWord, tailWord_4185191, baseEnd_4185191] using wordTrace_append hprefix tailTrace_4185191
  have hstable : (prefixWord ++ tailWord_4185191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185191).length < 2 ^ (prefixWord ++ tailWord_4185191).sum := by decide
  have hdescent : baseEnd_4185191 < baseStart_4185191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185257 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 7]
def baseStart_4185257 : Nat := 118140960795 + 4185257 * 2 ^ 59
def prefixEnd_4185257 : Nat := 4983230072969 + 3 ^ 40 * 4185257 * 2
def baseEnd_4185257 : Nat := 2149048503594436896439859

theorem tailTrace_4185257 : CollatzResearch.WordTrace tailWord_4185257 prefixEnd_4185257 2149048503594436896439859 := by
  unfold tailWord_4185257
  simp only [CollatzResearch.WordTrace]
  refine ⟨152648863398536148833770025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101765908932357432555846683 152648863398536148833770025)
  ·
    refine ⟨114486647548902111625327519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152648863398536148833770025 114486647548902111625327519)
    ·
      refine ⟨171729971323353167437991279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114486647548902111625327519 171729971323353167437991279)
      ·
        refine ⟨257594956985029751156986919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171729971323353167437991279 257594956985029751156986919)
        ·
          refine ⟨386392435477544626735480379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257594956985029751156986919 386392435477544626735480379)
          ·
            refine ⟨579588653216316940103220569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386392435477544626735480379 579588653216316940103220569)
            ·
              refine ⟨434691489912237705077415427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579588653216316940103220569 434691489912237705077415427)
              ·
                refine ⟨652037234868356557616123141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434691489912237705077415427 652037234868356557616123141)
                ·
                  refine ⟨122256981537816854553023089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 652037234868356557616123141 122256981537816854553023089)
                  ·
                    refine ⟨91692736153362640914767317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122256981537816854553023089 91692736153362640914767317)
                    ·
                      refine ⟨2149048503594436896439859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91692736153362640914767317 2149048503594436896439859)
                      ·
                        rfl

theorem cell23_4185257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_4185257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185257 prefixEnd_4185257 := by exact prefixLift 4185257
  have htrace : WordTrace (prefixWord ++ tailWord_4185257) baseStart_4185257 baseEnd_4185257 := by
    simpa [prefixWord, tailWord_4185257, baseEnd_4185257] using wordTrace_append hprefix tailTrace_4185257
  have hstable : (prefixWord ++ tailWord_4185257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185257).length < 2 ^ (prefixWord ++ tailWord_4185257).sum := by decide
  have hdescent : baseEnd_4185257 < baseStart_4185257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185258 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_4185258 : Nat := 118140960795 + 4185258 * 2 ^ 59
def prefixEnd_4185258 : Nat := 4983230072969 + 3 ^ 40 * 4185258 * 2
def baseEnd_4185258 : Nat := 2149049017075091392527355

theorem tailTrace_4185258 : CollatzResearch.WordTrace tailWord_4185258 prefixEnd_4185258 2149049017075091392527355 := by
  unfold tailWord_4185258
  simp only [CollatzResearch.WordTrace]
  refine ⟨38162224967883131501139107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101765933247688350669704285 38162224967883131501139107)
  ·
    refine ⟨57243337451824697251708661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38162224967883131501139107 57243337451824697251708661)
    ·
      refine ⟨5366562886108565367347687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57243337451824697251708661 5366562886108565367347687)
      ·
        refine ⟨8049844329162848051021531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5366562886108565367347687 8049844329162848051021531)
        ·
          refine ⟨12074766493744272076532297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8049844329162848051021531 12074766493744272076532297)
          ·
            refine ⟨9056074870308204057399223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12074766493744272076532297 9056074870308204057399223)
            ·
              refine ⟨13584112305462306086098835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9056074870308204057399223 13584112305462306086098835)
              ·
                refine ⟨20376168458193459129148253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13584112305462306086098835 20376168458193459129148253)
                ·
                  refine ⟨7641063171822547173430595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20376168458193459129148253 7641063171822547173430595)
                  ·
                    refine ⟨11461594757733820760145893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7641063171822547173430595 11461594757733820760145893)
                    ·
                      refine ⟨2149049017075091392527355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11461594757733820760145893 2149049017075091392527355)
                      ·
                        rfl

theorem cell23_4185258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_4185258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185258 prefixEnd_4185258 := by exact prefixLift 4185258
  have htrace : WordTrace (prefixWord ++ tailWord_4185258) baseStart_4185258 baseEnd_4185258 := by
    simpa [prefixWord, tailWord_4185258, baseEnd_4185258] using wordTrace_append hprefix tailTrace_4185258
  have hstable : (prefixWord ++ tailWord_4185258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185258).length < 2 ^ (prefixWord ++ tailWord_4185258).sum := by decide
  have hdescent : baseEnd_4185258 < baseStart_4185258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185278 : List Nat := [4, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5]
def baseStart_4185278 : Nat := 118140960795 + 4185278 * 2 ^ 59
def prefixEnd_4185278 : Nat := 4983230072969 + 3 ^ 40 * 4185278 * 2
def baseEnd_4185278 : Nat := 2149059286688181314277263

theorem tailTrace_4185278 : CollatzResearch.WordTrace tailWord_4185278 prefixEnd_4185278 2149059286688181314277263 := by
  unfold tailWord_4185278
  simp only [CollatzResearch.WordTrace]
  refine ⟨19081203666432508677535561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101766419554306712946856325 19081203666432508677535561)
  ·
    refine ⟨14310902749824381508151671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19081203666432508677535561 14310902749824381508151671)
    ·
      refine ⟨21466354124736572262227507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14310902749824381508151671 21466354124736572262227507)
      ·
        refine ⟨32199531187104858393341261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21466354124736572262227507 32199531187104858393341261)
        ·
          refine ⟨12074824195164321897502973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32199531187104858393341261 12074824195164321897502973)
          ·
            refine ⟨4528059073186620711563615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12074824195164321897502973 4528059073186620711563615)
            ·
              refine ⟨6792088609779931067345423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4528059073186620711563615 6792088609779931067345423)
              ·
                refine ⟨10188132914669896601018135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6792088609779931067345423 10188132914669896601018135)
                ·
                  refine ⟨15282199372004844901527203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10188132914669896601018135 15282199372004844901527203)
                  ·
                    refine ⟨22923299058007267352290805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15282199372004844901527203 22923299058007267352290805)
                    ·
                      refine ⟨2149059286688181314277263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22923299058007267352290805 2149059286688181314277263)
                      ·
                        rfl

theorem cell23_4185278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_4185278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185278 prefixEnd_4185278 := by exact prefixLift 4185278
  have htrace : WordTrace (prefixWord ++ tailWord_4185278) baseStart_4185278 baseEnd_4185278 := by
    simpa [prefixWord, tailWord_4185278, baseEnd_4185278] using wordTrace_append hprefix tailTrace_4185278
  have hstable : (prefixWord ++ tailWord_4185278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185278).length < 2 ^ (prefixWord ++ tailWord_4185278).sum := by decide
  have hdescent : baseEnd_4185278 < baseStart_4185278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185286 : List Nat := [6, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_4185286 : Nat := 118140960795 + 4185286 * 2 ^ 59
def prefixEnd_4185286 : Nat := 4983230072969 + 3 ^ 40 * 4185286 * 2
def baseEnd_4185286 : Nat := 2149063394533417282977227

theorem tailTrace_4185286 : CollatzResearch.WordTrace tailWord_4185286 prefixEnd_4185286 2149063394533417282977227 := by
  unfold tailWord_4185286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4770310034857221462080491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 101766614076954057857717141 4770310034857221462080491)
  ·
    refine ⟨7155465052285832193120737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4770310034857221462080491 7155465052285832193120737)
    ·
      refine ⟨5366598789214374144840553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7155465052285832193120737 5366598789214374144840553)
      ·
        refine ⟨4024949091910780608630415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5366598789214374144840553 4024949091910780608630415)
        ·
          refine ⟨6037423637866170912945623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4024949091910780608630415 6037423637866170912945623)
          ·
            refine ⟨9056135456799256369418435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6037423637866170912945623 9056135456799256369418435)
            ·
              refine ⟨13584203185198884554127653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9056135456799256369418435 13584203185198884554127653)
              ·
                refine ⟨2547038097224790853898935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13584203185198884554127653 2547038097224790853898935)
                ·
                  refine ⟨3820557145837186280848403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2547038097224790853898935 3820557145837186280848403)
                  ·
                    refine ⟨5730835718755779421272605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3820557145837186280848403 5730835718755779421272605)
                    ·
                      refine ⟨2149063394533417282977227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5730835718755779421272605 2149063394533417282977227)
                      ·
                        rfl

theorem cell23_4185286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_4185286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185286 prefixEnd_4185286 := by exact prefixLift 4185286
  have htrace : WordTrace (prefixWord ++ tailWord_4185286) baseStart_4185286 baseEnd_4185286 := by
    simpa [prefixWord, tailWord_4185286, baseEnd_4185286] using wordTrace_append hprefix tailTrace_4185286
  have hstable : (prefixWord ++ tailWord_4185286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185286).length < 2 ^ (prefixWord ++ tailWord_4185286).sum := by decide
  have hdescent : baseEnd_4185286 < baseStart_4185286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185342 : List Nat := [4, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_4185342 : Nat := 118140960795 + 4185342 * 2 ^ 59
def prefixEnd_4185342 : Nat := 4983230072969 + 3 ^ 40 * 4185342 * 2
def baseEnd_4185342 : Nat := 2149092149450069063876969

theorem tailTrace_4185342 : CollatzResearch.WordTrace tailWord_4185342 prefixEnd_4185342 2149092149450069063876969 := by
  unfold tailWord_4185342
  simp only [CollatzResearch.WordTrace]
  refine ⟨19081495450403526043826785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101767975735485472233742853 19081495450403526043826785)
  ·
    refine ⟨14311121587802644532870089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19081495450403526043826785 14311121587802644532870089)
    ·
      refine ⟨10733341190851983399652567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14311121587802644532870089 10733341190851983399652567)
      ·
        refine ⟨16100011786277975099478851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10733341190851983399652567 16100011786277975099478851)
        ·
          refine ⟨24150017679416962649218277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16100011786277975099478851 24150017679416962649218277)
          ·
            refine ⟨4528128314890680496728427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24150017679416962649218277 4528128314890680496728427)
            ·
              refine ⟨6792192472336020745092641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4528128314890680496728427 6792192472336020745092641)
              ·
                refine ⟨5094144354252015558819481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6792192472336020745092641 5094144354252015558819481)
                ·
                  refine ⟨3820608265689011669114611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5094144354252015558819481 3820608265689011669114611)
                  ·
                    refine ⟨5730912398533517503671917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3820608265689011669114611 5730912398533517503671917)
                    ·
                      refine ⟨2149092149450069063876969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5730912398533517503671917 2149092149450069063876969)
                      ·
                        rfl

theorem cell23_4185342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_4185342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185342 prefixEnd_4185342 := by exact prefixLift 4185342
  have htrace : WordTrace (prefixWord ++ tailWord_4185342) baseStart_4185342 baseEnd_4185342 := by
    simpa [prefixWord, tailWord_4185342, baseEnd_4185342] using wordTrace_append hprefix tailTrace_4185342
  have hstable : (prefixWord ++ tailWord_4185342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185342).length < 2 ^ (prefixWord ++ tailWord_4185342).sum := by decide
  have hdescent : baseEnd_4185342 < baseStart_4185342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185391 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 1, 7, 2]
def baseStart_4185391 : Nat := 118140960795 + 4185391 * 2 ^ 59
def prefixEnd_4185391 : Nat := 4983230072969 + 3 ^ 40 * 4185391 * 2
def baseEnd_4185391 : Nat := 2149117310002139372164243

theorem tailTrace_4185391 : CollatzResearch.WordTrace tailWord_4185391 prefixEnd_4185391 2149117310002139372164243 := by
  unfold tailWord_4185391
  simp only [CollatzResearch.WordTrace]
  refine ⟨152653750780050689719148027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101769167186700459812765351 152653750780050689719148027)
  ·
    refine ⟨228980626170076034578722041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152653750780050689719148027 228980626170076034578722041)
    ·
      refine ⟨171735469627557025934041531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228980626170076034578722041 171735469627557025934041531)
      ·
        refine ⟨257603204441335538901062297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171735469627557025934041531 257603204441335538901062297)
        ·
          refine ⟨193202403331001654175796723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257603204441335538901062297 193202403331001654175796723)
          ·
            refine ⟨289803604996502481263695085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193202403331001654175796723 289803604996502481263695085)
            ·
              refine ⟨108676351873688430473885657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289803604996502481263695085 108676351873688430473885657)
              ·
                refine ⟨81507263905266322855414243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108676351873688430473885657 81507263905266322855414243)
                ·
                  refine ⟨122260895857899484283121365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81507263905266322855414243 122260895857899484283121365)
                  ·
                    refine ⟨2865489746669519162885657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 122260895857899484283121365 2865489746669519162885657)
                    ·
                      refine ⟨2149117310002139372164243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2865489746669519162885657 2149117310002139372164243)
                      ·
                        rfl

theorem cell23_4185391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 7, 2].length) (baseStart_4185391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185391 prefixEnd_4185391 := by exact prefixLift 4185391
  have htrace : WordTrace (prefixWord ++ tailWord_4185391) baseStart_4185391 baseEnd_4185391 := by
    simpa [prefixWord, tailWord_4185391, baseEnd_4185391] using wordTrace_append hprefix tailTrace_4185391
  have hstable : (prefixWord ++ tailWord_4185391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185391).length < 2 ^ (prefixWord ++ tailWord_4185391).sum := by decide
  have hdescent : baseEnd_4185391 < baseStart_4185391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
